theory Tableau_Initialization
  imports Tableau_Simplex_Run
begin

text \<open>
  The starting tableau of Engine::processInputQuery
  (src/engine/Engine.cpp:1414-1598) on the native LP path:
  \<^item> createConstraintMatrix (1061-1089) accepts only equations, and
    invokePreprocessor (980-1012) rejects infinite bounds;
  \<^item> addAuxiliaryVariables (1290-1314) gives equation i the fresh variable
    n + i with coefficient -1, fixes both of its bounds to the equation's
    scalar and sets the scalar to 0;
  \<^item> with the auxiliary variables as the basis, each solved row is
    x(n + i) = the equation's terms. This is the basis used when
    ONLY_AUX_INITIAL_BASIS holds, and for every row that
    selectInitialVariablesForBasis leaves to augmentInitialBasisIfNeeded
    (1316-1328). The default triangular basis is reached from it by checked
    pivots (Tableau_Initial_Basis);
  \<^item> Tableau::initializeTableau (Tableau.cpp:336-374) puts every nonbasic at its
    lower bound, and computeAssignment (376-411) solves for the basics.
  Several bound atoms on one variable are read as their conjunction; the
  native query keeps one lower and one upper bound per variable, as the file
  workflow requires.
\<close>

section \<open>Engine input\<close>

fun bound_variable :: "bound \<Rightarrow> var" where
  "bound_variable (Lower x l) = x"
| "bound_variable (Upper x u) = x"

fun lowers :: "bound list \<Rightarrow> var \<Rightarrow> real list" where
  "lowers [] x = []"
| "lowers (Lower y l # bs) x = (if y = x then l # lowers bs x else lowers bs x)"
| "lowers (Upper y u # bs) x = lowers bs x"

fun uppers :: "bound list \<Rightarrow> var \<Rightarrow> real list" where
  "uppers [] x = []"
| "uppers (Lower y l # bs) x = uppers bs x"
| "uppers (Upper y u # bs) x = (if y = x then u # uppers bs x else uppers bs x)"

definition lower_of :: "query \<Rightarrow> var \<Rightarrow> real" where
  "lower_of Q x = Max (set (lowers (query_bounds Q) x))"

definition upper_of :: "query \<Rightarrow> var \<Rightarrow> real" where
  "upper_of Q x = Min (set (uppers (query_bounds Q) x))"

fun is_equation :: "linear_constraint \<Rightarrow> bool" where
  "is_equation (LinearEq e b) = True"
| "is_equation (LinearLe e b) = False"
| "is_equation (LinearGe e b) = False"

fun constraint_expr :: "linear_constraint \<Rightarrow> linexpr" where
  "constraint_expr (LinearEq e b) = e"
| "constraint_expr (LinearLe e b) = e"
| "constraint_expr (LinearGe e b) = e"

fun constraint_scalar :: "linear_constraint \<Rightarrow> real" where
  "constraint_scalar (LinearEq e b) = b"
| "constraint_scalar (LinearLe e b) = b"
| "constraint_scalar (LinearGe e b) = b"

text \<open>An equation c + terms = b is stored as terms = b - c.\<close>

definition aux_terms :: "linear_constraint \<Rightarrow> (real \<times> var) list" where
  "aux_terms c = row_terms (constraint_expr c)"

definition aux_scalar :: "linear_constraint \<Rightarrow> real" where
  "aux_scalar c = constraint_scalar c - row_const (constraint_expr c)"

definition engine_ready :: "nat \<Rightarrow> query \<Rightarrow> bool" where
  "engine_ready n Q \<longleftrightarrow>
     list_all (\<lambda>c. is_equation c \<and> list_all (\<lambda>(a, x). x < n) (aux_terms c)) (linear_atoms Q) \<and>
     list_all (\<lambda>b. bound_variable b < n) (query_bounds Q) \<and>
     list_all (\<lambda>x. lowers (query_bounds Q) x \<noteq> [] \<and> uppers (query_bounds Q) x \<noteq> []) [0..<n]"

definition bounds_consistent :: "nat \<Rightarrow> query \<Rightarrow> bool" where
  "bounds_consistent n Q \<longleftrightarrow> list_all (\<lambda>x. lower_of Q x \<le> upper_of Q x) [0..<n]"

section \<open>The auxiliary-basis tableau\<close>

definition initial_rows :: "nat \<Rightarrow> query \<Rightarrow> var \<Rightarrow> linexpr" where
  "initial_rows n Q x =
     (if n \<le> x \<and> x < n + length (linear_atoms Q)
      then Linexpr 0 (aux_terms (linear_atoms Q ! (x - n)))
      else Linexpr 0 [])"

definition initial_lower :: "nat \<Rightarrow> query \<Rightarrow> var \<Rightarrow> real" where
  "initial_lower n Q x =
     (if x < n then lower_of Q x
      else if x < n + length (linear_atoms Q) then aux_scalar (linear_atoms Q ! (x - n))
      else 0)"

definition initial_upper :: "nat \<Rightarrow> query \<Rightarrow> var \<Rightarrow> real" where
  "initial_upper n Q x =
     (if x < n then upper_of Q x
      else if x < n + length (linear_atoms Q) then aux_scalar (linear_atoms Q ! (x - n))
      else 0)"

definition initial_tableau :: "nat \<Rightarrow> query \<Rightarrow> tableau_state" where
  "initial_tableau n Q =
     \<lparr>tableau_basics = set [n..<n + length (linear_atoms Q)],
      tableau_nonbasics = set [0..<n],
      tableau_rows = initial_rows n Q,
      tableau_lower = initial_lower n Q,
      tableau_upper = initial_upper n Q,
      tableau_nonbasic_value = initial_lower n Q,
      tableau_basic_value = (\<lambda>x. eval_linexpr (initial_lower n Q) (initial_rows n Q x))\<rparr>"

abbreviation initial_basics :: "nat \<Rightarrow> query \<Rightarrow> var list" where
  "initial_basics n Q \<equiv> [n..<n + length (linear_atoms Q)]"

text \<open>The query's valuation, extended by the auxiliary values.\<close>

definition extend_aux :: "nat \<Rightarrow> query \<Rightarrow> valuation \<Rightarrow> valuation" where
  "extend_aux n Q v x =
     (if n \<le> x \<and> x < n + length (linear_atoms Q)
      then eval_terms v (aux_terms (linear_atoms Q ! (x - n)))
      else v x)"

section \<open>Bounds and equations\<close>

lemma lowers_mem: "l \<in> set (lowers bs x) \<longleftrightarrow> Lower x l \<in> set bs"
  by (induction bs x rule: lowers.induct) auto

lemma uppers_mem: "u \<in> set (uppers bs x) \<longleftrightarrow> Upper x u \<in> set bs"
  by (induction bs x rule: uppers.induct) auto

lemma bounds_iff:
  "(\<forall>b\<in>set bs. satisfies_bound v b) \<longleftrightarrow>
     (\<forall>x. (\<forall>l\<in>set (lowers bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers bs x). v x \<le> u))"
proof
  assume all: "\<forall>b\<in>set bs. satisfies_bound v b"
  have "\<And>x l. Lower x l \<in> set bs \<Longrightarrow> l \<le> v x" "\<And>x u. Upper x u \<in> set bs \<Longrightarrow> v x \<le> u"
    using all by fastforce+
  then show "\<forall>x. (\<forall>l\<in>set (lowers bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers bs x). v x \<le> u)"
    by (simp add: lowers_mem uppers_mem)
next
  assume all: "\<forall>x. (\<forall>l\<in>set (lowers bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers bs x). v x \<le> u)"
  show "\<forall>b\<in>set bs. satisfies_bound v b"
  proof
    fix b
    assume b: "b \<in> set bs"
    show "satisfies_bound v b"
    proof (cases b)
      case (Lower x l)
      then have "l \<in> set (lowers bs x)" using b lowers_mem by simp
      then show ?thesis using all Lower by simp
    next
      case (Upper x u)
      then have "u \<in> set (uppers bs x)" using b uppers_mem by simp
      then show ?thesis using all Upper by simp
    qed
  qed
qed

lemma engine_ready_facts:
  assumes "engine_ready n Q"
  shows "\<And>c. c \<in> set (linear_atoms Q) \<Longrightarrow> is_equation c"
    and "\<And>c a x. c \<in> set (linear_atoms Q) \<Longrightarrow> (a, x) \<in> set (aux_terms c) \<Longrightarrow> x < n"
    and "\<And>b. b \<in> set (query_bounds Q) \<Longrightarrow> bound_variable b < n"
    and "\<And>x. x < n \<Longrightarrow> lowers (query_bounds Q) x \<noteq> []"
    and "\<And>x. x < n \<Longrightarrow> uppers (query_bounds Q) x \<noteq> []"
  using assms unfolding engine_ready_def list_all_iff by fastforce+

lemma query_bounds_iff:
  assumes ready: "engine_ready n Q"
  shows "(\<forall>b\<in>set (query_bounds Q). satisfies_bound v b) \<longleftrightarrow>
         (\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x)"
proof -
  let ?bs = "query_bounds Q"
  have outside: "\<And>x. \<not> x < n \<Longrightarrow> lowers ?bs x = [] \<and> uppers ?bs x = []"
  proof -
    fix x
    assume x: "\<not> x < n"
    have "\<And>l. Lower x l \<notin> set ?bs" "\<And>u. Upper x u \<notin> set ?bs"
      using engine_ready_facts(3)[OF ready] x by force+
    then show "lowers ?bs x = [] \<and> uppers ?bs x = []"
      by (metis lowers_mem uppers_mem last_in_set)
  qed
  have inside: "\<And>x. x < n \<Longrightarrow>
      ((\<forall>l\<in>set (lowers ?bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers ?bs x). v x \<le> u)) \<longleftrightarrow>
      lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x"
    using engine_ready_facts(4,5)[OF ready]
    by (simp add: lower_of_def upper_of_def Max_le_iff Min_ge_iff)
  show ?thesis
    unfolding bounds_iff
  proof
    assume "\<forall>x. (\<forall>l\<in>set (lowers ?bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers ?bs x). v x \<le> u)"
    then show "\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x"
      using inside by blast
  next
    assume "\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x"
    then show "\<forall>x. (\<forall>l\<in>set (lowers ?bs x). l \<le> v x) \<and> (\<forall>u\<in>set (uppers ?bs x). v x \<le> u)"
      using inside outside by (metis empty_iff list.set(1) not_less)
  qed
qed

lemma equation_iff:
  "is_equation c \<Longrightarrow> satisfies_linear v c \<longleftrightarrow> eval_terms v (aux_terms c) = aux_scalar c"
  by (cases c) (auto simp: aux_terms_def aux_scalar_def eval_linexpr_parts)

lemma inconsistent_bounds_unsatisfiable:
  assumes "engine_ready n Q" "\<not> bounds_consistent n Q"
  shows "unsatisfiable Q"
proof -
  obtain x where x: "x < n" "upper_of Q x < lower_of Q x"
    using assms(2) unfolding bounds_consistent_def list_all_iff by auto
  show ?thesis
    unfolding unsatisfiable_def satisfiable_def satisfies_query_def
    using query_bounds_iff[OF assms(1)] x by force
qed

section \<open>The tableau represents the linear part of the query\<close>

lemma initial_tableau_simps:
  "tableau_basics (initial_tableau n Q) = set (initial_basics n Q)"
  "tableau_nonbasics (initial_tableau n Q) = set [0..<n]"
  "tableau_rows (initial_tableau n Q) = initial_rows n Q"
  "tableau_lower (initial_tableau n Q) = initial_lower n Q"
  "tableau_upper (initial_tableau n Q) = initial_upper n Q"
  by (simp_all add: initial_tableau_def)

lemma aux_range: "x \<in> set (initial_basics n Q) \<longleftrightarrow> n \<le> x \<and> x < n + length (linear_atoms Q)"
  by simp

theorem initial_tableau_invariant:
  assumes ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
  shows "simplex_invariant (initial_tableau n Q) (initial_basics n Q) [0..<n]"
proof -
  let ?S = "initial_tableau n Q" and ?E = "linear_atoms Q"
  have support: "\<And>x. x \<in> set (initial_basics n Q) \<Longrightarrow> linexpr_vars (initial_rows n Q x) \<subseteq> set [0..<n]"
  proof
    fix x y
    assume x: "x \<in> set (initial_basics n Q)" and y: "y \<in> linexpr_vars (initial_rows n Q x)"
    have i: "x - n < length ?E" using x by auto
    obtain a where "(a, y) \<in> set (aux_terms (?E ! (x - n)))"
      using y x by (auto simp: initial_rows_def)
    then have "y < n" using engine_ready_facts(2)[OF ready nth_mem[OF i]] by blast
    then show "y \<in> set [0..<n]" by simp
  qed
  have sup: "tableau_rows_supported ?S"
    using support unfolding tableau_rows_supported_def initial_tableau_simps by auto
  have rows: "tableau_rows_satisfied ?S"
    by (simp add: tableau_rows_satisfied_def initial_tableau_def)
  have ordered: "\<And>x. x < n \<Longrightarrow> lower_of Q x \<le> upper_of Q x"
    using consistent unfolding bounds_consistent_def list_all_iff by simp
  have nb: "tableau_nonbasic_bounds_satisfied ?S"
    using ordered
    by (simp add: tableau_nonbasic_bounds_satisfied_def initial_tableau_def initial_lower_def
        initial_upper_def)
  have ord: "tableau_bounds_ordered ?S"
    using ordered
    by (auto simp: tableau_bounds_ordered_def initial_tableau_def initial_lower_def initial_upper_def)
  show ?thesis
    using sup rows nb ord by (simp add: simplex_invariant_def initial_tableau_simps)
qed

theorem initial_bounded_models:
  assumes ready: "engine_ready n Q"
  shows "v \<in> tableau_bounded_models (initial_tableau n Q) \<longleftrightarrow>
    (\<forall>x. n \<le> x \<longrightarrow> x < n + length (linear_atoms Q) \<longrightarrow>
       v x = eval_terms v (aux_terms (linear_atoms Q ! (x - n))) \<and>
       v x = aux_scalar (linear_atoms Q ! (x - n))) \<and>
    (\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x)"
proof -
  have models: "v \<in> tableau_models (initial_tableau n Q) \<longleftrightarrow>
      (\<forall>x. n \<le> x \<longrightarrow> x < n + length (linear_atoms Q) \<longrightarrow>
         v x = eval_terms v (aux_terms (linear_atoms Q ! (x - n))))"
    by (auto simp: tableau_models_def initial_tableau_def initial_rows_def)
  have within: "(\<forall>x\<in>tableau_basics (initial_tableau n Q) \<union> tableau_nonbasics (initial_tableau n Q).
        tableau_lower (initial_tableau n Q) x \<le> v x \<and> v x \<le> tableau_upper (initial_tableau n Q) x) \<longleftrightarrow>
      (\<forall>x. n \<le> x \<longrightarrow> x < n + length (linear_atoms Q) \<longrightarrow>
         v x = aux_scalar (linear_atoms Q ! (x - n))) \<and>
      (\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x)"
    by (auto simp: initial_tableau_def initial_lower_def initial_upper_def)
  show ?thesis
    using models within unfolding tableau_bounded_models_def by blast
qed

lemma eval_aux_terms_extend:
  assumes ready: "engine_ready n Q" and c: "c \<in> set (linear_atoms Q)"
  shows "eval_terms (extend_aux n Q v) (aux_terms c) = eval_terms v (aux_terms c)"
proof -
  have "eval_linexpr (extend_aux n Q v) (Linexpr 0 (aux_terms c)) =
        eval_linexpr v (Linexpr 0 (aux_terms c))"
  proof (rule eval_linexpr_vars_cong)
    fix x
    assume "x \<in> linexpr_vars (Linexpr 0 (aux_terms c))"
    then have "x < n" using engine_ready_facts(2)[OF ready c] by auto
    then show "extend_aux n Q v x = v x" by (simp add: extend_aux_def)
  qed
  then show ?thesis by simp
qed

theorem query_model_extends:
  assumes ready: "engine_ready n Q"
      and linear: "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
      and bounds: "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
  shows "extend_aux n Q v \<in> tableau_bounded_models (initial_tableau n Q)"
proof -
  let ?w = "extend_aux n Q v" and ?E = "linear_atoms Q"
  have aux: "\<forall>x. n \<le> x \<longrightarrow> x < n + length ?E \<longrightarrow>
      ?w x = eval_terms ?w (aux_terms (?E ! (x - n))) \<and> ?w x = aux_scalar (?E ! (x - n))"
  proof (intro allI impI)
    fix x
    assume x: "n \<le> x" "x < n + length ?E"
    have c: "?E ! (x - n) \<in> set ?E" using x by simp
    have wx: "?w x = eval_terms v (aux_terms (?E ! (x - n)))"
      using x by (simp add: extend_aux_def)
    have "eval_terms v (aux_terms (?E ! (x - n))) = aux_scalar (?E ! (x - n))"
      using linear c equation_iff[OF engine_ready_facts(1)[OF ready c]] by blast
    then show "?w x = eval_terms ?w (aux_terms (?E ! (x - n))) \<and> ?w x = aux_scalar (?E ! (x - n))"
      using wx eval_aux_terms_extend[OF ready c] by simp
  qed
  have low: "\<forall>x<n. lower_of Q x \<le> ?w x \<and> ?w x \<le> upper_of Q x"
    using bounds query_bounds_iff[OF ready] by (simp add: extend_aux_def)
  show ?thesis
    using aux low initial_bounded_models[OF ready] by blast
qed

theorem bounded_model_satisfies_linear_part:
  assumes ready: "engine_ready n Q"
      and v: "v \<in> tableau_bounded_models (initial_tableau n Q)"
  shows "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
    and "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
proof -
  let ?E = "linear_atoms Q"
  have aux: "\<And>x. n \<le> x \<Longrightarrow> x < n + length ?E \<Longrightarrow>
      v x = eval_terms v (aux_terms (?E ! (x - n))) \<and> v x = aux_scalar (?E ! (x - n))"
    and low: "\<forall>x<n. lower_of Q x \<le> v x \<and> v x \<le> upper_of Q x"
    using v initial_bounded_models[OF ready] by blast+
  show "\<forall>c\<in>set ?E. satisfies_linear v c"
  proof
    fix c
    assume "c \<in> set ?E"
    then obtain i where i: "i < length ?E" "c = ?E ! i" by (auto simp: in_set_conv_nth)
    have "eval_terms v (aux_terms c) = aux_scalar c"
      using aux[of "n + i"] i by simp
    then show "satisfies_linear v c"
      using equation_iff engine_ready_facts(1)[OF ready] i nth_mem by metis
  qed
  show "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
    using low query_bounds_iff[OF ready] by blast
qed

corollary initial_empty_unsatisfiable:
  assumes "engine_ready n Q" "tableau_bounded_models (initial_tableau n Q) = {}"
  shows "unsatisfiable Q"
  using assms query_model_extends
  unfolding unsatisfiable_def satisfiable_def satisfies_query_def by blast

section \<open>Solving the linear part of a query\<close>

datatype linear_result =
    is_simplex_unsat: Simplex_Unsat
  | Simplex_Feasible valuation
  | is_simplex_unknown: Simplex_Unknown

text \<open>A feasible result holds a function, so results are tested by discriminator.\<close>

lemma is_simplex_unsat_iff: "is_simplex_unsat r \<longleftrightarrow> r = Simplex_Unsat"
  by (cases r) simp_all

definition solve_linear_part :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> linear_result" where
  "solve_linear_part fuel n Q =
     (if \<not> engine_ready n Q then Simplex_Unknown
      else if \<not> bounds_consistent n Q then Simplex_Unsat
      else (case simplex_run fuel (initial_tableau n Q) (initial_basics n Q) [0..<n] of
              (Feasible, S', _) \<Rightarrow> Simplex_Feasible (tableau_candidate S')
            | (Infeasible, _) \<Rightarrow> Simplex_Unsat
            | (Out_Of_Fuel, _) \<Rightarrow> Simplex_Unknown))"

theorem solve_linear_part_unsat:
  assumes "solve_linear_part fuel n Q = Simplex_Unsat"
  shows "unsatisfiable Q"
proof -
  have ready: "engine_ready n Q"
    using assms by (auto simp: solve_linear_part_def split: if_splits)
  show ?thesis
  proof (cases "bounds_consistent n Q")
    case False
    then show ?thesis using inconsistent_bounds_unsatisfiable[OF ready] by blast
  next
    case True
    obtain r S' bs' ns' where run:
        "simplex_run fuel (initial_tableau n Q) (initial_basics n Q) [0..<n] = (r, S', bs', ns')"
      by (cases "simplex_run fuel (initial_tableau n Q) (initial_basics n Q) [0..<n]") auto
    have "r = Infeasible"
      using assms ready True run
      by (cases r) (simp_all add: solve_linear_part_def)
    then have "tableau_bounded_models (initial_tableau n Q) = {}"
      using simplex_run_sound(4)[OF initial_tableau_invariant[OF ready True] run] by blast
    then show ?thesis using initial_empty_unsatisfiable[OF ready] by blast
  qed
qed

theorem solve_linear_part_feasible:
  assumes "solve_linear_part fuel n Q = Simplex_Feasible v"
  shows "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
    and "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
proof -
  have ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
    using assms by (auto simp: solve_linear_part_def split: if_splits)
  obtain r S' bs' ns' where run:
      "simplex_run fuel (initial_tableau n Q) (initial_basics n Q) [0..<n] = (r, S', bs', ns')"
    by (cases "simplex_run fuel (initial_tableau n Q) (initial_basics n Q) [0..<n]") auto
  have r: "r = Feasible" and v: "v = tableau_candidate S'"
    using assms ready consistent run
    by (cases r; simp add: solve_linear_part_def)+
  have "v \<in> tableau_bounded_models (initial_tableau n Q)"
    using simplex_run_sound(3)[OF initial_tableau_invariant[OF ready consistent] run r] v by simp
  then show "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
    "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
    using bounded_model_satisfies_linear_part[OF ready] by blast+
qed

theorem solve_linear_part_model:
  assumes "solve_linear_part fuel n Q = Simplex_Feasible v"
      and "list_all (satisfies_relu_constraint v) (relu_atoms Q)"
  shows "satisfies_query v Q"
  using solve_linear_part_feasible[OF assms(1)] assms(2)
  unfolding satisfies_query_def list_all_iff by blast

corollary solve_linear_part_sat:
  assumes "solve_linear_part fuel n Q = Simplex_Feasible v" "relu_atoms Q = []"
  shows "satisfiable Q"
  using solve_linear_part_model[OF assms(1)] assms(2) unfolding satisfiable_def by auto

export_code solve_linear_part initial_tableau engine_ready checking SML

end
