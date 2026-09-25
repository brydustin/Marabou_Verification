theory Tableau_Pivot
  imports Tableau_Assignment_Update
begin

text \<open>
  Exact basis exchange: the algebraic core of Tableau::performPivot
  (src/engine/Tableau.cpp:696-801) and Tableau::performDegeneratePivot
  (803-850). The leaving basic variable b and the entering nonbasic variable e
  swap roles, the solved rows are rewritten and the stored values move between
  the basic and nonbasic stores. Native Marabou keeps the rows implicitly, as a
  factorization of the basis matrix; Tableau::getTableauRow (1568-1607)
  computes row i as xb = scalar + \<Sum> c_j x_j. Here each basic variable's
  solved row is explicit. The pivot element is the entering variable's
  coefficient in the leaving row: native pivotEntryByRow, which
  performPivot compares with -changeColumn[leaving] (765-769).
  No factorization, floating-point rounding or tolerance is modeled.
\<close>

section \<open>Rows as constant plus terms\<close>

fun row_terms :: "linexpr \<Rightarrow> (real \<times> var) list" where
  "row_terms (Linexpr c ts) = ts"

fun row_const :: "linexpr \<Rightarrow> real" where
  "row_const (Linexpr c ts) = c"

definition row_coefficient :: "linexpr \<Rightarrow> var \<Rightarrow> real" where
  "row_coefficient r x = linexpr_coefficient (row_terms r) x"

definition drop_var :: "(real \<times> var) list \<Rightarrow> var \<Rightarrow> (real \<times> var) list" where
  "drop_var ts x = filter (\<lambda>(a, y). y \<noteq> x) ts"

definition scale_terms :: "real \<Rightarrow> (real \<times> var) list \<Rightarrow> (real \<times> var) list" where
  "scale_terms k ts = map (\<lambda>(a, y). (k * a, y)) ts"

lemma eval_linexpr_parts:
  "eval_linexpr v r = row_const r + eval_terms v (row_terms r)"
  by (cases r) simp

lemma linexpr_vars_parts:
  "linexpr_vars r = snd ` set (row_terms r)"
  by (cases r) simp

lemma eval_terms_drop_var:
  "eval_terms v ts = eval_terms v (drop_var ts x) + linexpr_coefficient ts x * v x"
  by (induction ts x rule: linexpr_coefficient.induct)
     (auto simp: drop_var_def algebra_simps)

lemma eval_terms_scale_terms [simp]:
  "eval_terms v (scale_terms k ts) = k * eval_terms v ts"
  by (simp add: scale_terms_def eval_terms_scale)

lemma coefficient_drop_var_same [simp]:
  "linexpr_coefficient (drop_var ts x) x = 0"
  by (induction ts x rule: linexpr_coefficient.induct) (auto simp: drop_var_def)

lemma coefficient_drop_var_other:
  "y \<noteq> x \<Longrightarrow> linexpr_coefficient (drop_var ts x) y = linexpr_coefficient ts y"
  by (induction ts y rule: linexpr_coefficient.induct) (auto simp: drop_var_def)

lemma coefficient_scale_terms [simp]:
  "linexpr_coefficient (scale_terms k ts) x = k * linexpr_coefficient ts x"
  by (induction ts x rule: linexpr_coefficient.induct)
     (auto simp: scale_terms_def algebra_simps)

lemma coefficient_append [simp]:
  "linexpr_coefficient (ts @ us) x =
     linexpr_coefficient ts x + linexpr_coefficient us x"
  by (induction ts x rule: linexpr_coefficient.induct) auto

lemma coefficient_absent:
  "x \<notin> snd ` set ts \<Longrightarrow> linexpr_coefficient ts x = 0"
  by (induction ts x rule: linexpr_coefficient.induct) (auto simp: image_iff)

lemma vars_drop_var [simp]:
  "snd ` set (drop_var ts x) = snd ` set ts - {x}"
  unfolding drop_var_def by force

lemma vars_scale_terms [simp]:
  "snd ` set (scale_terms k ts) = snd ` set ts"
  unfolding scale_terms_def by force

lemma eval_row_split:
  "eval_linexpr v r =
     row_const r + eval_terms v (drop_var (row_terms r) e) + row_coefficient r e * v e"
  using eval_terms_drop_var[of v "row_terms r" e]
  by (simp add: eval_linexpr_parts row_coefficient_def)

section \<open>Solving the leaving row and substituting it\<close>

text \<open>
  If xb = c + a*xe + rest with a \<noteq> 0, then xe = (xb - c - rest) / a.
\<close>

definition solve_row :: "var \<Rightarrow> linexpr \<Rightarrow> var \<Rightarrow> linexpr" where
  "solve_row b r e =
     Linexpr (- row_const r / row_coefficient r e)
       ((1 / row_coefficient r e, b) #
          scale_terms (- 1 / row_coefficient r e) (drop_var (row_terms r) e))"

definition substitute_row :: "var \<Rightarrow> linexpr \<Rightarrow> linexpr \<Rightarrow> linexpr" where
  "substitute_row e s r =
     Linexpr (row_const r + row_coefficient r e * row_const s)
       (drop_var (row_terms r) e @ scale_terms (row_coefficient r e) (row_terms s))"

lemma eval_solve_row:
  assumes "row_coefficient r e \<noteq> 0"
  shows "eval_linexpr v (solve_row b r e) =
    (v b - row_const r - eval_terms v (drop_var (row_terms r) e)) / row_coefficient r e"
  using assms by (simp add: solve_row_def field_simps)

lemma solve_row_iff:
  assumes a: "row_coefficient r e \<noteq> 0"
  shows "v b = eval_linexpr v r \<longleftrightarrow> v e = eval_linexpr v (solve_row b r e)"
  using eval_row_split[of v r e] eval_solve_row[OF a, of v b] a
  by (auto simp: field_simps)

lemma eval_substitute_row:
  "eval_linexpr v (substitute_row e s r) =
     eval_linexpr v r + row_coefficient r e * (eval_linexpr v s - v e)"
  using eval_row_split[of v r e] eval_linexpr_parts[of v s]
  by (simp add: substitute_row_def algebra_simps)

lemma vars_solve_row:
  "linexpr_vars (solve_row b r e) = insert b (linexpr_vars r - {e})"
  by (simp add: solve_row_def linexpr_vars_parts)

lemma vars_substitute_row:
  "linexpr_vars (substitute_row e s r) = (linexpr_vars r - {e}) \<union> linexpr_vars s"
  by (simp add: substitute_row_def linexpr_vars_parts image_Un)

lemma coefficient_solve_row_leaving:
  assumes "b \<notin> linexpr_vars r" "b \<noteq> e"
  shows "row_coefficient (solve_row b r e) b = 1 / row_coefficient r e"
  using assms coefficient_absent[of b "row_terms r"]
  by (simp add: solve_row_def row_coefficient_def coefficient_drop_var_other
      linexpr_vars_parts)

section \<open>The exchange\<close>

definition exchange_rows ::
  "(var \<Rightarrow> linexpr) \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> linexpr" where
  "exchange_rows R b e x =
     (if x = e then solve_row b (R b) e
      else substitute_row e (solve_row b (R b) e) (R x))"

text \<open>
  Code equations for kernel-checked evaluation (code_simp), which also
  normalizes under binders. As defined, exchange_rows and substitute_row
  mention the old row several times, so every exchange would copy the
  previous row function into the new one several times. These equivalent
  forms mention it once.
\<close>

lemma exchange_rows_code [code]:
  "exchange_rows R b e x = (let s = solve_row b (R b) e in if x = e then s else substitute_row e s (R x))"
  by (simp add: exchange_rows_def Let_def)

lemma substitute_row_code [code]:
  "substitute_row e s r =
     (case r of Linexpr c ts \<Rightarrow>
        Linexpr (c + linexpr_coefficient ts e * row_const s)
          (drop_var ts e @ scale_terms (linexpr_coefficient ts e) (row_terms s)))"
  by (cases r) (simp add: substitute_row_def row_coefficient_def)

text \<open>
  The value stores are indexed by variable, so the native array swap
  (Tableau.cpp:839-841, "values haven't changed") is a move between the two
  stores; the candidate valuation is unchanged (exchange_candidate).
\<close>

definition exchange_basis :: "tableau_state \<Rightarrow> var \<Rightarrow> var \<Rightarrow> tableau_state" where
  "exchange_basis S b e = S\<lparr>
     tableau_basics := insert e (tableau_basics S - {b}),
     tableau_nonbasics := insert b (tableau_nonbasics S - {e}),
     tableau_rows := exchange_rows (tableau_rows S) b e,
     tableau_nonbasic_value := (tableau_nonbasic_value S)(b := tableau_basic_value S b),
     tableau_basic_value := (tableau_basic_value S)(e := tableau_nonbasic_value S e)\<rparr>"

definition pivot_admissible :: "tableau_state \<Rightarrow> var \<Rightarrow> var \<Rightarrow> bool" where
  "pivot_admissible S b e \<longleftrightarrow>
     b \<in> tableau_basics S \<and> e \<in> tableau_nonbasics S \<and>
     row_coefficient (tableau_rows S b) e \<noteq> 0"

text \<open>Well-formedness without the nonbasic bound-order conjunct.\<close>

definition tableau_rows_supported :: "tableau_state \<Rightarrow> bool" where
  "tableau_rows_supported S \<longleftrightarrow>
     tableau_basics S \<inter> tableau_nonbasics S = {} \<and>
     (\<forall>b\<in>tableau_basics S. linexpr_vars (tableau_rows S b) \<subseteq> tableau_nonbasics S)"

lemma well_formed_rows_supported:
  "tableau_well_formed S \<Longrightarrow> tableau_rows_supported S"
  unfolding tableau_well_formed_def tableau_rows_supported_def by blast

lemma exchange_basis_simps [simp]:
  "tableau_basics (exchange_basis S b e) = insert e (tableau_basics S - {b})"
  "tableau_nonbasics (exchange_basis S b e) = insert b (tableau_nonbasics S - {e})"
  "tableau_rows (exchange_basis S b e) = exchange_rows (tableau_rows S) b e"
  "tableau_lower (exchange_basis S b e) = tableau_lower S"
  "tableau_upper (exchange_basis S b e) = tableau_upper S"
  by (simp_all add: exchange_basis_def)

lemma pivot_admissible_facts:
  assumes "pivot_admissible S b e" "tableau_rows_supported S"
  shows "b \<in> tableau_basics S" "e \<in> tableau_nonbasics S" "e \<notin> tableau_basics S"
    "b \<notin> tableau_nonbasics S" "b \<noteq> e" "row_coefficient (tableau_rows S b) e \<noteq> 0"
  using assms unfolding pivot_admissible_def tableau_rows_supported_def by auto

lemma exchange_carrier:
  assumes "pivot_admissible S b e"
  shows "tableau_basics (exchange_basis S b e) \<union> tableau_nonbasics (exchange_basis S b e) =
         tableau_basics S \<union> tableau_nonbasics S"
  using assms unfolding pivot_admissible_def by auto

theorem exchange_models:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
  shows "tableau_models (exchange_basis S b e) = tableau_models S"
proof -
  let ?R = "tableau_rows S"
  let ?s = "solve_row b (?R b) e"
  have b: "b \<in> tableau_basics S" and e: "e \<notin> tableau_basics S"
    and a: "row_coefficient (?R b) e \<noteq> 0"
    using pivot_admissible_facts[OF p sup] by auto
  have other_row:
    "\<And>v x. x \<in> tableau_basics S \<Longrightarrow> v e = eval_linexpr v ?s \<Longrightarrow>
       eval_linexpr v (exchange_rows ?R b e x) = eval_linexpr v (?R x)"
    using e by (auto simp: exchange_rows_def eval_substitute_row)
  show ?thesis
  proof (rule set_eqI)
    fix v
    have new: "v \<in> tableau_models (exchange_basis S b e) \<longleftrightarrow>
        v e = eval_linexpr v ?s \<and>
        (\<forall>x\<in>tableau_basics S - {b}. v x = eval_linexpr v (exchange_rows ?R b e x))"
      unfolding tableau_models_def by (simp add: exchange_rows_def)
    have old: "v \<in> tableau_models S \<longleftrightarrow>
        v b = eval_linexpr v (?R b) \<and>
        (\<forall>x\<in>tableau_basics S - {b}. v x = eval_linexpr v (?R x))"
      unfolding tableau_models_def using b by blast
    show "v \<in> tableau_models (exchange_basis S b e) \<longleftrightarrow> v \<in> tableau_models S"
      unfolding new old solve_row_iff[OF a, of v b] using other_row by auto
  qed
qed

theorem exchange_rows_supported:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
  shows "tableau_rows_supported (exchange_basis S b e)"
proof -
  let ?R = "tableau_rows S"
  have facts: "b \<in> tableau_basics S" "e \<in> tableau_nonbasics S"
    "e \<notin> tableau_basics S" "b \<notin> tableau_nonbasics S" "b \<noteq> e"
    using pivot_admissible_facts[OF p sup] by auto
  have support: "\<And>x. x \<in> tableau_basics S \<Longrightarrow> linexpr_vars (?R x) \<subseteq> tableau_nonbasics S"
    using sup unfolding tableau_rows_supported_def by blast
  have disjoint: "tableau_basics S \<inter> tableau_nonbasics S = {}"
    using sup unfolding tableau_rows_supported_def by blast
  have solved: "linexpr_vars (solve_row b (?R b) e) \<subseteq> insert b (tableau_nonbasics S - {e})"
    using support[OF facts(1)] by (auto simp: vars_solve_row)
  have substituted:
    "\<And>x. x \<in> tableau_basics S \<Longrightarrow>
       linexpr_vars (substitute_row e (solve_row b (?R b) e) (?R x)) \<subseteq>
         insert b (tableau_nonbasics S - {e})"
    using vars_substitute_row solved support by blast
  show ?thesis
    unfolding tableau_rows_supported_def
    using facts disjoint solved substituted by (auto simp: exchange_rows_def)
qed

theorem exchange_well_formed:
  assumes wf: "tableau_well_formed S" and p: "pivot_admissible S b e"
      and ordered: "tableau_lower S b \<le> tableau_upper S b"
  shows "tableau_well_formed (exchange_basis S b e)"
proof -
  have sup: "tableau_rows_supported (exchange_basis S b e)"
    using exchange_rows_supported[OF p well_formed_rows_supported[OF wf]] .
  have "finite (tableau_basics S)" "finite (tableau_nonbasics S)"
    "\<forall>j\<in>tableau_nonbasics S. tableau_lower S j \<le> tableau_upper S j"
    using wf unfolding tableau_well_formed_def by auto
  then show ?thesis
    using sup ordered unfolding tableau_well_formed_def tableau_rows_supported_def by auto
qed

theorem exchange_candidate:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
  shows "tableau_candidate (exchange_basis S b e) = tableau_candidate S"
  using pivot_admissible_facts[OF p sup]
  by (auto simp: fun_eq_iff tableau_candidate_def exchange_basis_def)

theorem exchange_nonbasic_bounds:
  assumes "tableau_nonbasic_bounds_satisfied S"
      and "tableau_lower S b \<le> tableau_basic_value S b"
      and "tableau_basic_value S b \<le> tableau_upper S b"
  shows "tableau_nonbasic_bounds_satisfied (exchange_basis S b e)"
  using assms
  by (auto simp: tableau_nonbasic_bounds_satisfied_def exchange_basis_def)

section \<open>Row satisfaction through the candidate valuation\<close>

lemma candidate_row_eval:
  assumes sup: "tableau_rows_supported S" and x: "x \<in> tableau_basics S"
  shows "eval_linexpr (tableau_candidate S) (tableau_rows S x) =
         eval_linexpr (tableau_nonbasic_value S) (tableau_rows S x)"
proof (rule eval_linexpr_vars_cong)
  fix y
  assume "y \<in> linexpr_vars (tableau_rows S x)"
  then have "y \<in> tableau_nonbasics S" "y \<notin> tableau_basics S"
    using sup x unfolding tableau_rows_supported_def by blast+
  then show "tableau_candidate S y = tableau_nonbasic_value S y"
    by (simp add: tableau_candidate_def)
qed

lemma rows_satisfied_iff_candidate:
  assumes sup: "tableau_rows_supported S"
  shows "tableau_rows_satisfied S \<longleftrightarrow> tableau_candidate S \<in> tableau_models S"
  using candidate_row_eval[OF sup]
  unfolding tableau_rows_satisfied_def tableau_models_def
  by (auto simp: tableau_candidate_def)

theorem exchange_rows_satisfied:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
      and rows: "tableau_rows_satisfied S"
  shows "tableau_rows_satisfied (exchange_basis S b e)"
  using rows
  unfolding rows_satisfied_iff_candidate[OF sup]
    rows_satisfied_iff_candidate[OF exchange_rows_supported[OF p sup]]
    exchange_candidate[OF p sup] exchange_models[OF p sup] .

theorem exchange_pivot_element:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
  shows "row_coefficient (tableau_rows (exchange_basis S b e) e) b =
           1 / row_coefficient (tableau_rows S b) e"
proof -
  have facts: "b \<in> tableau_basics S" "b \<notin> tableau_nonbasics S" "b \<noteq> e"
    using pivot_admissible_facts[OF p sup] by auto
  have "b \<notin> linexpr_vars (tableau_rows S b)"
    using sup facts unfolding tableau_rows_supported_def by blast
  then show ?thesis
    using facts by (simp add: exchange_rows_def coefficient_solve_row_leaving)
qed

corollary exchange_back_admissible:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
  shows "pivot_admissible (exchange_basis S b e) e b"
  using exchange_pivot_element[OF p sup] pivot_admissible_facts[OF p sup]
  unfolding pivot_admissible_def by auto

section \<open>The solved form of a basis is unique\<close>

text \<open>
  Two supported solved forms with the same basic and nonbasic variables and the
  same solutions have rows that agree on every valuation. So whatever computes
  the rows of a basis, in particular an exact B\<inverse>-based computation as in
  getTableauRow, obtains rows equal in value to the rows produced here. This
  states the matrix interpretation as an obligation on the native rows, not a
  proof about the native factorization.
\<close>

theorem solved_rows_unique:
  assumes S: "tableau_rows_supported S" and T: "tableau_rows_supported T"
      and basics: "tableau_basics T = tableau_basics S"
      and nonbasics: "tableau_nonbasics T = tableau_nonbasics S"
      and models: "tableau_models T = tableau_models S"
      and x: "x \<in> tableau_basics S"
  shows "eval_linexpr v (tableau_rows T x) = eval_linexpr v (tableau_rows S x)"
proof -
  let ?w = "\<lambda>y. if y \<in> tableau_basics S then eval_linexpr v (tableau_rows S y) else v y"
  have agree: "\<And>R y. tableau_rows_supported R \<Longrightarrow>
      tableau_basics R = tableau_basics S \<Longrightarrow> tableau_nonbasics R = tableau_nonbasics S \<Longrightarrow>
      y \<in> tableau_basics S \<Longrightarrow>
      eval_linexpr ?w (tableau_rows R y) = eval_linexpr v (tableau_rows R y)"
  proof -
    fix R y
    assume R: "tableau_rows_supported R" "tableau_basics R = tableau_basics S"
      "tableau_nonbasics R = tableau_nonbasics S" and y: "y \<in> tableau_basics S"
    show "eval_linexpr ?w (tableau_rows R y) = eval_linexpr v (tableau_rows R y)"
    proof (rule eval_linexpr_vars_cong)
      fix z
      assume "z \<in> linexpr_vars (tableau_rows R y)"
      then have "z \<notin> tableau_basics S"
        using R y unfolding tableau_rows_supported_def by blast
      then show "?w z = v z" by simp
    qed
  qed
  have "?w \<in> tableau_models S"
    unfolding tableau_models_def using agree[OF S refl refl] by simp
  then have "?w \<in> tableau_models T"
    using models by simp
  then have "?w x = eval_linexpr ?w (tableau_rows T x)"
    using x basics unfolding tableau_models_def by blast
  then show ?thesis
    using agree[OF T basics nonbasics x] x by simp
qed

corollary exchange_back_rows:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
      and x: "x \<in> tableau_basics S"
  shows "eval_linexpr v (tableau_rows (exchange_basis (exchange_basis S b e) e b) x) =
         eval_linexpr v (tableau_rows S x)"
proof -
  let ?S1 = "exchange_basis S b e"
  have p1: "pivot_admissible ?S1 e b"
    using exchange_back_admissible[OF p sup] .
  have sup1: "tableau_rows_supported ?S1"
    using exchange_rows_supported[OF p sup] .
  have facts: "b \<in> tableau_basics S" "e \<in> tableau_nonbasics S" "b \<noteq> e"
    "e \<notin> tableau_basics S" "b \<notin> tableau_nonbasics S"
    using pivot_admissible_facts[OF p sup] by auto
  show ?thesis
  proof (rule solved_rows_unique[OF sup exchange_rows_supported[OF p1 sup1] _ _ _ x])
    show "tableau_basics (exchange_basis ?S1 e b) = tableau_basics S"
      using facts by auto
    show "tableau_nonbasics (exchange_basis ?S1 e b) = tableau_nonbasics S"
      using facts by auto
    show "tableau_models (exchange_basis ?S1 e b) = tableau_models S"
      using exchange_models[OF p1 sup1] exchange_models[OF p sup] by simp
  qed
qed

section \<open>Represented equations and bounded solutions\<close>

definition tableau_represents :: "tableau_state \<Rightarrow> linear_constraint list \<Rightarrow> bool" where
  "tableau_represents S E \<longleftrightarrow>
     tableau_models S = {v. \<forall>c\<in>set E. satisfies_linear v c}"

theorem exchange_represents:
  assumes "pivot_admissible S b e" "tableau_rows_supported S" "tableau_represents S E"
  shows "tableau_represents (exchange_basis S b e) E"
  using assms exchange_models unfolding tableau_represents_def by simp

theorem basis_determines_rows:
  assumes "tableau_rows_supported S" "tableau_rows_supported T"
      "tableau_basics T = tableau_basics S" "tableau_nonbasics T = tableau_nonbasics S"
      "tableau_represents S E" "tableau_represents T E" "x \<in> tableau_basics S"
  shows "eval_linexpr v (tableau_rows T x) = eval_linexpr v (tableau_rows S x)"
  using assms solved_rows_unique unfolding tableau_represents_def by metis

definition tableau_bounded_models :: "tableau_state \<Rightarrow> valuation set" where
  "tableau_bounded_models S =
     {v \<in> tableau_models S.
        \<forall>x\<in>tableau_basics S \<union> tableau_nonbasics S.
          tableau_lower S x \<le> v x \<and> v x \<le> tableau_upper S x}"

theorem exchange_bounded_models:
  assumes "pivot_admissible S b e" "tableau_rows_supported S"
  shows "tableau_bounded_models (exchange_basis S b e) = tableau_bounded_models S"
  using exchange_models[OF assms] exchange_carrier[OF assms(1)]
  unfolding tableau_bounded_models_def by simp

section \<open>Pivot out, then set\<close>

text \<open>
  Engine::fixViolatedPlConstraintIfPossible (Engine.cpp:833-924) makes the
  basic variable to be repaired nonbasic with performDegeneratePivot, choosing
  the entering variable with the largest row coefficient (and returning when
  all are zero), and then calls setNonBasicAssignment(variable, value, true).
\<close>

definition pivot_and_set :: "tableau_state \<Rightarrow> var \<Rightarrow> var \<Rightarrow> real \<Rightarrow> tableau_state" where
  "pivot_and_set S b e t = update_nonbasic_assignment (exchange_basis S b e) b t"

theorem pivot_and_set_sound:
  assumes p: "pivot_admissible S b e" and sup: "tableau_rows_supported S"
      and rows: "tableau_rows_satisfied S"
  shows "tableau_rows_satisfied (pivot_and_set S b e t)"
    and "tableau_models (pivot_and_set S b e t) = tableau_models S"
    and "tableau_candidate (pivot_and_set S b e t) b = t"
    and "tableau_nonbasic_bounds_satisfied S \<Longrightarrow>
         tableau_lower S b \<le> tableau_basic_value S b \<Longrightarrow>
         tableau_basic_value S b \<le> tableau_upper S b \<Longrightarrow>
         tableau_lower S b \<le> t \<Longrightarrow> t \<le> tableau_upper S b \<Longrightarrow>
         tableau_nonbasic_bounds_satisfied (pivot_and_set S b e t)"
proof -
  have facts: "b \<noteq> e" using pivot_admissible_facts[OF p sup] by simp
  have b: "b \<in> tableau_nonbasics (exchange_basis S b e)" by simp
  have nb: "b \<notin> tableau_basics (exchange_basis S b e)" using facts by simp
  show "tableau_rows_satisfied (pivot_and_set S b e t)"
    unfolding pivot_and_set_def
    using update_nonbasic_preserves_rows[OF b exchange_rows_satisfied[OF p sup rows]] .
  show "tableau_models (pivot_and_set S b e t) = tableau_models S"
    using exchange_models[OF p sup]
    by (simp add: pivot_and_set_def update_nonbasic_assignment_def tableau_models_def)
  show "tableau_candidate (pivot_and_set S b e t) b = t"
    using nb by (simp add: pivot_and_set_def update_nonbasic_assignment_def tableau_candidate_def)
  assume bounds: "tableau_nonbasic_bounds_satisfied S"
    and old: "tableau_lower S b \<le> tableau_basic_value S b" "tableau_basic_value S b \<le> tableau_upper S b"
    and new: "tableau_lower S b \<le> t" "t \<le> tableau_upper S b"
  show "tableau_nonbasic_bounds_satisfied (pivot_and_set S b e t)"
    unfolding pivot_and_set_def
    using update_nonbasic_preserves_bounds[OF b exchange_nonbasic_bounds[OF bounds old]] new
    by simp
qed

end
