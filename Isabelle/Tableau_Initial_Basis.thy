theory Tableau_Initial_Basis
  imports Tableau_Initialization
begin

text \<open>
  The default initial basis of Engine::processInputQuery.
  ONLY_AUX_INITIAL_BASIS is false (GlobalConfiguration.cpp:98), so
  Engine::selectInitialVariablesForBasis (Engine.cpp:1115-1288) permutes the
  constraint matrix to find original columns forming a lower-triangular block:
  it repeatedly diagonalizes a singleton row, and otherwise excludes the
  densest remaining column. Those columns join the basis;
  augmentInitialBasisIfNeeded (1316-1328) adds the auxiliary variables of the
  remaining rows. Tableau::initializeTableau (Tableau.cpp:336-374) then numbers
  the basics in that order and the nonbasics in increasing order, puts the
  nonbasics at their lower bounds and computes the basics.

  Here the selection is an exact copy of that loop, with FloatUtils::isZero
  replaced by an exact test. The selected basis is reached from the
  auxiliary basis of Tableau_Initialization by exchanges, each checked for a
  nonzero pivot element. Soundness does not depend on the selection: a
  failed check or a mismatched index list is reported, never trusted.
\<close>

section \<open>Checked pivot sequences and a fresh assignment\<close>

fun pivot_sequence :: "tableau_state \<Rightarrow> (var \<times> var) list \<Rightarrow> tableau_state option" where
  "pivot_sequence S [] = Some S"
| "pivot_sequence S ((b, e) # ps) =
     (if pivot_admissible S b e then pivot_sequence (exchange_basis S b e) ps else None)"

lemma pivot_sequence_sound:
  assumes "pivot_sequence S ps = Some S'" "tableau_rows_supported S"
  shows "tableau_rows_supported S'"
    and "tableau_bounded_models S' = tableau_bounded_models S"
    and "tableau_lower S' = tableau_lower S" "tableau_upper S' = tableau_upper S"
    and "tableau_basics S' \<union> tableau_nonbasics S' = tableau_basics S \<union> tableau_nonbasics S"
  using assms
proof (induction S ps rule: pivot_sequence.induct)
  case (1 S)
  {
    case 1 then show ?case by simp
  next
    case 2 then show ?case by simp
  next
    case 3 then show ?case by simp
  next
    case 4 then show ?case by simp
  next
    case 5 then show ?case by simp
  }
next
  case (2 S b e ps)
  have all: "tableau_rows_supported S' \<and> tableau_bounded_models S' = tableau_bounded_models S \<and>
      tableau_lower S' = tableau_lower S \<and> tableau_upper S' = tableau_upper S \<and>
      tableau_basics S' \<union> tableau_nonbasics S' = tableau_basics S \<union> tableau_nonbasics S"
    if run: "pivot_sequence S ((b, e) # ps) = Some S'" and sup: "tableau_rows_supported S"
  proof -
    have p: "pivot_admissible S b e" and rest: "pivot_sequence (exchange_basis S b e) ps = Some S'"
      using run by (auto split: if_splits)
    have sup1: "tableau_rows_supported (exchange_basis S b e)"
      using exchange_rows_supported[OF p sup] .
    note IH = "2.IH"[OF p rest sup1]
    show ?thesis
      using IH exchange_bounded_models[OF p sup] exchange_carrier[OF p] by simp
  qed
  {
    case 1 then show ?case using all by blast
  next
    case 2 then show ?case using all by blast
  next
    case 3 then show ?case using all by blast
  next
    case 4 then show ?case using all by blast
  next
    case 5 then show ?case using all by blast
  }
qed

text \<open>Nonbasics at their lower bounds, basics solved from the rows.\<close>

definition reset_assignment :: "tableau_state \<Rightarrow> tableau_state" where
  "reset_assignment S = S\<lparr>
     tableau_nonbasic_value := tableau_lower S,
     tableau_basic_value := (\<lambda>x. eval_linexpr (tableau_lower S) (tableau_rows S x))\<rparr>"

definition lists_match :: "tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "lists_match S bs ns \<longleftrightarrow>
     distinct bs \<and> distinct ns \<and> set bs = tableau_basics S \<and> set ns = tableau_nonbasics S"

lemma reset_assignment_simps [simp]:
  "tableau_basics (reset_assignment S) = tableau_basics S"
  "tableau_nonbasics (reset_assignment S) = tableau_nonbasics S"
  "tableau_rows (reset_assignment S) = tableau_rows S"
  "tableau_lower (reset_assignment S) = tableau_lower S"
  "tableau_upper (reset_assignment S) = tableau_upper S"
  "tableau_bounded_models (reset_assignment S) = tableau_bounded_models S"
  by (simp_all add: reset_assignment_def tableau_bounded_models_def tableau_models_def)

lemma reset_assignment_invariant:
  assumes sup: "tableau_rows_supported S" and ord: "tableau_bounds_ordered S"
      and lists: "lists_match S bs ns"
  shows "simplex_invariant (reset_assignment S) bs ns"
proof -
  have rows: "tableau_rows_satisfied (reset_assignment S)"
    by (simp add: tableau_rows_satisfied_def reset_assignment_def)
  have nb: "tableau_nonbasic_bounds_satisfied (reset_assignment S)"
    using ord
    by (auto simp: tableau_nonbasic_bounds_satisfied_def reset_assignment_def
        tableau_bounds_ordered_def)
  show ?thesis
    using sup ord lists rows nb
    by (simp add: simplex_invariant_def lists_match_def tableau_rows_supported_def
        tableau_bounds_ordered_def)
qed

section \<open>The native triangular selection\<close>

text \<open>
  The search state mirrors the native arrays: nonzero counts per row and
  column position, the row and column orderings, and the numbers of excluded
  columns and diagonalized rows. Counts move with their positions, as in the
  native swaps.
\<close>

record basis_search =
  row_nnz :: "nat list"
  col_nnz :: "nat list"
  row_order :: "nat list"
  col_order :: "nat list"
  excluded :: nat
  triangular :: nat

definition swap :: "'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list" where
  "swap xs i j = xs[i := xs ! j, j := xs ! i]"

definition equation_coefficient :: "query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> real" where
  "equation_coefficient Q i j = linexpr_coefficient (aux_terms (linear_atoms Q ! i)) j"

definition initial_search :: "nat \<Rightarrow> query \<Rightarrow> basis_search" where
  "initial_search n Q =
     (let m = length (linear_atoms Q); A = equation_coefficient Q in
      \<lparr>row_nnz = map (\<lambda>i. length (filter (\<lambda>j. A i j \<noteq> 0) [0..<n])) [0..<m],
       col_nnz = map (\<lambda>j. length (filter (\<lambda>i. A i j \<noteq> 0) [0..<m])) [0..<n],
       row_order = [0..<m], col_order = [0..<n], excluded = 0, triangular = 0\<rparr>)"

text \<open>The first position of maximal count in [t, hi), as in Engine.cpp:1240-1251.\<close>

definition densest :: "nat list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "densest cn t hi =
     fst (fold (\<lambda>i (best, d). if d < cn ! i then (i, cn ! i) else (best, d)) [t..<hi] (t, cn ! t))"

definition search_step :: "nat \<Rightarrow> query \<Rightarrow> basis_search \<Rightarrow> basis_search" where
  "search_step n Q st =
     (let m = length (linear_atoms Q); A = equation_coefficient Q;
          t = triangular st; hi = n - excluded st in
      case find (\<lambda>i. row_nnz st ! i = 1) [t..<m] of
        Some r \<Rightarrow>
          (let ro = swap (row_order st) r t; rn = swap (row_nnz st) r t in
           case find (\<lambda>i. A (ro ! t) (col_order st ! i) \<noteq> 0) [t..<hi] of
             Some c \<Rightarrow>
               (let co = swap (col_order st) c t; cn = swap (col_nnz st) c t in
                st\<lparr>row_nnz := map (\<lambda>i. if t < i \<and> A (ro ! i) (co ! t) \<noteq> 0
                                       then rn ! i - 1 else rn ! i) [0..<m],
                   col_nnz := cn, row_order := ro, col_order := co, triangular := t + 1\<rparr>)
           | None \<Rightarrow> st\<lparr>excluded := excluded st + 1\<rparr>)
      | None \<Rightarrow>
          (let c = densest (col_nnz st) t hi; col = col_order st ! c in
           st\<lparr>row_nnz := map (\<lambda>i. if t \<le> i \<and> A (row_order st ! i) col \<noteq> 0
                                  then row_nnz st ! i - 1 else row_nnz st ! i) [0..<m],
              col_nnz := (col_nnz st)[c := col_nnz st ! (hi - 1)],
              col_order := (col_order st)[c := col_order st ! (hi - 1)],
              excluded := excluded st + 1\<rparr>))"

text \<open>
  The native loop runs while excluded + triangular < n, and every step raises
  that sum by one (the unreachable no-column case also does), so n steps
  suffice.
\<close>

fun search_loop :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> basis_search \<Rightarrow> basis_search" where
  "search_loop 0 n Q st = st"
| "search_loop (Suc k) n Q st =
     (if excluded st + triangular st < n then search_loop k n Q (search_step n Q st) else st)"

definition select_initial_basis :: "nat \<Rightarrow> query \<Rightarrow> basis_search" where
  "select_initial_basis n Q =
     (if length (linear_atoms Q) = 0 \<or> n = 0 then initial_search n Q
      else search_loop n n Q (initial_search n Q))"

text \<open>
  Pivot pairs (auxiliary of a diagonalized row, its column) and the native
  basic order: diagonalized columns, then the auxiliaries of the remaining
  rows in their final order.
\<close>

definition basis_pivots :: "nat \<Rightarrow> basis_search \<Rightarrow> (var \<times> var) list" where
  "basis_pivots n st =
     zip (map (\<lambda>r. n + r) (take (triangular st) (row_order st))) (take (triangular st) (col_order st))"

definition basis_order :: "nat \<Rightarrow> basis_search \<Rightarrow> var list" where
  "basis_order n st =
     take (triangular st) (col_order st) @ map (\<lambda>r. n + r) (drop (triangular st) (row_order st))"

definition native_initial_tableau ::
  "nat \<Rightarrow> query \<Rightarrow> (tableau_state \<times> var list \<times> var list) option" where
  "native_initial_tableau n Q =
     (let st = select_initial_basis n Q; bs = basis_order n st;
          ns = filter (\<lambda>x. x \<notin> set bs) [0..<n + length (linear_atoms Q)] in
      case pivot_sequence (initial_tableau n Q) (basis_pivots n st) of
        None \<Rightarrow> None
      | Some S \<Rightarrow> if lists_match S bs ns then Some (reset_assignment S, bs, ns) else None)"

theorem native_initial_tableau_sound:
  assumes ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
      and init: "native_initial_tableau n Q = Some (S, bs, ns)"
  shows "simplex_invariant S bs ns"
    and "tableau_bounded_models S = tableau_bounded_models (initial_tableau n Q)"
proof -
  let ?st = "select_initial_basis n Q"
  obtain S0 where seq: "pivot_sequence (initial_tableau n Q) (basis_pivots n ?st) = Some S0"
    and match: "lists_match S0 bs ns" and S: "S = reset_assignment S0"
    using init by (auto simp: native_initial_tableau_def Let_def split: option.splits if_splits)
  have inv0: "simplex_invariant (initial_tableau n Q) (initial_basics n Q) [0..<n]"
    using initial_tableau_invariant[OF ready consistent] .
  have sup0: "tableau_rows_supported (initial_tableau n Q)"
    and ord0: "tableau_bounds_ordered (initial_tableau n Q)"
    using inv0 unfolding simplex_invariant_def by auto
  note seqs = pivot_sequence_sound[OF seq sup0]
  have ord: "tableau_bounds_ordered S0"
    using ord0 seqs(3,4,5) unfolding tableau_bounds_ordered_def by simp
  show "simplex_invariant S bs ns"
    using reset_assignment_invariant[OF seqs(1) ord match] S by simp
  show "tableau_bounded_models S = tableau_bounded_models (initial_tableau n Q)"
    using seqs(2) S by simp
qed

section \<open>Solving from the native initial basis\<close>

definition solve_linear_part_native :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> linear_result" where
  "solve_linear_part_native fuel n Q =
     (if \<not> engine_ready n Q then Simplex_Unknown
      else if \<not> bounds_consistent n Q then Simplex_Unsat
      else (case native_initial_tableau n Q of
              None \<Rightarrow> Simplex_Unknown
            | Some (S, bs, ns) \<Rightarrow>
                (case simplex_run fuel S bs ns of
                   (Feasible, S', _) \<Rightarrow> Simplex_Feasible (tableau_candidate S')
                 | (Infeasible, _) \<Rightarrow> Simplex_Unsat
                 | (Out_Of_Fuel, _) \<Rightarrow> Simplex_Unknown)))"

theorem solve_linear_part_native_unsat:
  assumes "solve_linear_part_native fuel n Q = Simplex_Unsat"
  shows "unsatisfiable Q"
proof -
  have ready: "engine_ready n Q"
    using assms by (auto simp: solve_linear_part_native_def split: if_splits)
  show ?thesis
  proof (cases "bounds_consistent n Q")
    case False
    then show ?thesis using inconsistent_bounds_unsatisfiable[OF ready] by blast
  next
    case True
    obtain S bs ns where init: "native_initial_tableau n Q = Some (S, bs, ns)"
      using assms ready True
      by (auto simp: solve_linear_part_native_def split: option.splits)
    obtain r S' bs' ns' where run: "simplex_run fuel S bs ns = (r, S', bs', ns')"
      by (cases "simplex_run fuel S bs ns") auto
    have "r = Infeasible"
      using assms ready True init run
      by (cases r) (simp_all add: solve_linear_part_native_def)
    then have "tableau_bounded_models S = {}"
      using simplex_run_sound(4)[OF native_initial_tableau_sound(1)[OF ready True init] run] by blast
    then show ?thesis
      using native_initial_tableau_sound(2)[OF ready True init] initial_empty_unsatisfiable[OF ready]
      by simp
  qed
qed

theorem solve_linear_part_native_feasible:
  assumes "solve_linear_part_native fuel n Q = Simplex_Feasible v"
  shows "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
    and "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
proof -
  have ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
    using assms by (auto simp: solve_linear_part_native_def split: if_splits)
  obtain S bs ns where init: "native_initial_tableau n Q = Some (S, bs, ns)"
    using assms ready consistent
    by (auto simp: solve_linear_part_native_def split: option.splits)
  obtain r S' bs' ns' where run: "simplex_run fuel S bs ns = (r, S', bs', ns')"
    by (cases "simplex_run fuel S bs ns") auto
  have r: "r = Feasible" and v: "v = tableau_candidate S'"
    using assms ready consistent init run
    by (cases r; simp add: solve_linear_part_native_def)+
  have "v \<in> tableau_bounded_models (initial_tableau n Q)"
    using simplex_run_sound(3)[OF native_initial_tableau_sound(1)[OF ready consistent init] run r]
      native_initial_tableau_sound(2)[OF ready consistent init] v by simp
  then show "\<forall>c\<in>set (linear_atoms Q). satisfies_linear v c"
    "\<forall>b\<in>set (query_bounds Q). satisfies_bound v b"
    using bounded_model_satisfies_linear_part[OF ready] by blast+
qed

theorem solve_linear_part_native_model:
  assumes "solve_linear_part_native fuel n Q = Simplex_Feasible v"
      and "list_all (satisfies_relu_constraint v) (relu_atoms Q)"
  shows "satisfies_query v Q"
  using solve_linear_part_native_feasible[OF assms(1)] assms(2)
  unfolding satisfies_query_def list_all_iff by blast

section \<open>Solving a query\<close>

text \<open>The number of variables, as the file workflow computes it: one more than the largest index.\<close>

definition query_width :: "query \<Rightarrow> nat" where
  "query_width Q =
     Suc (fold max (map snd (concat (map aux_terms (linear_atoms Q))) @
                    map bound_variable (query_bounds Q) @
                    concat (map (\<lambda>r. case r of ReLU x y \<Rightarrow> [x, y]) (relu_atoms Q))) 0)"

definition solve_query :: "nat \<Rightarrow> query \<Rightarrow> linear_result" where
  "solve_query fuel Q = solve_linear_part_native fuel (query_width Q) Q"

theorem solve_query_unsat:
  "solve_query fuel Q = Simplex_Unsat \<Longrightarrow> unsatisfiable Q"
  unfolding solve_query_def by (rule solve_linear_part_native_unsat)

theorem solve_query_model:
  "solve_query fuel Q = Simplex_Feasible v \<Longrightarrow>
     list_all (satisfies_relu_constraint v) (relu_atoms Q) \<Longrightarrow> satisfies_query v Q"
  unfolding solve_query_def by (rule solve_linear_part_native_model)

corollary solve_query_sat:
  "solve_query fuel Q = Simplex_Feasible v \<Longrightarrow> relu_atoms Q = [] \<Longrightarrow> satisfiable Q"
  using solve_query_model unfolding satisfiable_def by fastforce

export_code solve_query solve_linear_part_native select_initial_basis checking SML

end
