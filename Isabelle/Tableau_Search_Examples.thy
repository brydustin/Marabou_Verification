theory Tableau_Search_Examples
  imports Tableau_Search Tableau_Relu_Split_Examples
begin

text \<open>
  Computations by code_simp; no evaluation oracle is used. Kernel-checked
  evaluation of the closure-based state is slow (TABLEAU_SEARCH.md), so the
  searches with splits start from the auxiliary basis
  (ONLY_AUX_INITIAL_BASIS), which is cheaper to evaluate than Marabou's
  pivoted default basis, and allow up to 50 simplex steps per iteration. The
  soundness theorems cover both starts and every step count.
\<close>

section \<open>Backtracking to refute a query\<close>

text \<open>
  split_query (Tableau_Relu_Split_Examples) needs a split. The search splits
  its ReLU with the active child first and refutes that child. It backtracks
  to the inactive child, whose bound x1 \<le> 0 crosses x1 \<ge> 1/4, refutes it
  too and finds the stack empty: three iterations.
\<close>

lemma split_query_search: "is_search_unsat (solve_search_aux_basis 3 50 3 split_query)"
  by code_simp

theorem split_query_unsatisfiable_by_search: "unsatisfiable split_query"
  using solve_search_verdicts(4)[OF split_query_search] .

section \<open>Backtracking to a solution\<close>

text \<open>
  ReLU x0 \<rightarrow> x1 with auxiliary x2, x1 - x0/2 = 1/2 and x0 \<le> 1/4. The active
  phase would need x0 = x1 = 1 > 1/4; the inactive phase has the solution
  x0 = -1, x1 = 0, x2 = 1. The linear solution violates the ReLU, the active
  child is refuted, and after backtracking the inactive child yields that
  solution.
\<close>

definition backtrack_sat_query :: query where
  "backtrack_sat_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0,
                      LinearEq (Linexpr 0 [(1, 1), (-1 / 2, 0)]) (1 / 2)],
      query_bounds = [Lower 0 (-1), Upper 0 (1 / 4), Lower 1 0, Upper 1 1, Lower 2 0, Upper 2 2],
      relu_atoms = [ReLU 0 1]\<rparr>"

lemma backtrack_sat_search:
  "case solve_search_aux_basis 3 50 3 backtrack_sat_query of
     Search_Sat v \<Rightarrow> [v 0, v 1, v 2] = [-1, 0, 1]
   | _ \<Rightarrow> False"
  by code_simp

theorem backtrack_sat_query_solution:
  "\<exists>v. solve_search_aux_basis 3 50 3 backtrack_sat_query = Search_Sat v \<and>
       satisfies_query v backtrack_sat_query \<and> v 0 = -1 \<and> v 1 = 0 \<and> v 2 = 1"
proof (cases "solve_search_aux_basis 3 50 3 backtrack_sat_query")
  case (Search_Sat v)
  then show ?thesis using backtrack_sat_search solve_search_aux_basis_sat[OF Search_Sat] by simp
next
  case Search_Unsat
  then show ?thesis using backtrack_sat_search by simp
next
  case Search_Unknown
  then show ?thesis using backtrack_sat_search by simp
qed

section \<open>Marabou's default basis\<close>

text \<open>
  With the native initial basis, sat_relu_query is solved without a split:
  one simplex step reaches a point that satisfies the ReLU.
\<close>

lemma sat_relu_query_search: "is_search_sat (solve_search 2 1 3 sat_relu_query)"
  by code_simp

section \<open>Restoration is necessary\<close>

text \<open>
  Applying the alternative on the first child's bounds, instead of the
  restored parent bounds, loses solutions. On sat_relu_query, the active
  child sets x0 \<ge> 0. The point x0 = -1/2, x1 = 0, x2 = 1/2 is a
  ReLU-respecting root solution in the inactive child, but the inactive
  split applied over the active child's bounds excludes it. So that branch
  does not represent the inactive child, whereas restore_branch_sound shows
  that the restored one does.
\<close>

definition sat_root :: tableau_state where
  "sat_root = initial_tableau 3 sat_relu_query"

definition unrestored :: branch where
  "unrestored =
     apply_split (native_inactive_split split_relu)
       (apply_split (native_active_split split_relu) (root_branch sat_root))"

definition missed_point :: valuation where
  "missed_point = extend_aux 3 sat_relu_query (\<lambda>x. if x = 0 then -1 / 2 else if x = 2 then 1 / 2 else 0)"

lemma unrestored_keeps_child_bound:
  "tableau_lower (store_tableau (branch_store unrestored)) 0 = 0"
  "0 \<in> carrier (store_tableau (branch_store unrestored))"
  "engine_ready 3 sat_relu_query"
  by code_simp+

lemma missed_point_facts:
  shows "missed_point \<in> tableau_bounded_models sat_root"
    and "missed_point \<in> relu_solutions [split_relu]"
    and "missed_point \<in> decision_models (native_inactive_split split_relu)"
    and "missed_point \<notin> tableau_bounded_models (store_tableau (branch_store unrestored))"
proof -
  let ?w = "\<lambda>x::var. if x = 0 then -1 / 2 else if x = 2 then 1 / 2 else (0 :: real)"
  have q: "satisfies_query ?w sat_relu_query"
    by (simp add: satisfies_query_def sat_relu_query_def satisfies_relu_def relu_def)
  have vals: "missed_point 0 = -1 / 2" "missed_point 1 = 0"
    by (simp_all add: missed_point_def extend_aux_def)
  show "missed_point \<in> tableau_bounded_models sat_root"
    using query_model_extends[OF unrestored_keeps_child_bound(3)] q
    unfolding satisfies_query_def sat_root_def missed_point_def by blast
  show "missed_point \<in> relu_solutions [split_relu]"
    using vals by (simp add: relu_solutions_def relu_holds_def split_relu_def satisfies_relu_def relu_def)
  show "missed_point \<in> decision_models (native_inactive_split split_relu)"
    using vals by (simp add: decision_models_splits split_relu_def)
  show "missed_point \<notin> tableau_bounded_models (store_tableau (branch_store unrestored))"
    using vals unrestored_keeps_child_bound(1,2) unfolding tableau_bounded_models_def by force
qed

theorem unrestored_alternative_breaks_branch:
  "\<not> relu_branch_of sat_root [split_relu]
       (unrestored\<lparr>branch_decisions := native_inactive_split split_relu\<rparr>)"
  using missed_point_facts unfolding relu_branch_of_def by auto

end
