theory Tableau_Pivot_Examples
  imports Tableau_Simplex_Run
begin

text \<open>
  Rows x2 = x0 + x1 and x3 = x0 - x1 with x0, x1 in [0, 1], x2 in [3/2, 2] and
  x3 in [l, 1], starting from x0 = x1 = 0. For l = 1/2 the unique solution is
  x0 = 1, x1 = 1/2; for l = 3/4 there is none (2 x0 \<ge> 9/4).
\<close>

definition example_rows :: "var \<Rightarrow> linexpr" where
  "example_rows x =
     (if x = 2 then Linexpr 0 [(1, 0), (1, 1)]
      else if x = 3 then Linexpr 0 [(1, 0), (-1, 1)]
      else Linexpr 0 [])"

definition example_state :: "real \<Rightarrow> tableau_state" where
  "example_state l =
     \<lparr>tableau_basics = {2, 3}, tableau_nonbasics = {0, 1},
      tableau_rows = example_rows,
      tableau_lower = (\<lambda>x. if x = 2 then 3 / 2 else if x = 3 then l else 0),
      tableau_upper = (\<lambda>x. if x = 2 then 2 else 1),
      tableau_nonbasic_value = (\<lambda>x. 0),
      tableau_basic_value = (\<lambda>x. 0)\<rparr>"

definition example_equations :: "linear_constraint list" where
  "example_equations =
     [LinearEq (Linexpr 0 [(1, 2), (-1, 0), (-1, 1)]) 0,
      LinearEq (Linexpr 0 [(1, 3), (-1, 0), (1, 1)]) 0]"

lemma example_invariant:
  assumes "l \<le> 1"
  shows "simplex_invariant (example_state l) [2, 3] [0, 1]"
  using assms
  by (auto simp: simplex_invariant_def example_state_def example_rows_def
      tableau_rows_supported_def tableau_rows_satisfied_def
      tableau_nonbasic_bounds_satisfied_def tableau_bounds_ordered_def)

lemma example_represents: "tableau_represents (example_state l) example_equations"
  by (auto simp: tableau_represents_def tableau_models_def example_state_def
      example_rows_def example_equations_def algebra_simps)

section \<open>One exchange\<close>

text \<open>Pivoting x3 out and x0 in solves x3's row for x0 and substitutes it.\<close>

lemma example_exchange_rows:
  "tableau_rows (exchange_basis (example_state l) 3 0) 0 = Linexpr 0 [(1, 3), (1, 1)]"
  "tableau_rows (exchange_basis (example_state l) 3 0) 2 =
     Linexpr 0 [(1, 1), (1, 3), (1, 1)]"
  by (simp_all add: exchange_basis_def exchange_rows_def example_state_def example_rows_def
      solve_row_def substitute_row_def row_coefficient_def drop_var_def scale_terms_def)

lemma example_exchange_admissible: "pivot_admissible (example_state l) 3 0"
  by (simp add: pivot_admissible_def example_state_def example_rows_def row_coefficient_def)

lemma example_exchange_models:
  "tableau_models (exchange_basis (example_state l) 3 0) = tableau_models (example_state l)"
  using exchange_models[OF example_exchange_admissible]
    example_invariant[of 0] unfolding simplex_invariant_def
  by (simp add: example_state_def tableau_rows_supported_def)

section \<open>The Harris choice and the native arrays\<close>

lemma example_first_choice:
  "first_eligible (example_state (1 / 2)) [0, 1] = Some (0, Increase)"
  "exact_harris_ratio_test (example_state (1 / 2)) 0 Increase [2, 3] = Leaving 3 (1 / 2)"
  by code_simp+

definition example_layout :: tableau_layout where
  "example_layout =
     \<lparr>basic_index = [2, 3], nonbasic_index = [0, 1],
      basic_assignment = [0, 0], nonbasic_assignment = [0, 0]\<rparr>"

lemma example_layout_abstracts: "layout_abstracts example_layout (example_state l)"
  by (auto simp: layout_abstracts_def layout_valid_def example_layout_def example_state_def
      less_Suc_eq nth_Cons')

text \<open>
  updateAssignmentForPivot with the native formulas: the change column is
  [-1, -1], delta = (1/2 - 0) / 1 and the leaving target is x3's lower bound.
\<close>

lemma example_native_pivot:
  "native_pivot example_layout 1 0
     (change_column (example_state (1 / 2)) 0 [2, 3]) (1 / 2) (1 / 2) =
   \<lparr>basic_index = [2, 0], nonbasic_index = [3, 1],
    basic_assignment = [1 / 2, 1 / 2], nonbasic_assignment = [1 / 2, 0]\<rparr>"
  by code_simp

lemma example_native_pivot_refines:
  "layout_abstracts
     \<lparr>basic_index = [2, 0], nonbasic_index = [3, 1],
      basic_assignment = [1 / 2, 1 / 2], nonbasic_assignment = [1 / 2, 0]\<rparr>
     (apply_choice (example_state (1 / 2)) 0 Increase (Leaving 3 (1 / 2)))"
proof -
  have ratio: "basic_ratio (example_state (1 / 2)) (nonbasic_index example_layout ! 0) Increase
                 (basic_index example_layout ! 1) = Some (1 / 2)"
    by code_simp
  have target: "native_leaving_target (example_state (1 / 2)) 3
                  (0 < step_rate (example_state (1 / 2)) 0 Increase 3) = 1 / 2"
    by code_simp
  have delta: "(1 / 2 - tableau_basic_value (example_state (1 / 2)) 3) /
                 row_coefficient (tableau_rows (example_state (1 / 2)) 3) 0 = (1 / 2 :: real)"
    by code_simp
  show ?thesis
    using native_simplex_pivot_refines[OF example_layout_abstracts[of "1 / 2"], of 1 0 Increase "1 / 2"]
      ratio target delta example_native_pivot
    by (simp add: example_layout_def)
qed

section \<open>Complete runs\<close>

definition feasible_run where
  "feasible_run = simplex_run 5 (example_state (1 / 2)) [2, 3] [0, 1]"

definition infeasible_run where
  "infeasible_run = simplex_run 6 (example_state (3 / 4)) [2, 3] [0, 1]"

text \<open>
  The feasible run: x3 leaves (ratio 1/2), x3 flips to its upper bound, x0
  leaves in a degenerate pivot, x3 flips back to its lower bound. The final
  basis is {x2, x1}.
\<close>

lemma feasible_run_result:
  "fst feasible_run = Feasible"
  "snd (snd feasible_run) = ([2, 1], [3, 0])"
  "map (tableau_candidate (fst (snd feasible_run))) [0, 1, 2, 3] = [1, 1 / 2, 3 / 2, 1 / 2]"
  unfolding feasible_run_def by code_simp+

theorem feasible_run_solution:
  "(\<forall>c\<in>set example_equations. satisfies_linear (tableau_candidate (fst (snd feasible_run))) c) \<and>
   (\<forall>x\<in>{2, 3, 0, 1}.
      tableau_lower (example_state (1 / 2)) x \<le> tableau_candidate (fst (snd feasible_run)) x \<and>
      tableau_candidate (fst (snd feasible_run)) x \<le> tableau_upper (example_state (1 / 2)) x)"
proof -
  obtain r S' bs' ns' where run: "feasible_run = (r, S', bs', ns')"
    by (cases feasible_run) auto
  have r: "r = Feasible" using feasible_run_result(1) by (simp add: run)
  have "simplex_run 5 (example_state (1 / 2)) [2, 3] [0, 1] = (r, S', bs', ns')"
    using run by (simp add: feasible_run_def)
  from simplex_run_represented(1)[OF example_invariant example_represents this r]
  show ?thesis by (simp add: run example_state_def)
qed

lemma infeasible_run_result: "fst infeasible_run = Infeasible"
  unfolding infeasible_run_def by code_simp

theorem example_infeasible:
  "\<not> (\<exists>v :: valuation. v 2 = v 0 + v 1 \<and> v 3 = v 0 - v 1 \<and>
           0 \<le> v 0 \<and> v 0 \<le> 1 \<and> 0 \<le> v 1 \<and> v 1 \<le> 1 \<and>
           3 / 2 \<le> v 2 \<and> v 2 \<le> 2 \<and> 3 / 4 \<le> v 3 \<and> v 3 \<le> 1)"
proof -
  obtain r S' bs' ns' where run: "infeasible_run = (r, S', bs', ns')"
    by (cases infeasible_run) auto
  have r: "r = Infeasible" using infeasible_run_result by (simp add: run)
  have "simplex_run 6 (example_state (3 / 4)) [2, 3] [0, 1] = (r, S', bs', ns')"
    using run by (simp add: infeasible_run_def)
  from simplex_run_sound(4)[OF example_invariant this r]
  have "tableau_bounded_models (example_state (3 / 4)) = {}" by simp
  then show ?thesis
    by (auto simp: tableau_bounded_models_def tableau_models_def example_state_def
        example_rows_def)
qed

section \<open>Rejections\<close>

text \<open>A zero pivot element is not admissible, and exchanging on it changes the solutions.\<close>

definition zero_pivot_state :: tableau_state where
  "zero_pivot_state =
     \<lparr>tableau_basics = {2}, tableau_nonbasics = {0, 1},
      tableau_rows = (\<lambda>x. Linexpr 0 [(1, 0), (1, 1), (-1, 1)]),
      tableau_lower = (\<lambda>x. 0), tableau_upper = (\<lambda>x. 1),
      tableau_nonbasic_value = (\<lambda>x. 0), tableau_basic_value = (\<lambda>x. 0)\<rparr>"

lemma zero_pivot_rejected:
  "\<not> pivot_admissible zero_pivot_state 2 1"
  "tableau_models (exchange_basis zero_pivot_state 2 1) \<noteq> tableau_models zero_pivot_state"
proof -
  show "\<not> pivot_admissible zero_pivot_state 2 1"
    by (simp add: pivot_admissible_def zero_pivot_state_def row_coefficient_def)
  let ?v = "(\<lambda>x. 0)(1 := 5) :: valuation"
  have "?v \<in> tableau_models zero_pivot_state"
    by (simp add: tableau_models_def zero_pivot_state_def)
  moreover have "?v \<notin> tableau_models (exchange_basis zero_pivot_state 2 1)"
    by (simp add: tableau_models_def zero_pivot_state_def exchange_basis_def exchange_rows_def
        solve_row_def row_coefficient_def drop_var_def scale_terms_def)
  ultimately show "tableau_models (exchange_basis zero_pivot_state 2 1) \<noteq>
                   tableau_models zero_pivot_state"
    by blast
qed

text \<open>A step past the minimal ratio pushes an in-bounds basic out of bounds.\<close>

definition overstep_state :: tableau_state where
  "overstep_state =
     \<lparr>tableau_basics = {1}, tableau_nonbasics = {0},
      tableau_rows = (\<lambda>x. Linexpr 0 [(1, 0)]),
      tableau_lower = (\<lambda>x. 0), tableau_upper = (\<lambda>x. if x = 0 then 2 else 1),
      tableau_nonbasic_value = (\<lambda>x. 0), tableau_basic_value = (\<lambda>x. 0)\<rparr>"

lemma overstep_rejected:
  "exact_harris_ratio_test overstep_state 0 Increase [1] = Leaving 1 1"
  "\<not> step_within_ratios overstep_state 0 Increase 2"
  "status_of overstep_state 1 = Between"
  "tableau_basic_value (move_entering overstep_state 0 Increase 2) 1 = 2"
proof -
  have ratio: "basic_ratio overstep_state 0 Increase 1 = Some 1"
    by code_simp
  show "exact_harris_ratio_test overstep_state 0 Increase [1] = Leaving 1 1"
    "status_of overstep_state 1 = Between"
    "tableau_basic_value (move_entering overstep_state 0 Increase 2) 1 = 2"
    by code_simp+
  show "\<not> step_within_ratios overstep_state 0 Increase 2"
    using ratio by (auto simp: step_within_ratios_def overstep_state_def)
qed

end
