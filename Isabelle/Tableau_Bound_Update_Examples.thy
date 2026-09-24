theory Tableau_Bound_Update_Examples
  imports Tableau_Bound_Update Tableau_Pivot_Examples Imported_Marabou_Example_Linear_Unsat
begin

text \<open>All computations by code_simp; no evaluation oracle is used.\<close>

section \<open>A file refuted by row bound tightening\<close>

text \<open>
  examples/linear_unsat.mqx: the auxiliary row x2 = x0 - x1 has x2 fixed to 0,
  while x0 \<le> 1/4 and x1 \<ge> 1/2. The row gives x2 \<le> -1/4, which crosses the
  lower bound 0: a recorded conflict at the root, with no decision, no simplex
  step and no Marabou certificate.
\<close>

definition row_refutation :: "rat_query \<Rightarrow> branch" where
  "row_refutation Q =
     apply_rules (row_rules (initial_tableau 2 (embed_query Q)) 2)
       (root_branch (initial_tableau 2 (embed_query Q)))"

lemma linear_unsat_row_conflict:
  "map_option (\<lambda>Q. (engine_ready 2 (embed_query Q), bounds_consistent 2 (embed_query Q),
                    first_conflict (branch_store (row_refutation Q))))
     (decode_query Imported_Marabou_Example_Linear_Unsat.query_file) =
   Some (True, True, Some (2, Upper_Side, - 1 / 4))"
  by code_simp

theorem linear_unsat_file_unsatisfiable_by_bounds:
  assumes Q: "decode_query Imported_Marabou_Example_Linear_Unsat.query_file = Some Q"
  shows "unsatisfiable (embed_query Q)"
proof -
  let ?S = "initial_tableau 2 (embed_query Q)"
  have facts: "engine_ready 2 (embed_query Q)" "bounds_consistent 2 (embed_query Q)"
    "first_conflict (branch_store (row_refutation Q)) = Some (2, Upper_Side, - 1 / 4)"
    using linear_unsat_row_conflict Q by simp_all
  have inv: "simplex_invariant ?S (initial_basics 2 (embed_query Q)) [0..<2]"
    using initial_tableau_invariant[OF facts(1,2)] .
  have sup: "tableau_rows_supported (store_tableau (branch_store (root_branch ?S)))"
    using inv by (simp add: root_branch_def simplex_invariant_def)
  note sound = apply_rules_sound[OF root_branch_of sup root_branch_conflicts[OF inv],
      of "row_rules ?S 2"]
  show ?thesis
  proof (rule root_conflict_unsatisfiable[OF facts(1)])
    show "branch_of ?S (row_refutation Q)" "branch_decisions (row_refutation Q) = []"
      "conflict_sound (branch_store (row_refutation Q))"
      "first_conflict (branch_store (row_refutation Q)) \<noteq> None"
      using sound facts(3) by (simp_all add: row_refutation_def root_branch_def)
  qed
qed

section \<open>Decisions versus derived bounds\<close>

text \<open>
  The rows x2 = x0 + x1 and x3 = x0 - x1 of Tableau_Pivot_Examples with
  x3 \<ge> 1/4. The root has solutions with x0 < 1, so x0 \<ge> 1 is a split
  decision, not an entailed fact.
\<close>

abbreviation split_root :: tableau_state where
  "split_root \<equiv> example_state (1 / 4)"

definition decided :: branch where
  "decided = apply_decision Lower_Side 0 1 (root_branch split_root)"

definition decided_twice :: branch where
  "decided_twice = apply_rules (row_rules (store_tableau (branch_store
     (apply_decision Lower_Side 1 1 decided))) 3) (apply_decision Lower_Side 1 1 decided)"

lemma root_solution_below_split:
  "(\<lambda>x. if x = 0 then 7 / 8 else if x = 1 then 5 / 8 else if x = 2 then 3 / 2 else 1 / 4)
     \<in> tableau_bounded_models split_root"
  by (auto simp: tableau_bounded_models_def tableau_models_def example_state_def example_rows_def)

lemma split_not_entailed: "\<not> entailed split_root Lower_Side 0 1"
  using root_solution_below_split unfolding entailed_def by force

theorem decision_keeps_branch: "branch_of split_root decided"
  unfolding decided_def
  by (rule apply_decision_branch[OF root_branch_of]) (simp add: root_branch_def example_state_def)

theorem split_as_derived_breaks_branch:
  "\<not> branch_of split_root (apply_derived Lower_Side 0 1 (root_branch split_root))"
  by (rule undeclared_decision_breaks_branch[OF root_branch_of])
     (use split_not_entailed in \<open>simp_all add: root_branch_def example_state_def\<close>)

text \<open>
  Applying the decision moves the nonbasic x0 from 0 to its new lower bound and
  updates the basics through their rows; x0 becomes pending.
\<close>

lemma decision_effects:
  "map (tableau_candidate (store_tableau (branch_store decided))) [0, 1, 2, 3] = [1, 0, 1, 1]"
  "0 \<in> pending_lower (branch_store decided)"
  "fst (propagate_tightenings [0, 1, 2, 3] (branch_store decided)) = [(0, Lower_Side, 1)]"
  "branch_decisions decided = [(Lower_Side, 0, 1)]"
  by code_simp+

text \<open>
  A second decision x1 \<ge> 1 makes row x3 = x0 - x1 give x3 \<le> 0 against x3 \<ge> 1/4:
  a conflict that refutes this branch only. The root itself has solutions.
\<close>

lemma second_decision_conflict:
  "first_conflict (branch_store decided_twice) = Some (3, Upper_Side, 0)"
  "branch_decisions decided_twice = [(Lower_Side, 0, 1), (Lower_Side, 1, 1)]"
  by code_simp+

theorem branch_refuted_not_root:
  "tableau_bounded_models split_root \<inter> decision_models [(Lower_Side, 0, 1), (Lower_Side, 1, 1)] = {}"
  "tableau_bounded_models split_root \<noteq> {}"
proof -
  let ?Br1 = "apply_decision Lower_Side 1 1 decided"
  have inv: "simplex_invariant split_root [2, 3] [0, 1]"
    using example_invariant[of "1 / 4"] by simp
  have c0: "conflict_sound (branch_store (root_branch split_root))"
    "conflict_complete (branch_store (root_branch split_root))"
    using root_branch_conflicts[OF inv] .
  have x0: "0 \<in> carrier (store_tableau (branch_store (root_branch split_root)))"
    by (simp add: root_branch_def example_state_def)
  have c1: "conflict_sound (branch_store decided)" "conflict_complete (branch_store decided)"
    using tighten_conflict_sound[OF c0(1) x0] tighten_conflict_complete[OF c0(2)]
    by (simp_all add: decided_def apply_decision_def)
  have x1: "1 \<in> carrier (store_tableau (branch_store decided))"
    by (simp add: decided_def apply_decision_def root_branch_def example_state_def)
  have br1: "branch_of split_root ?Br1"
    using apply_decision_branch[OF decision_keeps_branch x1] .
  have c2: "conflict_sound (branch_store ?Br1)" "conflict_complete (branch_store ?Br1)"
    using tighten_conflict_sound[OF c1(1) x1] tighten_conflict_complete[OF c1(2)]
    by (simp_all add: apply_decision_def)
  have sup: "tableau_rows_supported (store_tableau (branch_store ?Br1))"
    using inv
    by (simp add: simplex_invariant_def decided_def apply_decision_def root_branch_def
        tableau_rows_supported_def)
  have sound: "branch_of split_root decided_twice \<and> conflict_sound (branch_store decided_twice)"
    using apply_rules_sound[OF br1 sup c2] by (simp add: decided_twice_def)
  show "tableau_bounded_models split_root \<inter>
          decision_models [(Lower_Side, 0, 1), (Lower_Side, 1, 1)] = {}"
    using branch_conflict_refutes[of split_root decided_twice] sound second_decision_conflict
    by simp
  show "tableau_bounded_models split_root \<noteq> {}"
    using root_solution_below_split by blast
qed

section \<open>Weaker proposals and basic variables\<close>

lemma weaker_proposal_is_noop:
  "snd (tighten_bound Lower_Side 0 (-1) (branch_store (root_branch split_root))) = False"
  "fst (tighten_bound Lower_Side 0 (-1) (branch_store (root_branch split_root))) =
     branch_store (root_branch split_root)"
  by (simp_all add: tighten_weaker root_branch_def example_state_def)

text \<open>
  Tightening the basic x3 keeps its value 1 and only changes its status, here
  to above its new upper bound: the simplex loop then has work to do.
\<close>

lemma basic_tightening_status:
  "status_of (store_tableau (branch_store decided)) 3 = Between"
  "status_of (store_tableau (fst (tighten_bound Upper_Side 3 (3 / 4) (branch_store decided)))) 3 =
     Above_Upper"
  "tableau_candidate (store_tableau (fst (tighten_bound Upper_Side 3 (3 / 4) (branch_store decided)))) 3 = 1"
  by code_simp+

end
