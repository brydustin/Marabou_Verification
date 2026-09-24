# Theory inventory for the project direction audit

Snapshot: 2026-09-23. All 77 top-level theories are registered in `Isabelle/ROOT`.

This index lists every top-level theory, its direct imports, declared objects, and named lemmas/theorems/corollaries. It is an inventory, not a claim that every object models C++.

See [the direction audit](PROJECT_DIRECTION_AUDIT.md) for classification, source correspondence, build results and limitations.

## Core theories (26)

### [Bounded_Inequality_Auxiliary](../Isabelle/Bounded_Inequality_Auxiliary.thy)

Imports: Inequality_Auxiliary_Sequence Exact_Query_Format.

Objects: `opposite_inequality_bound`, `bounded_inequality_step`, `rat_introduce_bounded_inequality_aux`, `rat_introduce_bounded_inequality_sequence`, `bounded_decodes_like`.

Results: `bounded_inequality_step_parts`, `bounded_inequality_step_model`, `bounded_inequality_step_satisfiable_iff`, `bounded_inequality_sequence_append`, `bounded_inequality_sequence_failed_prefix`, `bounded_inequality_sequence_model`, `bounded_inequality_sequence_satisfiable_iff`, `bounded_inequality_sequence_unsatisfiable_iff`, `bounded_decodes_like_decodes`, `bounded_decodes_like_unsatisfiable`, `bounded_decodes_like_model`.

### [Exact_Query_Format](../Isabelle/Exact_Query_Format.thy)

Imports: Rational_Linear_Constraints.

Objects: `bytes`, `ascii`, `split_on`, `digits_value`, `parse_nat`, `parse_unsigned`, `parse_rat`, `parse_var`, `parse_pairs`, `statement`, `parse_linear`, `parse_statement`, `parse_line`, `assemble`, `exact_query_header`, `decode_query`, `same_constraints`, `decodes_like`, `print_nat`, `print_int`, `print_rat`, `print_var`, `print_terms`, `encode_linear`, `encode_bound`, `encode_relu`, `join`, `encode_lines`, `encode_query`, `good_token`, `linear_constant`, `encodable_query`, `encode_statement`, `encodable_statement`, `query_statements`.

Results: `keyword_bytes`, `same_constraints_models`, `same_constraints_unsatisfiable`, `decodes_like_unsatisfiable`, `decodes_like_model`, `decodes_like_decodes`, `split_on_no_separator`, `split_on_append_separator`, `split_on_join`, `split_on_lines`, `print_nat_unfold`, `digits_value_append`, `print_nat_digits`, `print_nat_nonempty`, `digits_value_print_nat`, `parse_nat_print_nat`, `print_nat_not`, `hd_print_nat_not_minus`, `parse_unsigned_print_nat`, `parse_unsigned_fraction`, `parse_rat_print_rat`, `parse_var_print_var`, `parse_pairs_print_terms`, `print_rat_bytes`, `print_rat_nonempty`, `good_print_rat`, `good_print_var`, `good_print_terms`, `encode_linear_good`, `encode_bound_good`, `encode_relu_good`, `encode_statement_good`, `encode_statement_nonempty`, `parse_linear_encoded`, `rat_expr_zero_constant`, `parse_statement_encode`, `join_bytes`, `parse_line_encode`, `encoded_line_no_newline`, `those_map_Some`, `encode_lines_statements`, `concat_map_nil`, `concat_map_single`, `assemble_query_statements`, `header_no_newline`, `decode_encode_query`.

### [Inequality_Auxiliary](../Isabelle/Inequality_Auxiliary.thy)

Imports: Tableau_Auxiliary.

Objects: `inequality_direction`, `inequality_atom`, `inequality_aux_bound`, `introduce_inequality_aux`.

Results: `satisfies_introduce_inequality_aux_iff`, `models_introduce_inequality_aux`, `inequality_aux_model_extension`, `inequality_aux_model_projection`, `satisfiable_introduce_inequality_aux_iff`, `unsatisfiable_introduce_inequality_aux_iff`.

### [Inequality_Auxiliary_Sequence](../Isabelle/Inequality_Auxiliary_Sequence.thy)

Imports: Rational_Inequality_Auxiliary Rational_Assignment.

Objects: `inequality_aux_step`, `rat_introduce_inequality_aux_sequence`, `check_after_inequality_aux_sequence`, `check_assignment_after_inequality_aux_sequence`.

Results: `inequality_aux_sequence_singleton`, `inequality_aux_sequence_append`, `inequality_aux_sequence_failed_prefix`, `inequality_aux_sequence_model`, `inequality_aux_sequence_satisfiable_iff`, `inequality_aux_sequence_unsatisfiable_iff`, `check_after_inequality_aux_sequence_empty`, `check_after_inequality_aux_sequence_singleton`, `check_after_inequality_aux_sequence_sound`, `check_after_inequality_aux_sequence_rejects_model`, `check_assignment_after_inequality_aux_sequence_sound`, `check_assignment_after_inequality_aux_sequence_satisfiable`, `inequality_relu_fixed_assignment_satisfiable`.

### [Linear_Constraints](../Isabelle/Linear_Constraints.thy)

Imports: Marabou_Semantics.

Objects: `satisfies_linear`, `satisfies_bound`.

Results: `linear_eq_iff_two_inequalities`, `lower_bound_as_linear`, `upper_bound_as_linear`, `inconsistent_bounds`, `linear_le_add`, `linear_le_scale_nonnegative`.

### [Marabou_Semantics](../Isabelle/Marabou_Semantics.thy)

Imports: Marabou_Syntax.

Objects: `eval_terms`, `eval_linexpr`, `const_expr`, `var_expr`, `add_linexpr`, `scale_linexpr`.

Results: `eval_terms_append`, `eval_terms_scale`, `eval_const_expr`, `eval_var_expr`, `eval_add_linexpr`, `eval_scale_linexpr`, `eval_terms_cong`.

### [Marabou_Syntax](../Isabelle/Marabou_Syntax.thy)

Imports: "HOL.Real".

Objects: `var`, `valuation`, `linexpr`, `linear_constraint`, `bound`, `relu_constraint`, `query`.

Results: (none).

### [Query_Semantics](../Isabelle/Query_Semantics.thy)

Imports: ReLU_Constraints.

Objects: `satisfies_query`, `models`, `satisfiable`, `unsatisfiable`.

Results: `satisfiable_iff_models_nonempty`, `unsatisfiable_iff_no_valuation`, `unsatisfiable_iff_models_empty`, `query_relu`, `query_inconsistent_bounds`.

### [Rational_Assignment](../Isabelle/Rational_Assignment.thy)

Imports: ReLU_Auxiliary_Sequence.

Objects: `rat_assignment`, `assignment_value`, `assignment_valuation`, `rat_eval_terms`, `rat_eval_expr`, `check_rat_linear`, `check_rat_bound`, `check_rat_relu`, `check_rat_assignment`.

Results: `of_rat_eval_terms`, `of_rat_eval_expr`, `check_rat_linear_iff`, `check_rat_bound_iff`, `of_rat_max_zero`, `check_rat_relu_iff`, `assignment_valuation_eq`, `check_rat_assignment_iff`, `check_rat_assignment_sound`, `check_rat_assignment_satisfiable`, `check_rat_assignment_excludes_certificate`, `unsatisfiable_rejects_assignment`, `fixed_aux_sequence_assignment_satisfiable`, `relu_aux_sequence_assignment_satisfiable`.

### [Rational_Inequality_Auxiliary](../Isabelle/Rational_Inequality_Auxiliary.thy)

Imports: Inequality_Auxiliary Rational_Tableau_Auxiliary.

Objects: `rat_inequality_atom`, `rat_inequality_aux_bound`, `rat_inequality_aux_query`, `rat_introduce_inequality_aux`, `check_after_inequality_aux`.

Results: `embed_rat_inequality_atom`, `embed_rat_inequality_aux_bound`, `embed_rat_inequality_aux_query`, `rat_introduce_inequality_aux_Some_iff`, `rat_inequality_aux_selection`, `rat_introduce_inequality_aux_model`, `rat_introduce_inequality_aux_satisfiable_iff`, `rat_introduce_inequality_aux_unsatisfiable_iff`, `check_after_inequality_aux_sound`.

### [Rational_Linear_Certificates](../Isabelle/Rational_Linear_Certificates.thy)

Imports: Rational_Linear_Constraints.

Objects: `merge_term`, `collect_terms`, `constant_contradiction`, `weighted_sum`, `check_linear_leaf`.

Results: `eval_merge_term`, `eval_collect_terms`, `all_zero_terms_eval`, `constant_contradiction_positive`, `weighted_sum_wellformed`, `weighted_sum_nonpositive`, `check_linear_leaf_sound`, `check_linear_leaf_no_model`, `check_linear_leaf_rejects_model`.

### [Rational_Linear_Constraints](../Isabelle/Rational_Linear_Constraints.thy)

Imports: Query_Semantics.

Objects: `rat_linexpr`, `rat_linear_constraint`, `rat_bound`, `rat_query`, `embed_linexpr`, `embed_linear`, `embed_bound`, `embed_query`, `eval_rat_expr`, `eval_rat_terms`, `rat_add`, `rat_scale`, `rat_sub_rhs`, `normalize_linear`, `normalize_bound`, `normalize_query`, `rat_add_bound`.

Results: `eval_embedded_terms`, `eval_rat_expr_simps`, `eval_rat_terms_append`, `eval_rat_terms_scale`, `eval_rat_add`, `eval_rat_scale`, `eval_rat_sub_rhs`, `normalize_linear_correct`, `normalize_bound_correct`, `normalize_query_correct`, `embed_query_normalization`, `query_implies_normalized`, `satisfies_rat_add_bound_iff`.

### [Rational_Linear_Implication](../Isabelle/Rational_Linear_Implication.thy)

Imports: Rational_Linear_Certificates.

Objects: `constant_nonpositive`, `check_linear_implication`, `check_linear_bound`.

Results: `constant_nonpositive_sound`, `check_linear_implication_sound`, `check_linear_bound_sound`, `rat_linear_bound_preserves_models`, `unsatisfiable_linear_bound`.

### [Rational_Proof_Trees](../Isabelle/Rational_Proof_Trees.thy)

Imports: Rational_Linear_Implication ReLU_Splitting ReLU_Aux_Lower_Bound_Propagation.

Objects: `rat_active_split`, `rat_inactive_split`, `certificate`, `check_certificate`.

Results: `embed_rat_active_split`, `embed_rat_inactive_split`, `check_certificate_sound`, `check_certificate_no_model`, `check_certificate_rejects_model`.

### [Rational_ReLU_Auxiliary](../Isabelle/Rational_ReLU_Auxiliary.thy)

Imports: ReLU_Auxiliary Tableau_Auxiliary_Sequence.

Objects: `rat_relu_aux_bounds`, `rat_relu_aux_lower_present`, `rat_relu_aux_query`, `rat_introduce_relu_aux`, `check_after_relu_aux`.

Results: `embed_rat_relu_aux_bounds`, `embed_rat_relu_aux_query`, `rat_introduce_relu_aux_Some_iff`, `rat_introduce_relu_aux_real`, `rat_relu_aux_model_extension`, `rat_relu_aux_model_projection`, `rat_introduce_relu_aux_satisfiable_iff`, `rat_introduce_relu_aux_unsatisfiable_iff`, `check_after_relu_aux_sound`, `check_after_relu_aux_rejects_model`.

### [Rational_Tableau_Auxiliary](../Isabelle/Rational_Tableau_Auxiliary.thy)

Imports: Tableau_Auxiliary Rational_Proof_Trees.

Objects: `rat_linexpr_vars`, `rat_linear_vars`, `rat_bound_vars`, `rat_query_vars`, `rat_fixed_aux_query`, `rat_introduce_fixed_aux`, `check_after_fixed_aux`.

Results: `linexpr_vars_embed`, `linear_vars_embed`, `bound_vars_embed`, `query_vars_embed`, `embed_rat_fixed_aux_query`, `rat_introduce_fixed_aux_Some_iff`, `rat_introduce_fixed_aux_satisfiable_iff`, `rat_introduce_fixed_aux_unsatisfiable_iff`, `check_after_fixed_aux_sound`.

### [ReLU_Aux_Bound_Propagation](../Isabelle/ReLU_Aux_Bound_Propagation.thy)

Imports: ReLU_Bound_Propagation Rational_Linear_Implication.

Objects: `relu_aux_expr`, `check_relu_aux_upper_bound`.

Results: `relu_aux_identity`, `relu_aux_upper_bound`, `eval_relu_aux_expr`, `check_relu_aux_upper_bound_sound`, `rat_relu_aux_upper_preserves_models`, `unsatisfiable_relu_aux_upper_bound`.

### [ReLU_Aux_Lower_Bound_Propagation](../Isabelle/ReLU_Aux_Lower_Bound_Propagation.thy)

Imports: ReLU_Output_Bound_Propagation.

Objects: `check_relu_aux_lower_output_upper_bound`.

Results: `relu_positive_aux_output_zero`, `relu_zero_aux_does_not_fix_output`, `check_relu_aux_lower_output_upper_bound_sound`, `rat_relu_aux_lower_output_upper_preserves_models`, `unsatisfiable_relu_aux_lower_output_upper_bound`.

### [ReLU_Auxiliary](../Isabelle/ReLU_Auxiliary.thy)

Imports: Tableau_Auxiliary ReLU_Aux_Bound_Propagation.

Objects: `relu_aux_bounds`, `relu_aux_lower_present`, `introduce_relu_aux`.

Results: `satisfies_introduce_relu_aux_raw`, `relu_aux_added_bounds`, `satisfies_introduce_relu_aux_iff`, `models_introduce_relu_aux`, `relu_aux_model_extension`, `relu_aux_model_projection`, `satisfiable_introduce_relu_aux_iff`, `unsatisfiable_introduce_relu_aux_iff`.

### [ReLU_Auxiliary_Sequence](../Isabelle/ReLU_Auxiliary_Sequence.thy)

Imports: Rational_ReLU_Auxiliary.

Objects: `relu_aux_step`, `rat_introduce_relu_aux_sequence`, `check_after_relu_aux_sequence`.

Results: `relu_aux_sequence_singleton`, `relu_aux_sequence_append`, `relu_aux_sequence_failed_prefix`, `relu_aux_sequence_satisfiable_iff`, `relu_aux_sequence_unsatisfiable_iff`, `check_after_relu_aux_sequence_empty`, `check_after_relu_aux_sequence_singleton`, `check_after_relu_aux_sequence_sound`, `check_after_relu_aux_sequence_rejects_model`.

### [ReLU_Bound_Propagation](../Isabelle/ReLU_Bound_Propagation.thy)

Imports: Rational_Linear_Constraints.

Objects: `check_relu_upper_bound`.

Results: `relu_upper_bound`, `check_relu_upper_bound_sound`, `rat_relu_upper_preserves_models`, `unsatisfiable_relu_upper_bound`.

### [ReLU_Constraints](../Isabelle/ReLU_Constraints.thy)

Imports: Linear_Constraints.

Objects: `relu`, `satisfies_relu`, `satisfies_relu_constraint`.

Results: `relu_nonnegative`, `relu_zero`, `relu_of_nonpositive`, `relu_of_nonnegative`, `relu_phase_decomposition`, `satisfies_relu_phase_decomposition`, `relu_phases_overlap_iff`.

### [ReLU_Output_Bound_Propagation](../Isabelle/ReLU_Output_Bound_Propagation.thy)

Imports: ReLU_Aux_Bound_Propagation.

Objects: `check_relu_output_aux_upper_bound`.

Results: `relu_positive_output_aux_zero`, `check_relu_output_aux_upper_bound_sound`, `rat_relu_output_aux_upper_preserves_models`, `unsatisfiable_relu_output_aux_upper_bound`.

### [ReLU_Splitting](../Isabelle/ReLU_Splitting.thy)

Imports: Query_Semantics.

Objects: `active_split`, `inactive_split`.

Results: `satisfies_active_split_iff`, `satisfied_relu_can_be_removed`, `satisfies_inactive_split_iff`, `query_relu_split`, `models_relu_split`, `satisfiable_relu_split`, `unsatisfiable_relu_split`, `split_removes_selected_relu`.

### [Tableau_Auxiliary](../Isabelle/Tableau_Auxiliary.thy)

Imports: Query_Semantics.

Objects: `linexpr_vars`, `linear_vars`, `bound_vars`, `relu_vars`, `query_vars`, `introduce_fixed_aux`.

Results: `eval_linexpr_vars_cong`, `satisfies_linear_vars_cong`, `satisfies_bound_vars_cong`, `satisfies_relu_vars_cong`, `satisfies_query_vars_cong`, `satisfies_query_fresh_update`, `satisfies_introduce_fixed_aux_iff`, `models_introduce_fixed_aux`, `fixed_aux_model_extension`, `fixed_aux_model_projection`, `satisfiable_introduce_fixed_aux_iff`, `unsatisfiable_introduce_fixed_aux_iff`.

### [Tableau_Auxiliary_Sequence](../Isabelle/Tableau_Auxiliary_Sequence.thy)

Imports: Rational_Tableau_Auxiliary.

Objects: `fixed_aux_step`, `rat_introduce_fixed_aux_sequence`, `check_after_fixed_aux_sequence`.

Results: `fixed_aux_sequence_singleton`, `fixed_aux_sequence_append`, `fixed_aux_sequence_failed_prefix`, `fixed_aux_sequence_satisfiable_iff`, `fixed_aux_sequence_unsatisfiable_iff`, `check_after_fixed_aux_sequence_empty`, `check_after_fixed_aux_sequence_singleton`, `check_after_fixed_aux_sequence_sound`, `check_after_fixed_aux_sequence_rejects_model`.

## Example theories (18)

### [Bounded_Inequality_Examples](../Isabelle/Bounded_Inequality_Examples.thy)

Imports: Bounded_Inequality_Auxiliary.

Objects: `bounded_le_query`, `bounded_ge_query`.

Results: `finite_slack_caps_accepted`, `weaker_slack_caps_accepted`, `unjustified_slack_caps_rejected`, `bounded_slack_guard_failures`, `bounded_le_assignment_checked`, `bounded_le_has_model`, `unchecked_cap_would_admit_false_contradiction`, `bounded_le_checked_sequence_cannot_create_unsat`.

### [Exact_Query_Format_Examples](../Isabelle/Exact_Query_Format_Examples.thy)

Imports: Exact_Query_Format Rational_Assignment_Examples.

Objects: `text_lines`, `example_chain_lines`.

Results: `header_only_is_the_empty_query`, `all_statement_forms`, `sat_text_decodes`, `sat_text_model`, `malformed_texts_rejected`, `malformed_numbers_rejected`, `other_bytes_rejected`, `number_spellings`, `encode_sat_rat_query`, `sat_rat_query_round_trip`, `example_chain_text_decodes_like_capture`, `mutated_chain_texts_rejected`.

### [Inequality_Auxiliary_Examples](../Isabelle/Inequality_Auxiliary_Examples.thy)

Imports: Inequality_Auxiliary_Sequence Exact_Query_Format_Examples.

Objects: `inequality_affine_expr`, `inequality_affine_query`, `inequality_affine_result`, `inequality_unsat_query`, `inequality_collision_query`, `inequality_ge_sign_query`, `inequality_relu_query`, `inequality_relu_certificate`.

Results: `inequality_affine_sequence_checked`, `inequality_affine_equisatisfiable`, `inequality_affine_assignment_checked`, `inequality_affine_source_model`, `inequality_zero_slack_boundary`, `inequality_guard_failures`, `inequality_late_failures`, `inequality_incorrect_assignments_rejected`, `inequality_affine_rejects_all_unsat_certificates`, `inequality_unsat_checked`, `inequality_source_unsatisfiable`, `inequality_bad_steps_and_leaf_rejected`, `inequality_collision_model`, `inequality_collision_raw_contradiction`, `inequality_collision_guard_rejects`, `inequality_collision_cannot_be_certified`, `inequality_ge_negative_slack_model`, `inequality_ge_wrong_sign_would_contradict`, `inequality_ge_correct_sign_rejects_false_contradiction`, `inequality_relu_pipeline_checked`, `inequality_relu_query_unsatisfiable`, `inequality_pipeline_later_collision_rejected`, `inequality_relu_linear_relaxation_has_model`, `inequality_relu_needs_nonlinear_evidence`, `inequality_text_decodes`, `inequality_text_unsatisfiable`.

### [Marabou_Examples](../Isabelle/Marabou_Examples.thy)

Imports: ReLU_Splitting.

Objects: `sat_example`, `sat_witness`, `unsat_example`, `zero_example`.

Results: `sat_example_witness`, `sat_example_satisfiable`, `unsat_example_active`, `unsat_example_inactive`, `unsat_example_unsatisfiable`, `zero_in_both_children`.

### [Rational_Assignment_Examples](../Isabelle/Rational_Assignment_Examples.thy)

Imports: Rational_Assignment ReLU_Output_Bound_Examples ReLU_Aux_Lower_Bound_Examples Imported_Marabou_Native_Relu_Sat.

Objects: `sat_rat_query`, `inactive_rat_query`, `relu_violating_assignment`.

Results: `sat_rat_assignment_checked`, `sat_rat_query_satisfiable`, `sat_rat_query_rejects_certificates`, `assignment_extra_variables_accepted`, `assignment_rejections`, `inactive_assignment_checked`, `positive_aux_query_rejects_assignments`, `relaxed_inactive_source_assignment`, `relaxed_chain_source_assignment`, `native_sat_relu_violation_rejected`.

### [Rational_Linear_Examples](../Isabelle/Rational_Linear_Examples.thy)

Imports: Rational_Linear_Certificates Marabou_Examples.

Objects: `fractional_bounds`, `affine_leaf`, `constant_leaf`, `sign_test`, `residual_test`, `zero_margin`, `active_linear_leaf`, `inactive_linear_leaf`.

Results: `fractional_bounds_checked`, `fractional_bounds_unsatisfiable`, `affine_leaf_checked`, `affine_leaf_unsatisfiable`, `constant_leaf_checked`, `unsplit_relus_are_allowed`, `too_few_weights_rejected`, `too_many_weights_rejected`, `zero_weights_rejected`, `negative_weight_rejected`, `sign_test_model`, `sign_test_all_certificates_rejected`, `nonzero_residual_rejected`, `residual_test_model`, `zero_margin_rejected`, `empty_query_rejected`, `active_linear_leaf_checked`, `inactive_linear_leaf_checked`, `embed_active_linear_leaf`, `embed_inactive_linear_leaf`, `unsat_example_via_leaf_certificates`.

### [Rational_Linear_Implication_Examples](../Isabelle/Rational_Linear_Implication_Examples.thy)

Imports: Rational_Proof_Trees.

Objects: `implication_query`, `explained_relu_query`, `explained_relu_certificate`.

Results: `upper_implication_checked`, `lower_implication_checked`, `general_linear_implication_checked`, `weaker_bound_checked`, `stronger_bound_rejected`, `bad_implication_weights_rejected`, `implication_query_has_model`, `implication_query_rejects_every_unsat_certificate`, `implication_is_not_itself_a_contradiction`, `unconditional_constant_targets`, `explained_relu_checked`, `explained_relu_unsatisfiable`, `unexplained_premise_rejected`, `forged_linear_step_rejected`, `linear_step_requires_checked_continuation`, `explained_relu_linear_relaxation_has_model`.

### [Rational_Proof_Tree_Examples](../Isabelle/Rational_Proof_Tree_Examples.thy)

Imports: Rational_Proof_Trees Rational_Linear_Examples.

Objects: `tree_query`, `tree_certificate`, `nested_query`, `nested_subtree`.

Results: `tree_certificate_checked`, `embed_tree_query`, `unsat_example_via_recursive_certificate`, `nested_tree_checked`, `nested_query_unsatisfiable`, `absent_relu_rejected`, `one_bad_child_rejected`, `repeated_split_rejected`, `satisfiable_query_rejects_every_tree`.

### [ReLU_Aux_Bound_Examples](../Isabelle/ReLU_Aux_Bound_Examples.thy)

Imports: Imported_Marabou_Solver_Relu_Aux Imported_Marabou_Solver_Relu_Aux_Active.

Objects: `aux_example`, `aux_certificate`, `active_aux_relaxation`.

Results: `auxiliary_negative_zero_positive_checked`, `auxiliary_negative_unsatisfiable`, `auxiliary_zero_unsatisfiable`, `auxiliary_positive_unsatisfiable`, `weaker_auxiliary_conclusion`, `stronger_auxiliary_conclusion_rejected`, `auxiliary_requires_both_equation_witnesses`, `auxiliary_checks_variables_and_premises`, `auxiliary_requires_checked_continuation`, `missing_auxiliary_equation_has_model`, `missing_auxiliary_equation_rejects_every_certificate`, `active_aux_relaxation_has_model`, `active_aux_relaxation_satisfiable`, `active_aux_capture_has_no_linear_certificate`.

### [ReLU_Aux_Lower_Bound_Examples](../Isabelle/ReLU_Aux_Lower_Bound_Examples.thy)

Imports: Imported_Marabou_Source_Relu_Aux_Inactive.

Objects: `aux_lower_query`, `aux_lower_certificate`, `captured_inactive_relaxation`, `relaxed_inactive_source`.

Results: `positive_aux_certificate_checked`, `positive_aux_query_unsatisfiable`, `aux_rule_accepts_weaker_conclusion`, `aux_rule_rejects_insufficient_weaker_conclusion`, `aux_rule_accepts_exact_tiny_positive_premise`, `positive_aux_satisfiable_model`, `positive_aux_sat_query_rejects_all_certificates`, `zero_aux_countermodel`, `zero_aux_raw_bound_creates_contradiction`, `aux_rule_rejects_nonpositive_premises`, `zero_aux_query_rejects_every_certificate`, `aux_rule_rejects_stronger_conclusion`, `aux_rule_rejects_wrong_or_absent_premise`, `aux_rule_needs_both_equation_witnesses`, `aux_rule_rejects_wrong_variables_or_missing_relu`, `aux_rule_needs_checked_continuation`, `output_rule_cannot_use_auxiliary_premise`, `captured_inactive_relaxation_has_model`, `captured_inactive_query_requires_nonlinear_evidence`, `relaxed_inactive_source_has_model`, `relaxed_inactive_source_rejects_all_sequence_certificates`.

### [ReLU_Auxiliary_Examples](../Isabelle/ReLU_Auxiliary_Examples.thy)

Imports: Rational_ReLU_Auxiliary Imported_Marabou_Source_Relu_Aux.

Objects: `solver_before_relu_aux`, `relu_interval_query`, `negative_relu_aux_result`, `negative_relu_witness`, `unbounded_relu_source`, `unbounded_relu_aux_result`, `occupied_relu_source`, `relu_collision_result`, `no_relu_source`.

Results: `solver_relu_aux_matches_captured_source`, `solver_relu_aux_source_equisatisfiable`, `solver_before_relu_aux_checked`, `solver_before_relu_aux_unsatisfiable`, `solver_relu_aux_rejects_bad_bridge_or_proof`, `negative_relu_aux_introduction`, `negative_relu_source_has_model`, `negative_relu_aux_extended_model`, `negative_relu_aux_needs_extension`, `negative_relu_source_rejects_all_certificates`, `zero_relu_aux_introduction`, `positive_relu_aux_introduction`, `unbounded_relu_aux_introduction`, `unbounded_relu_aux_has_model`, `same_input_output_is_supported`, `relu_aux_rejects_all_syntactic_collisions`, `relu_aux_rejects_reused_auxiliary`, `relu_aux_rejects_missing_premises`, `relu_collision_source_has_model`, `relu_collision_result_checked`, `relu_collision_raw_result_unsatisfiable`, `relu_collision_cannot_certify_source`, `no_relu_source_has_model`, `no_relu_raw_result_checked`, `no_relu_raw_result_unsatisfiable`, `missing_relu_cannot_certify_source`.

### [ReLU_Auxiliary_Sequence_Examples](../Isabelle/ReLU_Auxiliary_Sequence_Examples.thy)

Imports: Imported_Marabou_Native_Relu_Sequence.

Objects: `two_relu_intervals`, `interval_introductions`, `introduced_intervals`, `interval_witness`, `without_first_relu`, `without_second_relu`, `first_removed_witness`, `second_removed_witness`.

Results: `interval_sequence_computes`, `interval_source_has_model`, `interval_result_has_model`, `interval_source_rejects_all_sequence_certificates`, `interval_sequence_prefix_succeeds`, `sequence_rejects_late_collision`, `sequence_rejects_late_premise_or_selection`, `failed_sequence_cannot_be_repaired_by_appending`, `same_relu_with_another_fresh_auxiliary`, `first_relu_removed_model`, `second_relu_removed_model`, `native_source_needs_both_relus`, `native_sequence_rejects_incomplete_bridge_or_proof`.

### [ReLU_Bound_Examples](../Isabelle/ReLU_Bound_Examples.thy)

Imports: Rational_Proof_Trees.

Objects: `negative_upper_query`, `positive_upper_query`, `upper_sat_query`, `upper_chain_query`.

Results: `negative_upper_checked`, `negative_upper_unsatisfiable`, `positive_upper_checked`, `positive_upper_unsatisfiable`, `weaker_conclusion_allowed`, `zero_upper_checked`, `negative_upper_linear_model`, `positive_upper_linear_model`, `upper_sat_model`, `upper_sat_rejects_every_certificate`, `forged_input_upper_rejected`, `too_strong_output_upper_rejected`, `negative_output_upper_rejected`, `absent_relu_upper_rejected`, `wrong_relu_direction_rejected`, `propagation_still_requires_a_checked_child`, `upper_chain_checked`, `upper_chain_unsatisfiable`, `future_premise_rejected`.

### [ReLU_Output_Bound_Examples](../Isabelle/ReLU_Output_Bound_Examples.thy)

Imports: Imported_Marabou_Native_Relu_Chain.

Objects: `output_aux_query`, `output_aux_certificate`, `relaxed_chain_source`.

Results: `positive_output_certificate_checked`, `positive_output_query_unsatisfiable`, `output_rule_accepts_weaker_conclusion`, `output_rule_accepts_exact_tiny_positive_premise`, `positive_output_satisfiable_model`, `positive_output_sat_query_rejects_all_certificates`, `zero_output_countermodel`, `zero_output_raw_bound_creates_contradiction`, `output_rule_rejects_nonpositive_premises`, `zero_output_query_rejects_every_certificate`, `output_rule_rejects_stronger_conclusion`, `output_rule_rejects_wrong_or_absent_premise`, `output_rule_needs_both_equation_witnesses`, `output_rule_rejects_wrong_variables_or_missing_relu`, `output_rule_needs_checked_continuation`, `relaxed_chain_has_model`, `relaxed_chain_rejects_all_sequence_certificates`.

### [Solver_ReLU_Examples](../Isabelle/Solver_ReLU_Examples.thy)

Imports: Imported_Marabou_Solver_Relu.

Objects: `captured_linear_relaxation`, `captured_relaxation_witness`.

Results: `captured_linear_relaxation_has_model`, `captured_linear_relaxation_satisfiable`, `captured_linear_relaxation_rejects_every_certificate`, `captured_query_requires_nonlinear_evidence`.

### [Solver_ReLU_Split_Examples](../Isabelle/Solver_ReLU_Split_Examples.thy)

Imports: Imported_Marabou_Solver_Relu_Split.

Objects: `captured_active_child`, `captured_inactive_child`, `split_linear_relaxation`, `split_relaxation_witness`.

Results: `captured_split_shape`, `captured_active_child_checked`, `captured_inactive_child_checked`, `captured_active_child_unsatisfiable`, `captured_inactive_child_unsatisfiable`, `split_linear_relaxation_has_model`, `split_linear_relaxation_satisfiable`, `captured_split_requires_nonlinear_evidence`.

### [Tableau_Auxiliary_Examples](../Isabelle/Tableau_Auxiliary_Examples.thy)

Imports: Rational_Tableau_Auxiliary Imported_Marabou_Solver_Linear.

Objects: `solver_linear_before_aux`, `affine_aux_expr`, `affine_aux_source`, `affine_aux_result`, `affine_aux_witness`, `collision_source`, `collision_result`.

Results: `solver_linear_aux_matches_snapshot`, `solver_linear_aux_equisatisfiable`, `solver_linear_before_aux_checked`, `solver_linear_before_aux_unsatisfiable`, `solver_linear_rejects_bad_step_or_leaf`, `affine_aux_step_checked`, `affine_aux_preserves_other_atoms`, `affine_aux_source_has_model`, `affine_aux_extended_model`, `affine_aux_needs_model_extension`, `all_syntactic_collisions_rejected`, `invalid_positions_and_inequalities_rejected`, `auxiliary_reuse_rejected`, `negative_scalar_introduction`, `collision_source_has_model`, `collision_source_satisfiable`, `collision_result_checked`, `collision_result_unsatisfiable`, `collision_cannot_be_used_to_certify_source`.

### [Tableau_Auxiliary_Sequence_Examples](../Isabelle/Tableau_Auxiliary_Sequence_Examples.thy)

Imports: Tableau_Auxiliary_Sequence Imported_Marabou_Solver_Relu_Split.

Objects: `solver_split_input_query`, `solver_split_column_query`, `solver_split_aux_steps`, `sequence_sat_source`, `sequence_sat_result`.

Results: `solver_split_term_order_semantics`, `solver_split_sequence_matches_snapshot`, `solver_split_source_equisatisfiable`, `solver_split_before_aux_checked`, `solver_split_before_aux_unsatisfiable`, `solver_split_sequence_rejects_invalid_steps`, `solver_split_failed_prefix_stays_failed`, `solver_split_partial_sequence_rejects_saved_certificate`, `solver_split_sequence_checks_both_terminal_children`, `sequence_reads_current_scalar`, `sequence_sat_source_has_model`, `sequence_sat_result_has_model`, `sequence_sat_source_rejects_every_certificate`.

## Imported and file-binding theories (33)

### [Imported_Marabou_Exact_Texts](../Isabelle/Imported_Marabou_Exact_Texts.thy)

Imports: Exact_Query_Format Imported_Marabou_Source_Linear Imported_Marabou_Source_Relu Imported_Marabou_Source_Relu_Aux Imported_Marabou_Source_Relu_Aux_Active Imported_Marabou_Source_Relu_Aux_Inactive Imported_Marabou_Source_Relu_Split Imported_Marabou_Native_Relu_Intro Imported_Marabou_Native_Relu_Sequence Imported_Marabou_Native_Relu_Chain Imported_Marabou_Native_Relu_Sat.

Objects: `solver_linear_text`, `solver_relu_text`, `solver_relu_aux_text`, `solver_relu_aux_active_text`, `solver_relu_aux_inactive_text`, `solver_relu_split_text`, `solver_relu_intro_text`, `solver_relu_sequence_text`, `solver_relu_chain_text`, `solver_relu_sat_text`.

Results: `solver_linear_text_decodes`, `solver_linear_text_unsatisfiable`, `solver_relu_text_decodes`, `solver_relu_text_unsatisfiable`, `solver_relu_aux_text_decodes`, `solver_relu_aux_text_unsatisfiable`, `solver_relu_aux_active_text_decodes`, `solver_relu_aux_active_text_unsatisfiable`, `solver_relu_aux_inactive_text_decodes`, `solver_relu_aux_inactive_text_unsatisfiable`, `solver_relu_split_text_decodes`, `solver_relu_split_text_unsatisfiable`, `solver_relu_intro_text_decodes`, `solver_relu_intro_text_unsatisfiable`, `solver_relu_sequence_text_decodes`, `solver_relu_sequence_text_unsatisfiable`, `solver_relu_chain_text_decodes`, `solver_relu_chain_text_unsatisfiable`, `solver_relu_sat_text_decodes`, `solver_relu_sat_text_model`, `solver_relu_sat_text_satisfiable`.

### [Imported_Marabou_Example_Inequality_Relu_Sat](../Isabelle/Imported_Marabou_Example_Inequality_Relu_Sat.thy)

Imports: "Marabou_Verification.Bounded_Inequality_Auxiliary" Imported_Marabou_Prepared_Inequality_Relu_Sat.

Objects: `query_file`, `inequality_steps`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_model`, `query_file_satisfiable`.

### [Imported_Marabou_Example_Inequality_Relu_Unsat](../Isabelle/Imported_Marabou_Example_Inequality_Relu_Unsat.thy)

Imports: "Marabou_Verification.Bounded_Inequality_Auxiliary" Imported_Marabou_Prepared_Inequality_Relu_Unsat.

Objects: `query_file`, `inequality_steps`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Example_Linear_Unsat](../Isabelle/Imported_Marabou_Example_Linear_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Source_Linear.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Example_Relu_Chain_Unsat](../Isabelle/Imported_Marabou_Example_Relu_Chain_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Native_Relu_Chain.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Example_Relu_Sat](../Isabelle/Imported_Marabou_Example_Relu_Sat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Native_Relu_Sat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_model`, `query_file_satisfiable`.

### [Imported_Marabou_Explained_Negative](../Isabelle/Imported_Marabou_Explained_Negative.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Explained_Positive](../Isabelle/Imported_Marabou_Explained_Positive.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Linear](../Isabelle/Imported_Marabou_Linear.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Native_Relu_Chain](../Isabelle/Imported_Marabou_Native_Relu_Chain.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Native_Relu_Intro](../Isabelle/Imported_Marabou_Native_Relu_Intro.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.Rational_ReLU_Auxiliary".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introduction_matches_source`, `imported_relu_introduction_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Native_Relu_Sat](../Isabelle/Imported_Marabou_Native_Relu_Sat.thy)

Imports: "Marabou_Verification.Rational_Assignment".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_assignment`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_assignment_checked`, `imported_query_model`, `imported_query_satisfiable`, `imported_source_assignment_checked`, `imported_source_query_model`, `imported_source_query_satisfiable_via_processed`, `imported_relu_introductions_match_source`, `imported_before_relu_assignment_checked`, `imported_before_relu_query_model`, `imported_before_relu_query_satisfiable_via_processed`.

### [Imported_Marabou_Native_Relu_Sequence](../Isabelle/Imported_Marabou_Native_Relu_Sequence.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Nested](../Isabelle/Imported_Marabou_Nested.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Prepared_Inequality_Relu_Sat](../Isabelle/Imported_Marabou_Prepared_Inequality_Relu_Sat.thy)

Imports: "Marabou_Verification.Rational_Assignment".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_assignment`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_assignment_checked`, `imported_query_model`, `imported_query_satisfiable`, `imported_source_assignment_checked`, `imported_source_query_model`, `imported_source_query_satisfiable_via_processed`, `imported_relu_introductions_match_source`, `imported_before_relu_assignment_checked`, `imported_before_relu_query_model`, `imported_before_relu_query_satisfiable_via_processed`.

### [Imported_Marabou_Prepared_Inequality_Relu_Unsat](../Isabelle/Imported_Marabou_Prepared_Inequality_Relu_Unsat.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Propagation](../Isabelle/Imported_Marabou_Propagation.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Propagation_Chain](../Isabelle/Imported_Marabou_Propagation_Chain.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Propagation_Positive](../Isabelle/Imported_Marabou_Propagation_Positive.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Propagation_Tree](../Isabelle/Imported_Marabou_Propagation_Tree.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Relu](../Isabelle/Imported_Marabou_Relu.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Linear](../Isabelle/Imported_Marabou_Solver_Linear.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Relu](../Isabelle/Imported_Marabou_Solver_Relu.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Relu_Aux](../Isabelle/Imported_Marabou_Solver_Relu_Aux.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Relu_Aux_Active](../Isabelle/Imported_Marabou_Solver_Relu_Aux_Active.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Relu_Aux_Inactive](../Isabelle/Imported_Marabou_Solver_Relu_Aux_Inactive.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Solver_Relu_Split](../Isabelle/Imported_Marabou_Solver_Relu_Split.thy)

Imports: "Marabou_Verification.Rational_Proof_Trees".

Objects: `imported_query`, `imported_certificate`.

Results: `imported_certificate_checked`, `imported_query_unsatisfiable`.

### [Imported_Marabou_Source_Linear](../Isabelle/Imported_Marabou_Source_Linear.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

### [Imported_Marabou_Source_Relu](../Isabelle/Imported_Marabou_Source_Relu.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

### [Imported_Marabou_Source_Relu_Aux](../Isabelle/Imported_Marabou_Source_Relu_Aux.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

### [Imported_Marabou_Source_Relu_Aux_Active](../Isabelle/Imported_Marabou_Source_Relu_Aux_Active.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

### [Imported_Marabou_Source_Relu_Aux_Inactive](../Isabelle/Imported_Marabou_Source_Relu_Aux_Inactive.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

### [Imported_Marabou_Source_Relu_Split](../Isabelle/Imported_Marabou_Source_Relu_Split.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`.

## Theories added after the audit snapshot

The sections above are the audit-time snapshot of 77 theories. The following 35 theories were added later, in session order; the entries are extracted from their sources in the same format.

### [Tableau_State](../Isabelle/Tableau_State.thy)

Imports: Tableau_Auxiliary.

Objects: `tableau_state`, `tableau_well_formed`, `tableau_rows_satisfied`, `tableau_nonbasic_bounds_satisfied`, `tableau_candidate`, `tableau_models`.

Results: `tableau_candidate_satisfies_rows`, `tableau_models_update_independent`.

### [Tableau_Assignment_Update](../Isabelle/Tableau_Assignment_Update.thy)

Imports: Tableau_State.

Objects: `linexpr_coefficient`, `update_nonbasic_assignment`.

Results: `eval_terms_update`, `eval_linexpr_update`, `update_nonbasic_preserves_rows`, `update_nonbasic_preserves_well_formed`, `update_nonbasic_preserves_bounds`, `update_nonbasic_candidate_satisfies_rows`.

### [Tableau_Pivot](../Isabelle/Tableau_Pivot.thy)

Imports: Tableau_Assignment_Update.

Objects: `row_terms`, `row_const`, `row_coefficient`, `drop_var`, `scale_terms`, `solve_row`, `substitute_row`, `exchange_rows`, `exchange_basis`, `pivot_admissible`, `tableau_rows_supported`, `tableau_represents`, `tableau_bounded_models`, `pivot_and_set`.

Results: `eval_linexpr_parts`, `linexpr_vars_parts`, `eval_terms_drop_var`, `eval_terms_scale_terms`, `coefficient_drop_var_same`, `coefficient_drop_var_other`, `coefficient_scale_terms`, `coefficient_append`, `coefficient_absent`, `vars_drop_var`, `vars_scale_terms`, `eval_row_split`, `eval_solve_row`, `solve_row_iff`, `eval_substitute_row`, `vars_solve_row`, `vars_substitute_row`, `coefficient_solve_row_leaving`, `well_formed_rows_supported`, `exchange_basis_simps`, `pivot_admissible_facts`, `exchange_carrier`, `exchange_models`, `exchange_rows_supported`, `exchange_well_formed`, `exchange_candidate`, `exchange_nonbasic_bounds`, `candidate_row_eval`, `rows_satisfied_iff_candidate`, `exchange_rows_satisfied`, `exchange_pivot_element`, `exchange_back_admissible`, `solved_rows_unique`, `exchange_back_rows`, `exchange_represents`, `basis_determines_rows`, `exchange_bounded_models`, `pivot_and_set_sound`.

### [Tableau_Simplex_Step](../Isabelle/Tableau_Simplex_Step.thy)

Imports: Tableau_Pivot.

Objects: `basic_status`, `status_of`, `core_cost`, `reduced_cost`, `direction`, `direction_sign`, `entering_direction`, `entering_range`, `step_rate`, `basic_limit`, `basic_ratio`, `status_kept`, `min_ratio`, `pick_leaving`, `ratio_choice`, `exact_harris_ratio_test`, `move_entering`, `apply_choice`, `step_within_ratios`, `choice_admissible`, `tableau_bounds_ordered`, `native_leaving_target`.

Results: `direction_sign_square`, `direction_sign_nonzero`, `basic_ratio_rate`, `basic_ratio_coefficient`, `status_of_iff`, `basic_limit_sign`, `basic_ratio_nonneg`, `basic_ratio_step`, `basic_ratio_reaches_limit`, `status_kept_limit`, `min_ratio_none`, `min_ratio_le`, `min_ratio_attained`, `pick_leaving_from`, `pick_leaving_keeps`, `pick_leaving_finds`, `exact_harris_admissible`, `update_nonbasic_simps`, `update_coefficient_is_row_coefficient`, `move_entering_values`, `move_entering_simps`, `move_entering_models`, `move_entering_rows_satisfied`, `entering_within_bounds`, `limit_is_native_target`, `leaving_native_formulas`, `choice_invariants`, `eval_terms_as_sum`, `eval_linexpr_difference`, `no_entering_candidate_infeasible`, `all_between_candidate_feasible`.

### [Tableau_Index_Layout](../Isabelle/Tableau_Index_Layout.thy)

Imports: Tableau_Simplex_Step.

Objects: `tableau_layout`, `position`, `layout_valid`, `variable_to_index`, `layout_abstracts`, `change_column`, `swap_indices`, `native_degenerate_pivot`, `native_pivot`, `native_bound_flip`.

Results: `position_less`, `nth_position`, `position_nth`, `layout_swap_valid`, `variable_to_index_after_swap`, `exchange_values`, `layout_abstracts_facts`, `native_degenerate_pivot_refines`, `move_values_general`, `native_pivot_refines`, `native_bound_flip_refines`, `native_simplex_pivot_refines`.

### [Tableau_Simplex_Run](../Isabelle/Tableau_Simplex_Run.thy)

Imports: Tableau_Index_Layout.

Objects: `simplex_outcome`, `first_eligible`, `all_between`, `simplex_run`, `simplex_invariant`.

Results: `first_eligible_some`, `first_eligible_none`, `entering_direction_range`, `all_between_iff`, `update_position`, `simplex_step_invariant`, `simplex_run_sound_all`, `simplex_run_sound`, `simplex_run_represented`.

### [Tableau_Pivot_Examples](../Isabelle/Tableau_Pivot_Examples.thy)

Imports: Tableau_Simplex_Run.

Objects: `example_rows`, `example_state`, `example_equations`, `example_layout`, `feasible_run`, `infeasible_run`, `zero_pivot_state`, `overstep_state`.

Results: `example_invariant`, `example_represents`, `example_exchange_rows`, `example_exchange_admissible`, `example_exchange_models`, `example_first_choice`, `example_layout_abstracts`, `example_native_pivot`, `example_native_pivot_refines`, `feasible_run_result`, `feasible_run_solution`, `infeasible_run_result`, `example_infeasible`, `zero_pivot_rejected`, `overstep_rejected`.

### [Tableau_Initialization](../Isabelle/Tableau_Initialization.thy)

Imports: Tableau_Simplex_Run.

Objects: `bound_variable`, `lowers`, `uppers`, `lower_of`, `upper_of`, `is_equation`, `constraint_expr`, `constraint_scalar`, `aux_terms`, `aux_scalar`, `engine_ready`, `bounds_consistent`, `initial_rows`, `initial_lower`, `initial_upper`, `initial_tableau`, `initial_basics`, `extend_aux`, `linear_result`, `solve_linear_part`.

Results: `lowers_mem`, `uppers_mem`, `bounds_iff`, `engine_ready_facts`, `query_bounds_iff`, `equation_iff`, `inconsistent_bounds_unsatisfiable`, `initial_tableau_simps`, `aux_range`, `initial_tableau_invariant`, `initial_bounded_models`, `eval_aux_terms_extend`, `query_model_extends`, `bounded_model_satisfies_linear_part`, `initial_empty_unsatisfiable`, `is_simplex_unsat_iff`, `solve_linear_part_unsat`, `solve_linear_part_feasible`, `solve_linear_part_model`, `solve_linear_part_sat`.

### [Tableau_Initial_Basis](../Isabelle/Tableau_Initial_Basis.thy)

Imports: Tableau_Initialization.

Objects: `pivot_sequence`, `reset_assignment`, `lists_match`, `basis_search`, `swap`, `equation_coefficient`, `initial_search`, `densest`, `search_step`, `search_loop`, `select_initial_basis`, `basis_pivots`, `basis_order`, `native_initial_tableau`, `solve_linear_part_native`, `query_width`, `solve_query`.

Results: `pivot_sequence_sound`, `reset_assignment_simps`, `reset_assignment_invariant`, `native_initial_tableau_sound`, `solve_linear_part_native_unsat`, `solve_linear_part_native_feasible`, `solve_linear_part_native_model`, `solve_query_unsat`, `solve_query_model`, `solve_query_sat`.

### [Tableau_Initialization_Examples](../Isabelle/Tableau_Initialization_Examples.thy)

Imports: Tableau_Initial_Basis Imported_Marabou_Initial_Bases Imported_Marabou_Example_Linear_Unsat Imported_Marabou_Example_Relu_Sat.

Objects: `linear_sat_query`, `relu_linear_unsat_query`, `inequality_query`, `unbounded_query`, `crossed_bounds_query`.

Results: `linear_unsat_file_solved`, `linear_unsat_file_unsatisfiable_by_simplex`, `linear_sat_query_solved`, `linear_sat_query_satisfiable`, `relu_linear_unsat_query_unsatisfiable`, `relu_sat_file_relaxation_only`, `relu_split_swapped_basis_rejected`, `solver_boundaries`, `crossed_bounds_query_unsatisfiable`.

### [Imported_Marabou_Initial_Bases](../Isabelle/Imported_Marabou_Initial_Bases.thy)

Imports: Tableau_Initial_Basis Rational_Linear_Constraints.

Objects: `solver_linear_source`, `solver_relu_source`, `solver_relu_aux_source`, `solver_relu_aux_active_source`, `solver_relu_aux_inactive_source`, `solver_relu_split_source`, `solver_relu_intro_source`, `solver_relu_sequence_source`, `solver_relu_chain_source`, `solver_relu_sat_source`, `file_inequality_relu_unsat_source`, `file_inequality_relu_sat_source`, `file_inequality_linear_sat_source`, `file_phase_active_unsat_source`, `file_phase_inactive_unsat_source`, `file_phase_chain_unsat_source`, `file_phase_fixed_sat_source`, `file_preprocess_split_unsat_source`, `file_preprocess_eliminate_unsat_source`, `file_preprocess_mixed_sat_source`.

Results: `solver_linear_native_initial_basis`, `solver_relu_native_initial_basis`, `solver_relu_aux_native_initial_basis`, `solver_relu_aux_active_native_initial_basis`, `solver_relu_aux_inactive_native_initial_basis`, `solver_relu_split_native_initial_basis`, `solver_relu_intro_native_initial_basis`, `solver_relu_sequence_native_initial_basis`, `solver_relu_chain_native_initial_basis`, `solver_relu_sat_native_initial_basis`, `file_inequality_relu_unsat_native_initial_basis`, `file_inequality_relu_sat_native_initial_basis`, `file_inequality_linear_sat_native_initial_basis`, `file_phase_active_unsat_native_initial_basis`, `file_phase_inactive_unsat_native_initial_basis`, `file_phase_chain_unsat_native_initial_basis`, `file_phase_fixed_sat_native_initial_basis`, `file_preprocess_split_unsat_native_initial_basis`, `file_preprocess_eliminate_unsat_native_initial_basis`, `file_preprocess_mixed_sat_native_initial_basis`.

### [Tableau_Bound_Update](../Isabelle/Tableau_Bound_Update.thy)

Imports: Tableau_Initial_Basis.

Objects: `bound_side`, `bound_store`, `bound_holds`, `stronger`, `with_bound`, `crossed`, `carrier`, `mark_pending`, `set_bound`, `comply`, `tighten_bound`, `propagate_tightenings`, `conflict_sound`, `conflict_complete`, `branch`, `decision_models`, `branch_of`, `entailed`, `apply_derived`, `apply_decision`, `root_branch`, `term_lower`, `term_upper`, `row_lower_bound`, `row_upper_bound`, `solved_bounds`, `row_rule`, `rule_valid`, `rule_bound`, `apply_rules`, `row_rules`.

Results: `with_bound_simps`, `comply_simps`, `bounded_models_cong`, `tighten_weaker`, `tighten_stronger`, `tighten_store_tableau`, `tighten_structure`, `stronger_implies_old`, `tighten_bounded_models`, `tighten_weaker_noop`, `tighten_invariant`, `tighten_basic_value`, `tighten_pending`, `propagated_bounds_hold`, `propagate_tightenings_exact`, `tighten_bounds_monotone`, `crossed_persists`, `tighten_conflict`, `tighten_conflict_sound`, `tighten_conflict_complete`, `conflict_no_bounded_model`, `all_bounds_valid_iff`, `root_branch_of`, `root_branch_conflicts`, `tighten_bounded_models_subset`, `apply_derived_branch`, `apply_decision_branch`, `undeclared_decision_breaks_branch`, `branch_conflict_refutes`, `root_conflict_unsatisfiable`, `branch_simplex_infeasible`, `eval_terms_within`, `row_bounds_within`, `bounded_model_facts`, `row_rule_entailed`, `rule_target_in_carrier`, `apply_rules_sound`.

### [Tableau_Bound_Update_Examples](../Isabelle/Tableau_Bound_Update_Examples.thy)

Imports: Tableau_Bound_Update Tableau_Pivot_Examples Imported_Marabou_Example_Linear_Unsat.

Objects: `row_refutation`, `split_root`, `decided`, `decided_twice`.

Results: `linear_unsat_row_conflict`, `linear_unsat_file_unsatisfiable_by_bounds`, `root_solution_below_split`, `split_not_entailed`, `decision_keeps_branch`, `split_as_derived_breaks_branch`, `decision_effects`, `second_decision_conflict`, `branch_refuted_not_root`, `weaker_proposal_is_noop`, `basic_tightening_status`.

### [ReLU_Phase_Fixing](../Isabelle/ReLU_Phase_Fixing.thy)

Imports: Rational_Linear_Implication ReLU_Splitting.

Objects: `relu_hull_query`, `active_phase_bound`, `inactive_phase_bound`, `check_relu_fixed_active`, `check_relu_fixed_inactive`.

Results: `relu_hull_query_models`, `phase_bound_holds`, `check_relu_fixed_active_sound`, `check_relu_fixed_inactive_sound`, `relu_fixed_active_models`, `relu_fixed_inactive_models`, `unsatisfiable_relu_fixed_active`, `unsatisfiable_relu_fixed_inactive`, `phase_premises_need_exact_signs`.

### [ReLU_Phase_Fixing_Examples](../Isabelle/ReLU_Phase_Fixing_Examples.thy)

Imports: Rational_Proof_Trees Rational_Assignment.

Objects: `active_by_output`, `active_by_output_certificate`, `active_by_auxiliary`, `inactive_by_input`, `inactive_by_input_certificate`, `inactive_by_output`, `tiny_positive`.

Results: `active_by_output_checked`, `active_by_output_unsatisfiable`, `active_by_output_relaxation_has_model`, `active_by_auxiliary_premise`, `hull_row_is_needed`, `inactive_by_input_checked`, `inactive_by_input_unsatisfiable`, `inactive_by_input_relaxation_has_model`, `inactive_by_output_checked`, `tiny_positive_has_model`, `tiny_positive_inactive_split_is_unsatisfiable`, `tiny_positive_premise_rejected`, `tiny_positive_has_no_certificate`, `phase_fixing_rejections`.

### [Preprocessing_Projection](../Isabelle/Preprocessing_Projection.thy)

Imports: Rational_Proof_Trees.

Objects: `relu_active_facts`, `relu_inactive_facts`, `fact`, `apply_fact`, `apply_facts`, `proj_var`, `rename_expr`, `same_value`, `relu_link`, `check_relu_link`, `projection`, `check_projection`, `projection_map`.

Results: `apply_fact_models`, `apply_facts_models`, `eval_rename_terms`, `eval_rename_expr`, `same_value_sound`, `list_all2_left_witness`, `check_projection_model`, `check_projection_unsatisfiable`, `check_projection_rejects_false_unsat`.

### [Preprocessing_Projection_Examples](../Isabelle/Preprocessing_Projection_Examples.thy)

Imports: Preprocessing_Projection Rational_Assignment.

Objects: `merged_source`, `merged_result`, `merged_facts`, `merged_rows`, `merged_link`, `merged_projection`, `relu_facts_source`, `relu_facts`, `narrow_source`, `snapped`.

Results: `merged_projection_checked`, `merged_models_project`, `merged_projection_rejections`, `relu_facts_derive_bounds`, `relu_fact_rejections`, `narrow_source_has_model`, `snapped_unsatisfiable`, `snapped_projection_rejected`.

### [Imported_Marabou_Prepared_Inequality_Linear_Sat](../Isabelle/Imported_Marabou_Prepared_Inequality_Linear_Sat.thy)

Imports: "Marabou_Verification.Rational_Assignment".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_assignment`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_assignment_checked`, `imported_query_model`, `imported_query_satisfiable`, `imported_source_assignment_checked`, `imported_source_query_model`, `imported_source_query_satisfiable_via_processed`.

### [Imported_Marabou_Example_Inequality_Linear_Sat](../Isabelle/Imported_Marabou_Example_Inequality_Linear_Sat.thy)

Imports: "Marabou_Verification.Bounded_Inequality_Auxiliary" Imported_Marabou_Prepared_Inequality_Linear_Sat.

Objects: `query_file`, `inequality_steps`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_model`, `query_file_satisfiable`.

### [Imported_Marabou_File_Phase_Active_Unsat](../Isabelle/Imported_Marabou_File_Phase_Active_Unsat.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Example_Phase_Active_Unsat](../Isabelle/Imported_Marabou_Example_Phase_Active_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_File_Phase_Active_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_File_Phase_Inactive_Unsat](../Isabelle/Imported_Marabou_File_Phase_Inactive_Unsat.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Example_Phase_Inactive_Unsat](../Isabelle/Imported_Marabou_Example_Phase_Inactive_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_File_Phase_Inactive_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_File_Phase_Chain_Unsat](../Isabelle/Imported_Marabou_File_Phase_Chain_Unsat.thy)

Imports: "Marabou_Verification.Tableau_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_relu_introductions_match_source`, `imported_relu_introductions_equisatisfiable`, `imported_before_relu_processed_equisatisfiable`, `imported_before_relu_certificate_checked`, `imported_before_relu_query_unsatisfiable`.

### [Imported_Marabou_Example_Phase_Chain_Unsat](../Isabelle/Imported_Marabou_Example_Phase_Chain_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_File_Phase_Chain_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_File_Phase_Fixed_Sat](../Isabelle/Imported_Marabou_File_Phase_Fixed_Sat.thy)

Imports: "Marabou_Verification.Rational_Assignment".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_assignment`, `imported_before_relu_query`, `imported_relu_steps`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_assignment_checked`, `imported_query_model`, `imported_query_satisfiable`, `imported_source_assignment_checked`, `imported_source_query_model`, `imported_source_query_satisfiable_via_processed`, `imported_relu_introductions_match_source`, `imported_before_relu_assignment_checked`, `imported_before_relu_query_model`, `imported_before_relu_query_satisfiable_via_processed`.

### [Imported_Marabou_Example_Phase_Fixed_Sat](../Isabelle/Imported_Marabou_Example_Phase_Fixed_Sat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_File_Phase_Fixed_Sat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_model`, `query_file_satisfiable`.

### [Imported_Marabou_Preprocessed_Split_Unsat](../Isabelle/Imported_Marabou_Preprocessed_Split_Unsat.thy)

Imports: "Marabou_Verification.Preprocessing_Projection" "Marabou_Verification.Inequality_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence" "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_file_query`, `imported_slack_steps`, `imported_relu_aux_steps`, `imported_introduced_query`, `imported_projection`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_introductions_match`, `imported_projection_checked`, `imported_file_query_unsatisfiable`.

### [Imported_Marabou_Example_Preprocess_Split_Unsat](../Isabelle/Imported_Marabou_Example_Preprocess_Split_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Preprocessed_Split_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Preprocessed_Eliminate_Unsat](../Isabelle/Imported_Marabou_Preprocessed_Eliminate_Unsat.thy)

Imports: "Marabou_Verification.Preprocessing_Projection" "Marabou_Verification.Inequality_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence" "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_source_query`, `imported_source_column_query`, `imported_steps`, `imported_query`, `imported_certificate`, `imported_file_query`, `imported_slack_steps`, `imported_relu_aux_steps`, `imported_introduced_query`, `imported_projection`.

Results: `imported_source_term_order`, `imported_steps_match_query`, `imported_certificate_checked`, `imported_query_unsatisfiable`, `imported_source_certificate_checked`, `imported_source_equisatisfiable`, `imported_source_query_unsatisfiable`, `imported_introductions_match`, `imported_projection_checked`, `imported_file_query_unsatisfiable`.

### [Imported_Marabou_Example_Preprocess_Eliminate_Unsat](../Isabelle/Imported_Marabou_Example_Preprocess_Eliminate_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Preprocessed_Eliminate_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Preprocessed_Inequality_Unsat](../Isabelle/Imported_Marabou_Preprocessed_Inequality_Unsat.thy)

Imports: "Marabou_Verification.Preprocessing_Projection" "Marabou_Verification.Inequality_Auxiliary_Sequence" "Marabou_Verification.ReLU_Auxiliary_Sequence" "Marabou_Verification.Tableau_Auxiliary_Sequence".

Objects: `imported_file_query`, `imported_slack_steps`, `imported_relu_aux_steps`, `imported_introduced_query`, `imported_crossing_query`, `imported_projection`.

Results: `imported_introductions_match`, `imported_crossing_query_unsatisfiable`, `imported_projection_checked`, `imported_file_query_unsatisfiable`.

### [Imported_Marabou_Example_Preprocess_Inequality_Unsat](../Isabelle/Imported_Marabou_Example_Preprocess_Inequality_Unsat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Preprocessed_Inequality_Unsat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_unsatisfiable`.

### [Imported_Marabou_Preprocessed_Mixed_Sat](../Isabelle/Imported_Marabou_Preprocessed_Mixed_Sat.thy)

Imports: "Marabou_Verification.Rational_Assignment".

Objects: `imported_file_query`, `imported_assignment`.

Results: `imported_file_assignment_checked`, `imported_file_query_model`.

### [Imported_Marabou_Example_Preprocess_Mixed_Sat](../Isabelle/Imported_Marabou_Example_Preprocess_Mixed_Sat.thy)

Imports: "Marabou_Verification.Exact_Query_Format" Imported_Marabou_Preprocessed_Mixed_Sat.

Objects: `query_file`.

Results: `query_file_decodes_like_capture`, `query_file_decodes`, `query_file_model`, `query_file_satisfiable`.
