theory Inequality_Auxiliary_Examples
  imports Inequality_Auxiliary_Sequence Exact_Query_Format_Examples
begin

text \<open>
  Hand-written exact examples, not native captures. These exercise the two
  signed slack directions, finite composition, model projection, and the
  existing ReLU/tableau/certificate pipeline.
\<close>

definition inequality_affine_expr :: rat_linexpr where
  "inequality_affine_expr = RatExpr (1/2) [(2, 0), (-1, 0), (0, 9)]"

definition inequality_affine_query :: rat_query where
  "inequality_affine_query = \<lparr>
    rat_linear_atoms = [RatLe inequality_affine_expr (3/4),
      RatGe inequality_affine_expr 0, RatLe inequality_affine_expr (3/4),
      RatEq (RatExpr 0 [(1, 4)]) 1],
    rat_query_bounds = [RatLower 4 1, RatUpper 4 1],
    rat_relu_atoms = [ReLU 2 3]\<rparr>"

definition inequality_affine_result :: rat_query where
  "inequality_affine_result = \<lparr>
    rat_linear_atoms = [
      RatEq (RatExpr (1/2) [(2, 0), (-1, 0), (0, 9), (1, 5)]) (3/4),
      RatEq (RatExpr (1/2) [(2, 0), (-1, 0), (0, 9), (1, 6)]) 0,
      RatLe inequality_affine_expr (3/4), RatEq (RatExpr 0 [(1, 4)]) 1],
    rat_query_bounds = [RatLower 4 1, RatUpper 4 1, RatLower 5 0, RatUpper 6 0],
    rat_relu_atoms = [ReLU 2 3]\<rparr>"

lemma inequality_affine_sequence_checked:
  "rat_introduce_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)] =
    Some inequality_affine_result"
  by code_simp

lemma inequality_affine_equisatisfiable:
  "satisfiable (embed_query inequality_affine_result) \<longleftrightarrow>
    satisfiable (embed_query inequality_affine_query)"
  by (rule inequality_aux_sequence_satisfiable_iff[OF inequality_affine_sequence_checked])

lemma inequality_affine_assignment_checked:
  "check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)]
    [(4, 1), (5, 1/4), (6, -1/2)]"
  by code_simp

theorem inequality_affine_source_model:
  "satisfies_query (assignment_valuation [(4, 1), (5, 1/4), (6, -1/2)])
    (embed_query inequality_affine_query)"
  by (rule check_assignment_after_inequality_aux_sequence_sound[OF inequality_affine_assignment_checked])

lemma inequality_zero_slack_boundary:
  "check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)]
    [(0, 1/4), (4, 1), (5, 0), (6, -3/4)]"
  by code_simp

lemma inequality_guard_failures:
  "(\<forall>s \<in> set [0, 2, 3, 4, 9].
      rat_introduce_inequality_aux inequality_affine_query 0 s = None) \<and>
   rat_introduce_inequality_aux inequality_affine_query 3 5 = None \<and>
   rat_introduce_inequality_aux inequality_affine_query 4 5 = None \<and>
   rat_introduce_inequality_aux (inequality_affine_query\<lparr>rat_linear_atoms := []\<rparr>) 0 5 = None"
  by code_simp

lemma inequality_late_failures:
  "rat_introduce_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 5)] = None \<and>
   rat_introduce_inequality_aux_sequence inequality_affine_query [(0, 5), (0, 6)] = None \<and>
   rat_introduce_inequality_aux_sequence inequality_affine_query [(0, 5), (7, 6)] = None \<and>
   \<not> check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 5)]
     [(4, 1), (5, 1/4), (6, -1/2)]"
  by code_simp

lemma inequality_incorrect_assignments_rejected:
  "\<not> check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)]
      [(4, 1), (5, 1/4), (6, 1/2)] \<and>
   \<not> check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)]
      [(4, 1)] \<and>
   \<not> check_assignment_after_inequality_aux_sequence inequality_affine_query [(0, 5), (1, 6)]
      [(4, 1), (5, 1/4), (5, 1/4), (6, -1/2)]"
  by code_simp

lemma inequality_affine_rejects_all_unsat_certificates:
  "\<not> check_after_inequality_aux_sequence inequality_affine_query steps relu_steps tableau_steps cert"
  by (rule check_after_inequality_aux_sequence_rejects_model[OF inequality_affine_source_model])

definition inequality_unsat_query :: rat_query where
  "inequality_unsat_query = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0)]) 0, RatGe (RatExpr 0 [(1, 0)]) 1],
    rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

lemma inequality_unsat_checked:
  "check_after_inequality_aux_sequence inequality_unsat_query [(0, 1), (1, 2)] [] []
    (Linear_Unsat [1, 0, 0, 1, 1, 1])"
  by code_simp

theorem inequality_source_unsatisfiable:
  "unsatisfiable (embed_query inequality_unsat_query)"
  by (rule check_after_inequality_aux_sequence_sound[OF inequality_unsat_checked])

lemma inequality_bad_steps_and_leaf_rejected:
  "\<not> check_after_inequality_aux_sequence inequality_unsat_query [(0, 0), (1, 2)] [] []
      (Linear_Unsat [1, 0, 0, 1, 1, 1]) \<and>
   \<not> check_after_inequality_aux_sequence inequality_unsat_query [(0, 1), (1, 1)] [] []
      (Linear_Unsat [1, 0, 0, 1, 1, 1]) \<and>
   \<not> check_after_inequality_aux_sequence inequality_unsat_query [(0, 1), (1, 2)] [] []
      (Linear_Unsat [])"
  by code_simp

text \<open>
  Without freshness, reusing a variable constrained only by an unrelated
  bound would create a false contradiction. The unchecked raw operation
  demonstrates the failure, while the guarded executable step rejects it.
\<close>

definition inequality_collision_query :: rat_query where
  "inequality_collision_query = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0)]) 0],
    rat_query_bounds = [RatUpper 1 (-1)], rat_relu_atoms = []\<rparr>"

lemma inequality_collision_model:
  "check_rat_assignment inequality_collision_query [(1, -1)]"
  by code_simp

lemma inequality_collision_raw_contradiction:
  "check_certificate
    (rat_inequality_aux_query inequality_collision_query 0 1 Slack_Le (RatExpr 0 [(1, 0)]) 0)
    (Linear_Unsat [0, 0, 1, 1])"
  by code_simp

lemma inequality_collision_guard_rejects:
  "rat_introduce_inequality_aux inequality_collision_query 0 1 = None"
  by code_simp

theorem inequality_collision_cannot_be_certified:
  "\<not> check_after_inequality_aux_sequence inequality_collision_query steps relu_steps tableau_steps cert"
  by (rule check_after_inequality_aux_sequence_rejects_model[
        OF check_rat_assignment_sound[OF inequality_collision_model]])

text \<open>
  For GE, the native +1 coefficient needs a NONPOSITIVE slack. Reversing
  that bound would turn the satisfiable x=2, x>=1 query into a contradiction.
\<close>

definition inequality_ge_sign_query :: rat_query where
  "inequality_ge_sign_query = \<lparr>
    rat_linear_atoms = [RatGe (RatExpr 0 [(1, 0)]) 1],
    rat_query_bounds = [RatLower 0 2, RatUpper 0 2], rat_relu_atoms = []\<rparr>"

lemma inequality_ge_negative_slack_model:
  "check_assignment_after_inequality_aux_sequence inequality_ge_sign_query [(0, 1)]
    [(0, 2), (1, -1)]"
  by code_simp

lemma inequality_ge_wrong_sign_would_contradict:
  "check_certificate
    (rat_inequality_aux_query inequality_ge_sign_query 0 1 Slack_Le (RatExpr 0 [(1, 0)]) 1)
    (Linear_Unsat [1, 0, 1, 0, 1])"
  by code_simp

lemma inequality_ge_correct_sign_rejects_false_contradiction:
  "\<not> check_after_inequality_aux inequality_ge_sign_query 0 1 (Linear_Unsat [1, 0, 1, 0, 1])"
  by code_simp

text \<open>
  Compose two inequality replacements, a ReLU introduction, three scalar-fixed
  introductions, an explained input upper bound and ReLU output propagation.
  These coefficients are hand-written checked evidence, not a solver run.
\<close>

definition inequality_relu_query :: rat_query where
  "inequality_relu_query = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0)]) (-1), RatGe (RatExpr 0 [(1, 1)]) 1],
    rat_query_bounds = [RatLower 0 (-2), RatUpper 0 2, RatLower 1 0, RatUpper 1 2],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition inequality_relu_certificate :: certificate where
  "inequality_relu_certificate =
    Linear_Bound (RatUpper 0 (-1)) (map (\<lambda>i. if i \<in> set [0, 10, 15] then 1 else 0) [0..<20])
      (Relu_Upper 0 1 (-1) 0
        (Linear_Unsat (map (\<lambda>i. if i \<in> set [3, 6, 13, 18] then 1 else 0) [0..<22])))"

lemma inequality_relu_pipeline_checked:
  "check_after_inequality_aux_sequence inequality_relu_query [(0, 2), (1, 3)]
    [ReLU_Aux_Step 0 1 4 (Some (-2))] [(0, 5), (1, 6), (2, 7)] inequality_relu_certificate"
  by code_simp

theorem inequality_relu_query_unsatisfiable:
  "unsatisfiable (embed_query inequality_relu_query)"
  by (rule check_after_inequality_aux_sequence_sound[OF inequality_relu_pipeline_checked])

lemma inequality_pipeline_later_collision_rejected:
  "\<not> check_after_inequality_aux_sequence inequality_relu_query [(0, 2), (1, 3)]
      [ReLU_Aux_Step 0 1 2 (Some (-2))] [(0, 5), (1, 6), (2, 7)] inequality_relu_certificate \<and>
   \<not> check_after_inequality_aux_sequence inequality_relu_query [(0, 2), (1, 3)]
      [ReLU_Aux_Step 0 1 4 (Some (-2))] [(0, 5), (1, 5), (2, 7)] inequality_relu_certificate"
  by code_simp

lemma inequality_relu_linear_relaxation_has_model:
  "check_rat_assignment (inequality_relu_query\<lparr>rat_relu_atoms := []\<rparr>) [(0, -1), (1, 1)]"
  by code_simp

theorem inequality_relu_needs_nonlinear_evidence:
  "\<not> check_linear_leaf inequality_relu_query weights"
proof -
  have model: "satisfies_query (assignment_valuation [(0, -1), (1, 1)])
      (embed_query (inequality_relu_query\<lparr>rat_relu_atoms := []\<rparr>))"
    by (rule check_rat_assignment_sound[OF inequality_relu_linear_relaxation_has_model])
  have "\<not> check_linear_leaf (inequality_relu_query\<lparr>rat_relu_atoms := []\<rparr>) weights"
    by (rule check_linear_leaf_rejects_model[OF model])
  then show ?thesis by (simp add: check_linear_leaf_def normalize_query_def)
qed

text \<open>
  The HOL byte decoder already supports inequalities. The native file
  workflow still rejects them; this hand-written decoded example claims
  only the mathematical transformation and exact certificate theorem.
\<close>

lemma inequality_text_decodes:
  "decode_query (text_lines [''marabou-exact-query-v1'', ''le 1 x0 <= 0'', ''ge 1 x0 >= 1'']) =
    Some inequality_unsat_query"
  by code_simp

theorem inequality_text_unsatisfiable:
  assumes "decode_query
    (text_lines [''marabou-exact-query-v1'', ''le 1 x0 <= 0'', ''ge 1 x0 >= 1'']) = Some Q"
  shows "unsatisfiable (embed_query Q)"
  using assms inequality_text_decodes inequality_source_unsatisfiable by simp

end
