theory Rational_Linear_Implication_Examples
  imports Rational_Proof_Trees
begin

text \<open>
  x0 = 2*x2 - x3, with -1/2 \<le> x2 \<le> 1/2 and 1/2 \<le> x3 \<le> 3/2.
  Duplicate occurrences of x0 exercise exact coefficient collection.
\<close>

definition implication_query :: rat_query where
  "implication_query = \<lparr>
     rat_linear_atoms = [RatEq (RatExpr 0 [(1/2, 0), (1/2, 0), (-2, 2), (1, 3)]) 0],
     rat_query_bounds = [RatUpper 2 (1/2), RatLower 3 (1/2),
                         RatLower 2 (-1/2), RatUpper 3 (3/2)],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma upper_implication_checked:
  "check_linear_bound implication_query (RatUpper 0 (1/2)) [1, 0, 2, 1, 0, 0]"
  by code_simp

lemma lower_implication_checked:
  "check_linear_bound implication_query (RatLower 0 (-5/2)) [0, 1, 0, 0, 2, 1]"
  by code_simp

lemma general_linear_implication_checked:
  "check_linear_implication implication_query (RatExpr (-1) [(1, 0), (1, 2)])
     [1, 0, 3, 1, 0, 0]"
  by code_simp

lemma weaker_bound_checked:
  "check_linear_bound implication_query (RatUpper 0 (5/8)) [1, 0, 2, 1, 0, 0]"
  by code_simp

lemma stronger_bound_rejected:
  "\<not> check_linear_bound implication_query (RatUpper 0 (1/2 - 1/10^20))
     [1, 0, 2, 1, 0, 0]"
  by code_simp

lemma bad_implication_weights_rejected:
  "\<not> check_linear_bound implication_query (RatUpper 0 (1/2)) [-1, 0, 2, 1, 0, 0]"
  "\<not> check_linear_bound implication_query (RatUpper 0 (1/2)) [1, 0, 2, 1, 0]"
  "\<not> check_linear_bound implication_query (RatUpper 0 (1/2)) [1, 0, 2, 1, 0, 0, 0]"
  "\<not> check_linear_bound implication_query (RatUpper 0 (1/2)) [1, 0, 1, 1, 0, 0]"
  by code_simp+

lemma implication_query_has_model:
  "satisfies_query (\<lambda>_. 1/2) (embed_query implication_query)"
  by (simp add: implication_query_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def of_rat_divide of_rat_minus)

lemma implication_query_rejects_every_unsat_certificate:
  "\<not> check_certificate implication_query cert"
  by (rule check_certificate_rejects_model[OF implication_query_has_model])

lemma implication_is_not_itself_a_contradiction:
  "\<not> check_linear_leaf implication_query [1, 0, 2, 1, 0, 0]"
  by code_simp

lemma unconditional_constant_targets:
  "check_linear_implication implication_query (RatExpr (-1) []) [0, 0, 0, 0, 0, 0]"
  "check_linear_implication implication_query (RatExpr 0 []) [0, 0, 0, 0, 0, 0]"
  "\<not> check_linear_implication implication_query (RatExpr 1 []) [0, 0, 0, 0, 0, 0]"
  by code_simp+

definition explained_relu_query :: rat_query where
  "explained_relu_query = rat_add_bound implication_query (RatLower 1 (3/4))"

definition explained_relu_certificate :: certificate where
  "explained_relu_certificate =
     Linear_Bound (RatUpper 0 (1/2)) [1, 0, 0, 2, 1, 0, 0]
       (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [0, 0, 1, 0, 1, 0, 0, 0, 0]))"

lemma explained_relu_checked:
  "check_certificate explained_relu_query explained_relu_certificate"
  by code_simp

theorem explained_relu_unsatisfiable:
  "unsatisfiable (embed_query explained_relu_query)"
  by (rule check_certificate_sound[OF explained_relu_checked])

lemma unexplained_premise_rejected:
  "\<not> check_certificate explained_relu_query
     (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [0, 0, 1, 1, 0, 0, 0, 0]))"
  by code_simp

lemma forged_linear_step_rejected:
  "\<not> check_certificate explained_relu_query
     (Linear_Bound (RatUpper 0 (1/4)) [1, 0, 0, 2, 1, 0, 0]
       (Relu_Upper 0 1 (1/4) (1/4) (Linear_Unsat [0, 0, 1, 0, 1, 0, 0, 0, 0])))"
  by code_simp

lemma linear_step_requires_checked_continuation:
  "\<not> check_certificate explained_relu_query
     (Linear_Bound (RatUpper 0 (1/2)) [1, 0, 0, 2, 1, 0, 0]
       (Linear_Unsat [0, 0, 0, 0, 0, 0, 0, 0]))"
  by code_simp

text \<open>The linear relaxation has a model; the ReLU step is essential here.\<close>

lemma explained_relu_linear_relaxation_has_model:
  "satisfies_query (\<lambda>x. if x = 1 then 3/4 else 1/2)
     (embed_query (explained_relu_query\<lparr>rat_relu_atoms := []\<rparr>))"
  by (simp add: explained_relu_query_def implication_query_def rat_add_bound_def
      embed_query_def satisfies_query_def of_rat_divide of_rat_minus)

end
