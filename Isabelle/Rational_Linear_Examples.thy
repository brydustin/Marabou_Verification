theory Rational_Linear_Examples
  imports Rational_Linear_Certificates Marabou_Examples
begin

text \<open>
  All acceptance/rejection computations use code_simp, which produces HOL
  proofs by rewriting code equations. Real-semantic conclusions then follow
  from check_linear_leaf_sound, not from trusting external execution.
\<close>

definition fractional_bounds :: rat_query where
  "fractional_bounds = \<lparr>
     rat_linear_atoms = [],
     rat_query_bounds = [RatLower 0 (1/2), RatUpper 0 (1/3)],
     rat_relu_atoms = []\<rparr>"

lemma fractional_bounds_checked:
  "check_linear_leaf fractional_bounds [1/3, 1/3]"
  by code_simp

theorem fractional_bounds_unsatisfiable:
  "unsatisfiable (embed_query fractional_bounds)"
  by (rule check_linear_leaf_sound[OF fractional_bounds_checked])

text \<open>
  The affine equality is 1/2 + (1/3)x + y + (1/6)x - y = 3/2,
  with a zero coefficient on variable 9. Thus x = 2, contradicting x \<le> 1.
  This tests fractional coefficients, nonzero constants, both equality rows,
  and cancellation of repeated, nonadjacent variables.
\<close>

definition affine_leaf :: rat_query where
  "affine_leaf = \<lparr>
     rat_linear_atoms =
       [RatEq (RatExpr (1/2) [(1/3, 0), (1, 1), (1/6, 0), (-1, 1), (0, 9)]) (3/2),
        RatLe (RatExpr 0 [(1, 0)]) 1],
     rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

lemma affine_leaf_checked: "check_linear_leaf affine_leaf [0, 2, 1]"
  by code_simp

theorem affine_leaf_unsatisfiable: "unsatisfiable (embed_query affine_leaf)"
  by (rule check_linear_leaf_sound[OF affine_leaf_checked])

definition constant_leaf :: rat_query where
  "constant_leaf = \<lparr>
     rat_linear_atoms = [RatEq (RatExpr (1/2) []) (1/3)],
     rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

lemma constant_leaf_checked: "check_linear_leaf constant_leaf [1, 0]"
  by code_simp

lemma unsplit_relus_are_allowed:
  "check_linear_leaf (fractional_bounds\<lparr>rat_relu_atoms := [ReLU 1 2]\<rparr>) [1, 1]"
  by code_simp

lemma too_few_weights_rejected: "\<not> check_linear_leaf fractional_bounds [1]"
  by code_simp

lemma too_many_weights_rejected: "\<not> check_linear_leaf fractional_bounds [1, 1, 0]"
  by code_simp

lemma zero_weights_rejected: "\<not> check_linear_leaf fractional_bounds [0, 0]"
  by code_simp

text \<open>
  Without the sign check, x \<le> 0 minus x \<le> 1 would wrongly give 1 \<le> 0.
  The zero valuation satisfies this query; the forged weights are rejected.
\<close>

definition sign_test :: rat_query where
  "sign_test = \<lparr>
     rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0)]) 0, RatLe (RatExpr 0 [(1, 0)]) 1],
     rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

lemma negative_weight_rejected: "\<not> check_linear_leaf sign_test [1, -1]"
  by code_simp

lemma sign_test_model: "satisfies_query (\<lambda>_. 0) (embed_query sign_test)"
  by (simp add: embed_query_def sign_test_def satisfies_query_def)

lemma sign_test_all_certificates_rejected: "\<not> check_linear_leaf sign_test ws"
  by (rule check_linear_leaf_rejects_model[OF sign_test_model])

text \<open>
  A small nonzero residual coefficient must not be rounded away. This query is
  satisfiable at x = -1000000 despite its positive affine constant.
\<close>

definition residual_test :: rat_query where
  "residual_test = \<lparr>
     rat_linear_atoms = [RatLe (RatExpr 1 [(1/1000000, 0)]) 0],
     rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

lemma nonzero_residual_rejected: "\<not> check_linear_leaf residual_test [1]"
  by code_simp

lemma residual_test_model:
  "satisfies_query (\<lambda>_. -1000000) (embed_query residual_test)"
  by (simp add: embed_query_def residual_test_def satisfies_query_def of_rat_divide)

definition zero_margin :: rat_query where
  "zero_margin = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatLower 0 (1/2), RatUpper 0 (1/2)], rat_relu_atoms = []\<rparr>"

lemma zero_margin_rejected: "\<not> check_linear_leaf zero_margin [1, 1]"
  by code_simp

lemma empty_query_rejected:
  "\<not> check_linear_leaf
     \<lparr>rat_linear_atoms = [], rat_query_bounds = [], rat_relu_atoms = []\<rparr> []"
  by code_simp

text \<open>
  Close the earlier ReLU example using two checked linear certificates. These
  are explicit rational versions of its existing real child queries; the
  equalities below establish the connection, rather than assuming it.
\<close>

definition active_linear_leaf :: rat_query where
  "active_linear_leaf = \<lparr>
     rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0)]) 0,
                         RatGe (RatExpr 0 [(1, 1)]) 1],
     rat_query_bounds = [RatLower 0 0, RatUpper 0 0], rat_relu_atoms = []\<rparr>"

definition inactive_linear_leaf :: rat_query where
  "inactive_linear_leaf = \<lparr>
     rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1)]) 0,
                         RatGe (RatExpr 0 [(1, 1)]) 1],
     rat_query_bounds = [RatUpper 0 0, RatUpper 0 0], rat_relu_atoms = []\<rparr>"

lemma active_linear_leaf_checked:
  "check_linear_leaf active_linear_leaf [1, 0, 1, 0, 1]"
  by code_simp

lemma inactive_linear_leaf_checked:
  "check_linear_leaf inactive_linear_leaf [1, 0, 1, 0, 0]"
  by code_simp

lemma embed_active_linear_leaf:
  "embed_query active_linear_leaf = active_split unsat_example 0 1"
  by (simp add: embed_query_def active_linear_leaf_def active_split_def unsat_example_def
      var_expr_def)

lemma embed_inactive_linear_leaf:
  "embed_query inactive_linear_leaf = inactive_split unsat_example 0 1"
  by (simp add: embed_query_def inactive_linear_leaf_def inactive_split_def unsat_example_def
      var_expr_def)

theorem unsat_example_via_leaf_certificates: "unsatisfiable unsat_example"
proof (rule unsatisfiable_relu_split[where x = 0 and y = 1])
  show "ReLU 0 1 \<in> set (relu_atoms unsat_example)"
    by (simp add: unsat_example_def)
  show "unsatisfiable (active_split unsat_example 0 1)"
    using check_linear_leaf_sound[OF active_linear_leaf_checked]
    by (simp only: embed_active_linear_leaf)
  show "unsatisfiable (inactive_split unsat_example 0 1)"
    using check_linear_leaf_sound[OF inactive_linear_leaf_checked]
    by (simp only: embed_inactive_linear_leaf)
qed

end
