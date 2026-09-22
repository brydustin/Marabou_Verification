theory Rational_Proof_Tree_Examples
  imports Rational_Proof_Trees Rational_Linear_Examples
begin

definition tree_query :: rat_query where
  "tree_query = \<lparr>
     rat_linear_atoms = [RatGe (RatExpr 0 [(1, 1)]) 1],
     rat_query_bounds = [RatUpper 0 0], rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition tree_certificate :: certificate where
  "tree_certificate = Relu_Split 0 1
     (Linear_Unsat [1, 0, 1, 0, 1]) (Linear_Unsat [1, 0, 1, 0, 0])"

lemma tree_certificate_checked: "check_certificate tree_query tree_certificate"
  by code_simp

lemma embed_tree_query: "embed_query tree_query = unsat_example"
  by (simp add: embed_query_def tree_query_def unsat_example_def var_expr_def)

theorem unsat_example_via_recursive_certificate: "unsatisfiable unsat_example"
  using check_certificate_sound[OF tree_certificate_checked]
  by (simp only: embed_tree_query)

text \<open>
  A second, independent ReLU forces a genuinely nested tree. After either
  phase of ReLU 2 3, both phases of ReLU 0 1 close with the same contradiction.
  The additional phase equation and bound receive zero weights.
\<close>

definition nested_query :: rat_query where
  "nested_query = tree_query\<lparr>rat_relu_atoms := [ReLU 2 3, ReLU 0 1]\<rparr>"

definition nested_subtree :: certificate where
  "nested_subtree = Relu_Split 0 1
     (Linear_Unsat [1, 0, 0, 0, 1, 0, 0, 1])
     (Linear_Unsat [1, 0, 0, 0, 1, 0, 0, 0])"

lemma nested_tree_checked:
  "check_certificate nested_query (Relu_Split 2 3 nested_subtree nested_subtree)"
  by code_simp

theorem nested_query_unsatisfiable: "unsatisfiable (embed_query nested_query)"
  by (rule check_certificate_sound[OF nested_tree_checked])

lemma absent_relu_rejected:
  "\<not> check_certificate
     (fractional_bounds\<lparr>rat_relu_atoms := []\<rparr>)
     (Relu_Split 0 1 (Linear_Unsat [0, 0, 0, 1, 1])
                     (Linear_Unsat [0, 0, 0, 1, 1]))"
  by code_simp

lemma one_bad_child_rejected:
  "\<not> check_certificate tree_query
     (Relu_Split 0 1 (Linear_Unsat [1, 0, 1, 0, 1]) (Linear_Unsat [0, 0, 0, 0, 0]))"
  by code_simp

lemma repeated_split_rejected:
  "\<not> check_certificate tree_query (Relu_Split 0 1 tree_certificate tree_certificate)"
  by code_simp

lemma satisfiable_query_rejects_every_tree: "\<not> check_certificate sign_test cert"
  by (rule check_certificate_rejects_model[OF sign_test_model])

end
