theory Solver_ReLU_Examples
  imports Imported_Marabou_Solver_Relu
begin

text \<open>
  The captured query needs a nonlinear inference: its linear relaxation has a
  real model. b=z=-1/2, f=w=1/4, aux=3/4, and the three tableau slacks are zero.
  Source: tools/solver_capture/capture.cpp; native row order and auxiliary
  introduction are documented in notes/SOLVER_RELU_CAPTURE.md.
\<close>

definition captured_linear_relaxation :: rat_query where
  "captured_linear_relaxation =
    imported_query\<lparr>rat_relu_atoms := []\<rparr>"

definition captured_relaxation_witness :: valuation where
  "captured_relaxation_witness x =
    (if x = 0 \<or> x = 2 then -1/2
     else if x = 1 \<or> x = 3 then 1/4
     else if x = 4 then 3/4 else 0)"

lemma captured_linear_relaxation_has_model:
  "satisfies_query captured_relaxation_witness
    (embed_query captured_linear_relaxation)"
  by (simp add: captured_linear_relaxation_def captured_relaxation_witness_def
      imported_query_def embed_query_def satisfies_query_def
      of_rat_divide of_rat_minus)

theorem captured_linear_relaxation_satisfiable:
  "satisfiable (embed_query captured_linear_relaxation)"
  using captured_linear_relaxation_has_model
  unfolding satisfiable_def by blast

lemma captured_linear_relaxation_rejects_every_certificate:
  "\<not> check_certificate captured_linear_relaxation cert"
  by (rule check_certificate_rejects_model[OF captured_linear_relaxation_has_model])

text \<open>
  Linear leaves ignore ReLU atoms, so no linear leaf alone can certify the
  captured query, even though its full imported certificate proves UNSAT.
\<close>

theorem captured_query_requires_nonlinear_evidence:
  "\<not> check_linear_leaf imported_query ws"
proof -
  have "\<not> check_linear_leaf captured_linear_relaxation ws"
    by (rule check_linear_leaf_rejects_model[OF captured_linear_relaxation_has_model])
  then show ?thesis
    by (simp add: captured_linear_relaxation_def check_linear_leaf_def normalize_query_def)
qed

end
