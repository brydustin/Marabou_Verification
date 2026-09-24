theory ReLU_Output_Bound_Examples
  imports Imported_Marabou_Native_Relu_Chain
begin

definition output_aux_query :: "rat \<Rightarrow> rat \<Rightarrow> rat_query" where
  "output_aux_query l minimum_aux = \<lparr>
    rat_linear_atoms = [RatEq (relu_aux_expr 0 1 2) 0],
    rat_query_bounds = [RatLower 1 l, RatLower 2 minimum_aux],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition output_aux_certificate :: "rat \<Rightarrow> rat \<Rightarrow> certificate" where
  "output_aux_certificate l u =
    Relu_Output_Aux_Upper 0 1 2 l u [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 1, 0, 1])"

lemma positive_output_certificate_checked:
  "check_certificate (output_aux_query (1/2) (1/4)) (output_aux_certificate (1/2) 0)"
  by code_simp

theorem positive_output_query_unsatisfiable:
  "unsatisfiable (embed_query (output_aux_query (1/2) (1/4)))"
  by (rule check_certificate_sound[OF positive_output_certificate_checked])

lemma output_rule_accepts_weaker_conclusion:
  "check_certificate (output_aux_query (1/2) (1/4)) (output_aux_certificate (1/2) (1/8))"
  by code_simp

lemma output_rule_accepts_exact_tiny_positive_premise:
  "check_certificate (output_aux_query (1 / 100000000000000000000) (1/4))
    (output_aux_certificate (1 / 100000000000000000000) 0)"
  by code_simp

text \<open>
  Positive output alone is not an UNSAT claim: y=x=1/2 and a=0 is a model
  when the auxiliary is only constrained to be nonnegative.
\<close>

lemma positive_output_satisfiable_model:
  "satisfies_query (\<lambda>i. if i = 0 \<or> i = 1 then 1/2 else 0)
    (embed_query (output_aux_query (1/2) 0))"
  by (simp add: output_aux_query_def relu_aux_expr_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def of_rat_divide)

theorem positive_output_sat_query_rejects_all_certificates:
  "\<not> check_certificate (output_aux_query (1/2) 0) cert"
  by (rule check_certificate_rejects_model[OF positive_output_satisfiable_model])

text \<open>
  Zero is different: x=-1, y=0, a=1 satisfies the ReLU and auxiliary
  equation. Unsoundly adding a<=0 gives a checked linear contradiction.
  The guarded output rule therefore requires strict positivity.
\<close>

lemma zero_output_countermodel:
  "satisfies_query (\<lambda>i. if i = 0 then -1 else if i = 2 then 1 else 0)
    (embed_query (output_aux_query 0 1))"
  by (simp add: output_aux_query_def relu_aux_expr_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def)

lemma zero_output_raw_bound_creates_contradiction:
  "check_certificate (rat_add_bound (output_aux_query 0 1) (RatUpper 2 0))
    (Linear_Unsat [0, 0, 1, 0, 1])"
  by code_simp

lemma output_rule_rejects_nonpositive_premises:
  "\<not> check_certificate (output_aux_query 0 1) (output_aux_certificate 0 0) \<and>
   \<not> check_certificate (output_aux_query (-1 / 100000000000000000000) 1)
      (output_aux_certificate (-1 / 100000000000000000000) 0)"
  by code_simp

theorem zero_output_query_rejects_every_certificate:
  "\<not> check_certificate (output_aux_query 0 1) cert"
  by (rule check_certificate_rejects_model[OF zero_output_countermodel])

lemma output_rule_rejects_stronger_conclusion:
  "\<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) 0) 0 1 2
    (1/2) (-1 / 100000000000000000000) [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma output_rule_rejects_wrong_or_absent_premise:
  "\<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) (1/4)) 0 1 2
      (3/4) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound
      ((output_aux_query (1/2) (1/4))\<lparr>rat_query_bounds :=
        [RatLower 0 (1/2), RatLower 2 (1/4)]\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound
      ((output_aux_query (1/2) (1/4))\<lparr>rat_query_bounds :=
        [RatUpper 1 (1/2), RatLower 2 (1/4)]\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma output_rule_needs_both_equation_witnesses:
  "\<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) (1/4)) 0 1 2
      (1/2) 0 [0, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) (1/4)) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 0, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound
      ((output_aux_query (1/2) (1/4))\<lparr>rat_linear_atoms := []\<rparr>) 0 1 2
      (1/2) 0 [0, 0] [0, 0]"
  by code_simp

lemma output_rule_rejects_wrong_variables_or_missing_relu:
  "\<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) (1/4)) 0 1 3
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound (output_aux_query (1/2) (1/4)) 1 0 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_output_aux_upper_bound
      ((output_aux_query (1/2) (1/4))\<lparr>rat_relu_atoms := []\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma output_rule_needs_checked_continuation:
  "\<not> check_certificate (output_aux_query (1/2) (1/4))
    (Relu_Output_Aux_Upper 0 1 2 (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 0, 0, 0]))"
  by code_simp

text \<open>
  The native chained query is UNSAT through the complete imported proof.
  A coherent relaxation w>=0 has a real model; this rules out every accepted
  ReLU/tableau-sequence certificate for that relaxed source.
\<close>

definition relaxed_chain_source :: rat_query where
  "relaxed_chain_source = imported_before_relu_query\<lparr>rat_query_bounds :=
    [RatLower 0 (-2), RatUpper 0 2, RatLower 1 0, RatUpper 1 2,
     RatLower 2 (-2), RatUpper 2 2, RatLower 3 0, RatUpper 3 2,
     RatLower 4 (-2), RatUpper 4 (-1/2), RatLower 5 0, RatUpper 5 2]\<rparr>"

lemma relaxed_chain_has_model:
  "satisfies_query (\<lambda>i. if i = 0 \<or> i = 4 then -1/2 else if i = 2 then -1/4 else 0)
    (embed_query relaxed_chain_source)"
  by (simp add: relaxed_chain_source_def imported_before_relu_query_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def of_rat_divide of_rat_minus)

theorem relaxed_chain_rejects_all_sequence_certificates:
  "\<not> check_after_relu_aux_sequence relaxed_chain_source relu_steps tableau_steps cert"
  by (rule check_after_relu_aux_sequence_rejects_model[OF relaxed_chain_has_model])

end
