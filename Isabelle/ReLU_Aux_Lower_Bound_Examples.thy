theory ReLU_Aux_Lower_Bound_Examples
  imports Imported_Marabou_Source_Relu_Aux_Inactive
begin

definition aux_lower_query :: "rat \<Rightarrow> rat \<Rightarrow> rat_query" where
  "aux_lower_query l minimum_output = \<lparr>
    rat_linear_atoms = [RatEq (relu_aux_expr 0 1 2) 0],
    rat_query_bounds = [RatLower 2 l, RatLower 1 minimum_output],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition aux_lower_certificate :: "rat \<Rightarrow> rat \<Rightarrow> certificate" where
  "aux_lower_certificate l u =
    Relu_Aux_Lower_Output_Upper 0 1 2 l u [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 1, 0, 1])"

lemma positive_aux_certificate_checked:
  "check_certificate (aux_lower_query (1/2) (1/4)) (aux_lower_certificate (1/2) 0)"
  by code_simp

theorem positive_aux_query_unsatisfiable:
  "unsatisfiable (embed_query (aux_lower_query (1/2) (1/4)))"
  by (rule check_certificate_sound[OF positive_aux_certificate_checked])

lemma aux_rule_accepts_weaker_conclusion:
  "check_certificate (aux_lower_query (1/2) (1/4)) (aux_lower_certificate (1/2) (1/8))"
  by code_simp

lemma aux_rule_rejects_insufficient_weaker_conclusion:
  "\<not> check_certificate (aux_lower_query (1/2) (1/4)) (aux_lower_certificate (1/2) (1/4))"
  by code_simp

lemma aux_rule_accepts_exact_tiny_positive_premise:
  "check_certificate (aux_lower_query (1 / 100000000000000000000) (1/4))
    (aux_lower_certificate (1 / 100000000000000000000) 0)"
  by code_simp

text \<open>
  A positive auxiliary alone is not an UNSAT claim: x=-1/2, y=0 and a=1/2
  is a model when the output is only constrained to be nonnegative.
\<close>

lemma positive_aux_satisfiable_model:
  "satisfies_query (\<lambda>i. if i = 0 then -1/2 else if i = 2 then 1/2 else 0)
    (embed_query (aux_lower_query (1/2) 0))"
  by (simp add: aux_lower_query_def relu_aux_expr_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def of_rat_divide)

theorem positive_aux_sat_query_rejects_all_certificates:
  "\<not> check_certificate (aux_lower_query (1/2) 0) cert"
  by (rule check_certificate_rejects_model[OF positive_aux_satisfiable_model])

text \<open>
  Zero is different: x=y=1 and a=0 satisfy the ReLU and auxiliary equation.
  Unsoundly adding y<=0 gives a checked linear contradiction.
  The guarded auxiliary rule therefore requires strict positivity.
\<close>

lemma zero_aux_countermodel:
  "satisfies_query (\<lambda>i. if i = 0 \<or> i = 1 then 1 else 0)
    (embed_query (aux_lower_query 0 1))"
  by (simp add: aux_lower_query_def relu_aux_expr_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def)

lemma zero_aux_raw_bound_creates_contradiction:
  "check_certificate (rat_add_bound (aux_lower_query 0 1) (RatUpper 1 0))
    (Linear_Unsat [0, 0, 1, 0, 1])"
  by code_simp

lemma aux_rule_rejects_nonpositive_premises:
  "\<not> check_certificate (aux_lower_query 0 1) (aux_lower_certificate 0 0) \<and>
   \<not> check_certificate (aux_lower_query (-1 / 100000000000000000000) 1)
      (aux_lower_certificate (-1 / 100000000000000000000) 0)"
  by code_simp

theorem zero_aux_query_rejects_every_certificate:
  "\<not> check_certificate (aux_lower_query 0 1) cert"
  by (rule check_certificate_rejects_model[OF zero_aux_countermodel])

lemma aux_rule_rejects_stronger_conclusion:
  "\<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) 0) 0 1 2
    (1/2) (-1 / 100000000000000000000) [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

text \<open>
  The premise must be the stated AUXILIARY lower bound. Output or input
  lower bounds, an auxiliary upper bound, or a different value reject.
\<close>

lemma aux_rule_rejects_wrong_or_absent_premise:
  "\<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) (1/4)) 0 1 2
      (3/4) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound
      ((aux_lower_query (1/2) (1/4))\<lparr>rat_query_bounds :=
        [RatLower 1 (1/2), RatLower 2 0]\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound
      ((aux_lower_query (1/2) (1/4))\<lparr>rat_query_bounds :=
        [RatLower 0 (1/2), RatLower 1 (1/4)]\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound
      ((aux_lower_query (1/2) (1/4))\<lparr>rat_query_bounds :=
        [RatUpper 2 (1/2), RatLower 1 (1/4)]\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma aux_rule_needs_both_equation_witnesses:
  "\<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) (1/4)) 0 1 2
      (1/2) 0 [0, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) (1/4)) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 0, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound
      ((aux_lower_query (1/2) (1/4))\<lparr>rat_linear_atoms := []\<rparr>) 0 1 2
      (1/2) 0 [0, 0] [0, 0]"
  by code_simp

lemma aux_rule_rejects_wrong_variables_or_missing_relu:
  "\<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) (1/4)) 0 1 3
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound (aux_lower_query (1/2) (1/4)) 1 0 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0] \<and>
   \<not> check_relu_aux_lower_output_upper_bound
      ((aux_lower_query (1/2) (1/4))\<lparr>rat_relu_atoms := []\<rparr>) 0 1 2
      (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma aux_rule_needs_checked_continuation:
  "\<not> check_certificate (aux_lower_query (1/2) (1/4))
    (Relu_Aux_Lower_Output_Upper 0 1 2 (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 0, 0, 0]))"
  by code_simp

lemma output_rule_cannot_use_auxiliary_premise:
  "\<not> check_certificate (aux_lower_query (1/2) (1/4))
    (Relu_Output_Aux_Upper 0 1 2 (1/2) 0 [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 1, 0, 1]))"
  by code_simp

text \<open>
  The native capture's processed query needs nonlinear evidence: dropping
  its ReLU leaves the model a=w=f=t=1/4, b=0, all tableau slacks zero.
  Variables: a=x0, b=x1, f=x2, w=x3, t=x4; slacks x5..x7.
\<close>

definition captured_inactive_relaxation :: rat_query where
  "captured_inactive_relaxation = imported_query\<lparr>rat_relu_atoms := []\<rparr>"

lemma captured_inactive_relaxation_has_model:
  "satisfies_query (\<lambda>i. if i = 0 \<or> i = 2 \<or> i = 3 \<or> i = 4 then 1/4 else 0)
    (embed_query captured_inactive_relaxation)"
  by (simp add: captured_inactive_relaxation_def imported_query_def embed_query_def
      satisfies_query_def of_rat_divide of_rat_minus)

theorem captured_inactive_query_requires_nonlinear_evidence:
  "\<not> check_linear_leaf imported_query ws"
proof -
  have "\<not> check_linear_leaf captured_inactive_relaxation ws"
    by (rule check_linear_leaf_rejects_model[OF captured_inactive_relaxation_has_model])
  then show ?thesis
    by (simp add: captured_inactive_relaxation_def check_linear_leaf_def normalize_query_def)
qed

text \<open>
  Relaxing only w>=1/4 to w>=0 keeps the ReLU but admits a=w=0 and
  b=f=t=1/4. No checked introduction sequence and certificate accepts it.
\<close>

definition relaxed_inactive_source :: rat_query where
  "relaxed_inactive_source = imported_source_column_query\<lparr>rat_query_bounds :=
    [RatLower 0 0, RatUpper 0 2, RatLower 1 (-2), RatUpper 1 2, RatLower 2 0, RatUpper 2 2,
     RatLower 3 0, RatUpper 3 2, RatLower 4 (1/4), RatUpper 4 2]\<rparr>"

lemma relaxed_inactive_source_has_model:
  "satisfies_query (\<lambda>i. if i = 1 \<or> i = 2 \<or> i = 4 then 1/4 else 0)
    (embed_query relaxed_inactive_source)"
  by (simp add: relaxed_inactive_source_def imported_source_column_query_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def of_rat_divide of_rat_minus)

theorem relaxed_inactive_source_rejects_all_sequence_certificates:
  "\<not> check_after_fixed_aux_sequence relaxed_inactive_source steps cert"
  by (rule check_after_fixed_aux_sequence_rejects_model[OF relaxed_inactive_source_has_model])

end
