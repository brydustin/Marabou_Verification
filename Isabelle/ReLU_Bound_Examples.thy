theory ReLU_Bound_Examples
  imports Rational_Proof_Trees
begin

definition negative_upper_query :: rat_query where
  "negative_upper_query = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatUpper 0 (-1/2), RatLower 1 (1/4), RatUpper 1 2],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma negative_upper_checked:
  "check_certificate negative_upper_query
     (Relu_Upper 0 1 (-1/2) 0 (Linear_Unsat [1, 0, 1, 0]))"
  by code_simp

theorem negative_upper_unsatisfiable: "unsatisfiable (embed_query negative_upper_query)"
  by (rule check_certificate_sound[OF negative_upper_checked])

definition positive_upper_query :: rat_query where
  "positive_upper_query = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatUpper 0 (1/2), RatLower 1 (3/4)],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma positive_upper_checked:
  "check_certificate positive_upper_query
     (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [1, 0, 1]))"
  by code_simp

theorem positive_upper_unsatisfiable: "unsatisfiable (embed_query positive_upper_query)"
  by (rule check_certificate_sound[OF positive_upper_checked])

lemma weaker_conclusion_allowed:
  "check_certificate positive_upper_query
     (Relu_Upper 0 1 (1/2) (5/8) (Linear_Unsat [1, 0, 1]))"
  by code_simp

lemma zero_upper_checked:
  "check_certificate
     \<lparr>rat_linear_atoms = [], rat_query_bounds = [RatUpper 0 0, RatLower 1 (1/4)],
      rat_relu_atoms = [ReLU 0 1]\<rparr>
     (Relu_Upper 0 1 0 0 (Linear_Unsat [1, 0, 1]))"
  by code_simp

text \<open>
  These two explicit linear models show that propagation adds a useful ReLU
  consequence: the original linear relaxations alone are satisfiable.
\<close>

lemma negative_upper_linear_model:
  "satisfies_query (\<lambda>x. if x = 0 then -1/2 else 1/4)
     (embed_query (negative_upper_query\<lparr>rat_relu_atoms := []\<rparr>))"
  by (simp add: embed_query_def negative_upper_query_def satisfies_query_def
      of_rat_divide of_rat_minus)

lemma positive_upper_linear_model:
  "satisfies_query (\<lambda>x. if x = 0 then 1/2 else 3/4)
     (embed_query (positive_upper_query\<lparr>rat_relu_atoms := []\<rparr>))"
  by (simp add: embed_query_def positive_upper_query_def satisfies_query_def of_rat_divide)

definition upper_sat_query :: rat_query where
  "upper_sat_query = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatUpper 0 (1/2), RatLower 1 (1/2)],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma upper_sat_model:
  "satisfies_query (\<lambda>_. 1/2) (embed_query upper_sat_query)"
  by (simp add: embed_query_def upper_sat_query_def satisfies_query_def
      satisfies_relu_def relu_def of_rat_divide)

lemma upper_sat_rejects_every_certificate: "\<not> check_certificate upper_sat_query cert"
  by (rule check_certificate_rejects_model[OF upper_sat_model])

text \<open>
  If either the input-bound membership or the numeric guard were omitted,
  the following forged propagation could close the satisfiable query above.
\<close>

lemma forged_input_upper_rejected:
  "\<not> check_certificate upper_sat_query (Relu_Upper 0 1 0 0 (Linear_Unsat [1, 0, 1]))"
  by code_simp

lemma too_strong_output_upper_rejected:
  "\<not> check_certificate upper_sat_query
     (Relu_Upper 0 1 (1/2) (1/2 - 1/1000000) (Linear_Unsat [1, 0, 1]))"
  by code_simp

lemma negative_output_upper_rejected:
  "\<not> check_certificate negative_upper_query
     (Relu_Upper 0 1 (-1/2) (-1/1000000) (Linear_Unsat [1, 0, 1, 0]))"
  by code_simp

lemma absent_relu_upper_rejected:
  "\<not> check_certificate (positive_upper_query\<lparr>rat_relu_atoms := []\<rparr>)
     (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [1, 0, 1]))"
  by code_simp

lemma wrong_relu_direction_rejected:
  "\<not> check_certificate positive_upper_query
     (Relu_Upper 1 0 (1/2) (1/2) (Linear_Unsat [1, 0, 1]))"
  by code_simp

lemma propagation_still_requires_a_checked_child:
  "\<not> check_certificate positive_upper_query
     (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [0, 0, 0]))"
  by code_simp

definition upper_chain_query :: rat_query where
  "upper_chain_query = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatUpper 0 (1/2), RatLower 2 (3/4)],
     rat_relu_atoms = [ReLU 0 1, ReLU 1 2]\<rparr>"

lemma upper_chain_checked:
  "check_certificate upper_chain_query
     (Relu_Upper 0 1 (1/2) (1/2)
       (Relu_Upper 1 2 (1/2) (1/2) (Linear_Unsat [1, 0, 0, 1])))"
  by code_simp

theorem upper_chain_unsatisfiable: "unsatisfiable (embed_query upper_chain_query)"
  by (rule check_certificate_sound[OF upper_chain_checked])

lemma future_premise_rejected:
  "\<not> check_certificate upper_chain_query
     (Relu_Upper 1 2 (1/2) (1/2)
       (Relu_Upper 0 1 (1/2) (1/2) (Linear_Unsat [0, 1, 0, 1])))"
  by code_simp

end
