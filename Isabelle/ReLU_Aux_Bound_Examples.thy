theory ReLU_Aux_Bound_Examples
  imports Imported_Marabou_Solver_Relu_Aux Imported_Marabou_Solver_Relu_Aux_Active
begin

definition aux_example :: "rat \<Rightarrow> rat_query" where
  "aux_example l = \<lparr>
     rat_linear_atoms = [RatEq (relu_aux_expr 0 1 2) 0],
     rat_query_bounds = [RatLower 0 l, RatLower 2 (max 0 (-l) + 1/4)],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition aux_certificate :: "rat \<Rightarrow> certificate" where
  "aux_certificate l = Relu_Aux_Upper 0 1 2 l (max 0 (-l))
    [1, 0, 0, 0] [0, 1, 0, 0] (Linear_Unsat [0, 0, 1, 0, 1])"

lemma auxiliary_negative_zero_positive_checked:
  "check_certificate (aux_example (-1/2)) (aux_certificate (-1/2))"
  "check_certificate (aux_example 0) (aux_certificate 0)"
  "check_certificate (aux_example (1/2)) (aux_certificate (1/2))"
  by code_simp+

theorem auxiliary_negative_unsatisfiable:
  "unsatisfiable (embed_query (aux_example (-1/2)))"
  by (rule check_certificate_sound[OF auxiliary_negative_zero_positive_checked(1)])

theorem auxiliary_zero_unsatisfiable:
  "unsatisfiable (embed_query (aux_example 0))"
  by (rule check_certificate_sound[OF auxiliary_negative_zero_positive_checked(2)])

theorem auxiliary_positive_unsatisfiable:
  "unsatisfiable (embed_query (aux_example (1/2)))"
  by (rule check_certificate_sound[OF auxiliary_negative_zero_positive_checked(3)])

lemma weaker_auxiliary_conclusion:
  "check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (5/8)
    [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma stronger_auxiliary_conclusion_rejected:
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (1/2 - 1/10^20)
    [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp

lemma auxiliary_requires_both_equation_witnesses:
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (1/2)
    [0, 0, 0, 0] [0, 1, 0, 0]"
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (1/2)
    [1, 0, 0, 0] [0, 0, 0, 0]"
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (1/2)
    [-1, 0, 0, 0] [0, 1, 0, 0]"
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 (-1/2) (1/2)
    [1, 0, 0] [0, 1, 0, 0]"
  by code_simp+

lemma auxiliary_checks_variables_and_premises:
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 3 (-1/2) (1/2)
    [1, 0, 0, 0] [0, 1, 0, 0]"
  "\<not> check_relu_aux_upper_bound (aux_example (-1/2)) 0 1 2 0 0
    [1, 0, 0, 0] [0, 1, 0, 0]"
  "\<not> check_relu_aux_upper_bound ((aux_example (-1/2))\<lparr>rat_relu_atoms := []\<rparr>)
    0 1 2 (-1/2) (1/2) [1, 0, 0, 0] [0, 1, 0, 0]"
  by code_simp+

lemma auxiliary_requires_checked_continuation:
  "\<not> check_certificate (aux_example (-1/2))
    (Relu_Aux_Upper 0 1 2 (-1/2) (1/2) [1, 0, 0, 0] [0, 1, 0, 0]
      (Linear_Unsat [0, 0, 0, 0, 0]))"
  by code_simp

text \<open>Without the auxiliary equation, a is free to exceed ReLU(-x).\<close>

lemma missing_auxiliary_equation_has_model:
  "satisfies_query (\<lambda>x. if x = 0 then -1/2 else if x = 2 then 3/4 else 0)
    (embed_query ((aux_example (-1/2))\<lparr>rat_linear_atoms := []\<rparr>))"
  by (simp add: aux_example_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def of_rat_divide of_rat_minus)

lemma missing_auxiliary_equation_rejects_every_certificate:
  "\<not> check_certificate ((aux_example (-1/2))\<lparr>rat_linear_atoms := []\<rparr>) cert"
  by (rule check_certificate_rejects_model[OF missing_auxiliary_equation_has_model])

text \<open>
  The active solver capture needs the new rule: its linear relaxation has
  b=z=1/2, f=3/4, aux=w=1/4 and all tableau slacks zero.
  The broader negative capture also checks the extra auxiliary lemma, but
  its final contradiction only needs the subsequent output-upper lemma.
\<close>

definition active_aux_relaxation :: rat_query where
  "active_aux_relaxation =
    Imported_Marabou_Solver_Relu_Aux_Active.imported_query\<lparr>rat_relu_atoms := []\<rparr>"

lemma active_aux_relaxation_has_model:
  "satisfies_query
    (\<lambda>x. if x = 0 \<or> x = 2 then 1/2 else if x = 1 then 3/4
      else if x = 3 \<or> x = 4 then 1/4 else 0)
    (embed_query active_aux_relaxation)"
  by (simp add: active_aux_relaxation_def
      Imported_Marabou_Solver_Relu_Aux_Active.imported_query_def
      embed_query_def satisfies_query_def of_rat_divide of_rat_minus)

theorem active_aux_relaxation_satisfiable:
  "satisfiable (embed_query active_aux_relaxation)"
  using active_aux_relaxation_has_model unfolding satisfiable_def by blast

theorem active_aux_capture_has_no_linear_certificate:
  "\<not> check_linear_leaf Imported_Marabou_Solver_Relu_Aux_Active.imported_query ws"
proof -
  have "\<not> check_linear_leaf active_aux_relaxation ws"
    by (rule check_linear_leaf_rejects_model[OF active_aux_relaxation_has_model])
  then show ?thesis
    by (simp add: active_aux_relaxation_def check_linear_leaf_def normalize_query_def)
qed

end
