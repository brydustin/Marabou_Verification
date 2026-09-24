theory Bounded_Inequality_Examples
  imports Bounded_Inequality_Auxiliary
begin

definition bounded_le_query :: rat_query where
  "bounded_le_query = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0)]) 0],
    rat_query_bounds = [RatLower 0 (-1), RatUpper 0 (-1)],
    rat_relu_atoms = []\<rparr>"

definition bounded_ge_query :: rat_query where
  "bounded_ge_query = \<lparr>
    rat_linear_atoms = [RatGe (RatExpr 0 [(1, 0)]) 0],
    rat_query_bounds = [RatLower 0 1, RatUpper 0 1],
    rat_relu_atoms = []\<rparr>"

lemma finite_slack_caps_accepted:
  "rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 1 1 [1, 0, 1, 0, 0]) \<noteq> None \<and>
   rat_introduce_bounded_inequality_aux bounded_ge_query
      (Bounded_Inequality_Step 0 1 (-1) [0, 1, 0, 1, 0]) \<noteq> None"
  by code_simp

lemma weaker_slack_caps_accepted:
  "rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 1 2 [1, 0, 1, 0, 0]) \<noteq> None \<and>
   rat_introduce_bounded_inequality_aux bounded_ge_query
      (Bounded_Inequality_Step 0 1 (-2) [0, 1, 0, 1, 0]) \<noteq> None"
  by code_simp

lemma unjustified_slack_caps_rejected:
  "rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 1 0 [1, 0, 1, 0, 0]) = None \<and>
   rat_introduce_bounded_inequality_aux bounded_ge_query
      (Bounded_Inequality_Step 0 1 0 [0, 1, 0, 1, 0]) = None"
  by code_simp

lemma bounded_slack_guard_failures:
  "rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 0 1 [1, 0, 1, 0, 0]) = None \<and>
   rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 1 1 1 [1, 0, 1, 0, 0]) = None \<and>
   rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 1 1 []) = None \<and>
   rat_introduce_bounded_inequality_aux bounded_le_query
      (Bounded_Inequality_Step 0 1 1 [-1, 0, 1, 0, 0]) = None \<and>
   rat_introduce_bounded_inequality_sequence bounded_le_query
      [Bounded_Inequality_Step 0 1 1 [1, 0, 1, 0, 0],
       Bounded_Inequality_Step 0 2 1 []] = None"
  by code_simp

text \<open>
  A finite cap cannot just be guessed. This query has the model x=-1.
  Its introduced slack is necessarily 1; adding the unjustified cap s<=0
  would admit a linear contradiction. The checked introduction rejects it.
\<close>

lemma bounded_le_assignment_checked:
  "check_rat_assignment bounded_le_query [(0, -1)]"
  by code_simp

theorem bounded_le_has_model:
  "satisfies_query (assignment_valuation [(0, -1)]) (embed_query bounded_le_query)"
  by (rule check_rat_assignment_sound[OF bounded_le_assignment_checked])

lemma unchecked_cap_would_admit_false_contradiction:
  "check_certificate
    (rat_add_bound
      (rat_inequality_aux_query bounded_le_query 0 1 Slack_Le (RatExpr 0 [(1, 0)]) 0)
      (RatUpper 1 0))
    (Linear_Unsat [0, 1, 1, 0, 1, 0])"
  by code_simp

theorem bounded_le_checked_sequence_cannot_create_unsat:
  assumes "rat_introduce_bounded_inequality_sequence bounded_le_query steps = Some R"
  shows "\<not> unsatisfiable (embed_query R)"
  using bounded_inequality_sequence_satisfiable_iff[OF assms] bounded_le_has_model
  unfolding unsatisfiable_def satisfiable_def by blast

end
