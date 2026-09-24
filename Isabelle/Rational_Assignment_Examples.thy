theory Rational_Assignment_Examples
  imports Rational_Assignment ReLU_Output_Bound_Examples ReLU_Aux_Lower_Bound_Examples
    Imported_Marabou_Native_Relu_Sat
begin

text \<open>
  x + y = 2, -1 <= x <= 1, y = ReLU(x): the rational counterpart of
  Marabou_Examples.sat_example, with x = 0 and y = 1.
\<close>

definition sat_rat_query :: rat_query where
  "sat_rat_query = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (1, 1)]) 2],
    rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma sat_rat_assignment_checked:
  "check_rat_assignment sat_rat_query [(0, 1), (1, 1)]"
  by code_simp

theorem sat_rat_query_satisfiable:
  "satisfiable (embed_query sat_rat_query)"
  by (rule check_rat_assignment_satisfiable[OF sat_rat_assignment_checked])

lemma sat_rat_query_rejects_certificates:
  "\<not> check_certificate sat_rat_query cert"
  by (rule check_rat_assignment_excludes_certificate[OF sat_rat_assignment_checked])

text \<open>
  Extra variables are irrelevant and unlisted ones are 0. Duplicates are
  rejected even when the first occurrence would be a model. Approximate
  values, bound violations and ReLU violations reject; the last assignment
  satisfies every linear atom and bound.
\<close>

lemma assignment_extra_variables_accepted:
  "check_rat_assignment sat_rat_query [(1, 1), (7, -3), (0, 1)]"
  by code_simp

lemma assignment_rejections:
  "\<not> check_rat_assignment sat_rat_query [(0, 1), (1, 1), (0, 5)] \<and>
   \<not> check_rat_assignment sat_rat_query [(0, 1)] \<and>
   \<not> check_rat_assignment sat_rat_query [(0, 1), (1, 1 + 1 / 100000000000000000000)] \<and>
   \<not> check_rat_assignment sat_rat_query [(0, 3/2), (1, 1/2)] \<and>
   \<not> check_rat_assignment sat_rat_query [(0, -1/2), (1, 5/2)]"
  by code_simp

text \<open>
  The inactive phase: x = -1/2 and y = 0 satisfy y = ReLU(x) and x <= 0.
\<close>

definition inactive_rat_query :: rat_query where
  "inactive_rat_query = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 0), (1, 1)]) 0],
    rat_query_bounds = [RatLower 0 (-1), RatUpper 1 1],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma inactive_assignment_checked:
  "check_rat_assignment inactive_rat_query [(0, -1/2), (1, 0)] \<and>
   \<not> check_rat_assignment inactive_rat_query [(0, -1/2), (1, 1/2)]"
  by code_simp

text \<open>
  UNSAT queries admit no accepted assignment. The earlier relaxations of the
  two native UNSAT captures are instead witnessed by exact assignments.
\<close>

lemma positive_aux_query_rejects_assignments:
  "\<not> check_rat_assignment (aux_lower_query (1/2) (1/4)) \<sigma>"
  by (rule unsatisfiable_rejects_assignment[OF positive_aux_query_unsatisfiable])

lemma relaxed_inactive_source_assignment:
  "check_rat_assignment relaxed_inactive_source [(1, 1/4), (2, 1/4), (4, 1/4)]"
  by code_simp

lemma relaxed_chain_source_assignment:
  "check_rat_assignment relaxed_chain_source [(0, -1/2), (2, -1/4), (4, -1/2)]"
  by code_simp

text \<open>
  The native SAT capture (b=x0, f=x1, c=x2, g=x3, z=x4, w=x5, y=x6, ReLU
  auxiliaries x7, x8, tableau slacks x9..x13). This assignment satisfies
  every processed row and bound but has g = 1/2 while ReLU(c) = 0, so only
  the ReLU check rejects it.
\<close>

definition relu_violating_assignment :: rat_assignment where
  "relu_violating_assignment =
    [(0, 1/2), (1, 1/2), (2, -1/4), (3, 1/2), (4, 1/2), (5, -1/4), (6, 1), (7, 0), (8, 3/4)]"

lemma native_sat_relu_violation_rejected:
  "\<not> check_rat_assignment Imported_Marabou_Native_Relu_Sat.imported_query
      relu_violating_assignment \<and>
   check_rat_assignment
      (Imported_Marabou_Native_Relu_Sat.imported_query\<lparr>rat_relu_atoms := []\<rparr>)
      relu_violating_assignment"
  by code_simp

end
