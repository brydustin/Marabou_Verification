theory ReLU_Phase_Fixing_Examples
  imports Rational_Proof_Trees Rational_Assignment
begin

text \<open>
  Weights for check_relu_fixed_active/inactive index the rows of
  relu_hull_query Q x y: first -y <= 0 and x - y <= 0, then the rows of Q.
\<close>

section \<open>Active phase fixed by a positive output lower bound\<close>

text \<open>
  x in [-1, 1], y in [3/2, 2], y = ReLU(x). The phase must be active, so
  y = x <= 1, which contradicts y >= 3/2. The linear relaxation y >= x,
  y >= 0 has the model x = 1, y = 3/2, so the phase is essential.
\<close>

definition active_by_output :: rat_query where
  "active_by_output = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1, RatLower 1 (3/2), RatUpper 1 2],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition active_by_output_certificate :: certificate where
  "active_by_output_certificate =
     Relu_Fix_Active 0 1 (RatLower 1 (3/2)) [0, 0, 0, 0, 1, 0]
       (Linear_Unsat [1, 0, 0, 0, 1, 1, 0])"

lemma active_by_output_checked:
  "check_certificate active_by_output active_by_output_certificate"
  by code_simp

theorem active_by_output_unsatisfiable:
  "unsatisfiable (embed_query active_by_output)"
  by (rule check_certificate_sound[OF active_by_output_checked])

lemma active_by_output_relaxation_has_model:
  "check_rat_assignment (active_by_output\<lparr>rat_relu_atoms := [],
     rat_linear_atoms := [RatGe (RatExpr 0 [(1, 1)]) 0, RatGe (RatExpr 0 [(1, 1), (-1, 0)]) 0]\<rparr>)
     [(0, 1), (1, 3/2)]"
  by code_simp

section \<open>Active phase fixed through the hull inequality y >= 0\<close>

text \<open>
  An auxiliary-form ReLU: y - x - a = 0 with a = 0. No bound gives x >= 0
  directly, and y's own lower bound is negative. Yet x = y - a >= 0 follows
  from the hull row y >= 0: weights 1 on -y <= 0, on the equality row
  y - x - a <= 0 and on a <= 0.
\<close>

definition active_by_auxiliary :: rat_query where
  "active_by_auxiliary = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 2, RatLower 1 (-1), RatUpper 1 2,
                         RatLower 2 0, RatUpper 2 0],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma active_by_auxiliary_premise:
  "check_relu_fixed_active active_by_auxiliary 0 1 (RatLower 0 0)
     [1, 0, 1, 0, 0, 0, 0, 0, 0, 1]"
  by code_simp

text \<open>
  Without the hull rows no weights prove x >= 0: normalized rows ignore the
  ReLU, and the relaxation has the model x = y = -1, a = 0.
\<close>

lemma hull_row_is_needed:
  "\<not> check_linear_bound active_by_auxiliary (RatLower 0 0) ws"
proof
  assume "check_linear_bound active_by_auxiliary (RatLower 0 0) ws"
  then have relaxed: "check_linear_bound (active_by_auxiliary\<lparr>rat_relu_atoms := []\<rparr>) (RatLower 0 0) ws"
    by (simp add: check_linear_bound_def check_linear_implication_def normalize_query_def)
  have "check_rat_assignment (active_by_auxiliary\<lparr>rat_relu_atoms := []\<rparr>) [(0, -1), (1, -1), (2, 0)]"
    by code_simp
  from check_linear_bound_sound[OF relaxed check_rat_assignment_sound[OF this]]
  show False by (simp add: assignment_valuation_def assignment_value_def)
qed

section \<open>Inactive phase fixed by a nonpositive input or output upper bound\<close>

text \<open>
  x in [-2, -1/2], y in [0, 2], y - w = 0 with w in [1/4, 2]. The phase must
  be inactive, so y = 0 < 1/4 <= w. The relaxation has the model
  x = -1/2, y = w = 1/4.
\<close>

definition inactive_by_input :: rat_query where
  "inactive_by_input = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 2)]) 0],
     rat_query_bounds = [RatLower 0 (-2), RatUpper 0 (-1/2), RatLower 1 0, RatUpper 1 2,
                         RatLower 2 (1/4), RatUpper 2 2],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition inactive_by_input_certificate :: certificate where
  "inactive_by_input_certificate =
     Relu_Fix_Inactive 0 1 (RatUpper 0 (-1/2)) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
       (Linear_Unsat [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0])"

lemma inactive_by_input_checked:
  "check_certificate inactive_by_input inactive_by_input_certificate"
  by code_simp

theorem inactive_by_input_unsatisfiable:
  "unsatisfiable (embed_query inactive_by_input)"
  by (rule check_certificate_sound[OF inactive_by_input_checked])

lemma inactive_by_input_relaxation_has_model:
  "check_rat_assignment (inactive_by_input\<lparr>rat_relu_atoms := []\<rparr>)
     [(0, -1/2), (1, 1/4), (2, 1/4)]"
  by code_simp

definition inactive_by_output :: rat_query where
  "inactive_by_output = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 2)]) 0],
     rat_query_bounds = [RatLower 0 (-2), RatUpper 0 2, RatLower 1 (-1), RatUpper 1 0,
                         RatLower 2 (1/4), RatUpper 2 2],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

text \<open>
  Here y <= 0 forces x <= 0, contradicting x = w >= 1/4. The inactive split
  adds x <= 0; the leaf combines it with x - w = 0 and w >= 1/4.
\<close>

lemma inactive_by_output_checked:
  "check_certificate inactive_by_output
     (Relu_Fix_Inactive 0 1 (RatUpper 1 0) [0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
       (Linear_Unsat [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0]))"
  by code_simp

section \<open>Rejections\<close>

text \<open>
  A native epsilon test would call an upper bound of 10^-12 nonpositive and
  fix the inactive phase. The query below then has exactly one model,
  x = y = 10^-12, so it is satisfiable; its inactive split is not.
  The exact check refuses that premise, and no certificate is accepted.
\<close>

definition tiny_positive :: rat_query where
  "tiny_positive = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 (1/1000000000000),
                         RatLower 1 (1/1000000000000), RatUpper 1 1],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

lemma tiny_positive_has_model:
  "check_rat_assignment tiny_positive [(0, 1/1000000000000), (1, 1/1000000000000)]"
  by code_simp

lemma tiny_positive_inactive_split_is_unsatisfiable:
  "check_certificate (rat_inactive_split tiny_positive 0 1) (Linear_Unsat [1, 0, 0, 0, 0, 1, 0])"
  by code_simp

lemma tiny_positive_premise_rejected:
  "\<not> check_relu_fixed_inactive tiny_positive 0 1 (RatUpper 0 (1/1000000000000))
       [0, 0, 0, 1, 0, 0]"
  by code_simp

theorem tiny_positive_has_no_certificate:
  "\<not> check_certificate tiny_positive cert"
  using check_certificate_rejects_model[OF check_rat_assignment_sound[OF tiny_positive_has_model]] .

text \<open>Other malformed evidence is rejected as well.\<close>

lemma phase_fixing_rejections:
  \<comment> \<open>A negative input lower bound, however small, does not fix the active phase.\<close>
  "\<not> check_relu_fixed_active active_by_output 0 1 (RatLower 0 (-1/1000000)) [0, 0, 1, 0, 0, 0]"
  \<comment> \<open>A zero output lower bound does not either.\<close>
  "\<not> check_relu_fixed_active active_by_output 0 1 (RatLower 1 0) [1, 0, 0, 0, 0, 0]"
  \<comment> \<open>The premise must be implied: y >= 2 is not.\<close>
  "\<not> check_relu_fixed_active active_by_output 0 1 (RatLower 1 2) [0, 0, 0, 0, 1, 0]"
  \<comment> \<open>A lower bound cannot fix the inactive phase, nor an upper bound the active one.\<close>
  "\<not> check_relu_fixed_inactive inactive_by_input 0 1 (RatLower 0 (-2)) [0, 0, 0, 0, 1, 0, 0, 0, 0, 0]"
  "\<not> check_relu_fixed_active inactive_by_input 0 1 (RatUpper 0 (-1/2)) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]"
  \<comment> \<open>The ReLU must be present, with input and output in order.\<close>
  "\<not> check_relu_fixed_inactive inactive_by_input 1 0 (RatUpper 0 (-1/2)) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]"
  \<comment> \<open>Missing and negative weights.\<close>
  "\<not> check_relu_fixed_inactive inactive_by_input 0 1 (RatUpper 0 (-1/2)) []"
  "\<not> check_relu_fixed_inactive inactive_by_input 0 1 (RatUpper 0 (-1/2)) [0, 0, 0, 0, 0, 1, -1, 0, 0, 0]"
  \<comment> \<open>The continuation is checked against the chosen phase only.\<close>
  "\<not> check_certificate active_by_output
       (Relu_Fix_Active 0 1 (RatLower 1 (3/2)) [0, 0, 0, 0, 1, 0] (Linear_Unsat [0, 0, 0, 0, 1, 1, 0]))"
  "\<not> check_certificate inactive_by_input
       (Relu_Fix_Active 0 1 (RatUpper 0 (-1/2)) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
         (Linear_Unsat [1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]))"
  by code_simp+

end
