theory Imported_Marabou_Preprocessed_Inequality_Unsat
  imports "Marabou_Verification.Preprocessing_Projection" "Marabou_Verification.Inequality_Auxiliary_Sequence"
    "Marabou_Verification.ReLU_Auxiliary_Sequence" "Marabou_Verification.Tableau_Auxiliary_Sequence"
begin

text \<open>
  Native preprocessing. The file's query gets the native slack and ReLU
  auxiliary introductions (checked, with native variable numbering), then
  checked facts re-derive the native tightenings exactly, and the projection
  shows that every constraint of imported_crossing_query is implied under the recorded
  variable renaming. None of the preprocessing record is trusted.
  Preprocessing record SHA-256: f1cab99c072a02575ef0049598aa298790991354ca601bbbb66808fc0579d271
\<close>

definition imported_file_query :: rat_query where
  "imported_file_query = \<lparr>rat_linear_atoms = [RatGe (RatExpr 0 [(1, 0), (1, 1)]) 3, RatLe (RatExpr 0 [(1, 2), ((-1), 1)]) (-1)],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1, RatUpper 1 3],
     rat_relu_atoms = [ReLU 1 2]\<rparr>"

definition imported_slack_steps :: "inequality_aux_step list" where
  "imported_slack_steps = [(0, 3), (1, 4)]"

definition imported_relu_aux_steps :: "relu_aux_step list" where
  "imported_relu_aux_steps = [ReLU_Aux_Step 1 2 5 None]"

definition imported_introduced_query :: rat_query where
  "imported_introduced_query = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (1, 1), (1, 3)]) 3, RatEq (RatExpr 0 [(1, 2), ((-1), 1), (1, 4)]) (-1), RatEq (RatExpr 0 [(1, 2), ((-1), 1), ((-1), 5)]) 0],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1, RatUpper 1 3, RatUpper 3 0, RatLower 4 0, RatLower 5 0],
     rat_relu_atoms = [ReLU 1 2]\<rparr>"

lemma imported_introductions_match:
  "(case rat_introduce_inequality_aux_sequence imported_file_query imported_slack_steps of
      None \<Rightarrow> None
    | Some P \<Rightarrow> rat_introduce_relu_aux_sequence P imported_relu_aux_steps) =
    Some imported_introduced_query"
  by code_simp

definition imported_crossing_query :: rat_query where
  "imported_crossing_query = \<lparr>rat_linear_atoms = [],
     rat_query_bounds = [RatLower 0 3, RatUpper 0 2],
     rat_relu_atoms = []\<rparr>"

text \<open>
  Native preprocessing reported infeasibility without a proof. The facts
  derive 3 <= x1 <= 2 exactly.
\<close>

lemma imported_crossing_query_unsatisfiable:
  "unsatisfiable (embed_query imported_crossing_query)"
  by (rule check_certificate_sound[of _ "Linear_Unsat [1, 1]"]) code_simp

definition imported_projection :: projection where
  "imported_projection = Projection
    [Fact_Hull 1 2, Fact_Bound (RatLower 2 0) [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], Fact_Bound (RatLower 0 0) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0], Fact_Bound (RatLower 1 2) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0], Fact_Bound (RatLower 3 (-1)) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0], Fact_Bound (RatUpper 2 2) [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0], Fact_Bound (RatUpper 4 2) [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0], Fact_Bound (RatUpper 1 2) [0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1], Fact_Bound (RatLower 2 2) [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1], Fact_Bound (RatUpper 5 0) [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], Fact_Phase_Active 1 2 (RatLower 1 2) [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0], Fact_Bound (RatLower 0 1) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], Fact_Bound (RatLower 3 0) [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0], Fact_Bound (RatLower 1 3) [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0]]
    [1]
    [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]
    []"

lemma imported_projection_checked:
  "check_projection imported_introduced_query imported_projection imported_crossing_query"
  by code_simp

theorem imported_file_query_unsatisfiable:
  "unsatisfiable (embed_query imported_file_query)"
proof -
  obtain P where slacks: "rat_introduce_inequality_aux_sequence imported_file_query imported_slack_steps = Some P"
      and relus: "rat_introduce_relu_aux_sequence P imported_relu_aux_steps = Some imported_introduced_query"
    using imported_introductions_match by (auto split: option.splits)
  have "unsatisfiable (embed_query imported_introduced_query)"
    by (rule check_projection_unsatisfiable[OF imported_projection_checked imported_crossing_query_unsatisfiable])
  then have "unsatisfiable (embed_query P)"
    using relu_aux_sequence_unsatisfiable_iff[OF relus] by simp
  then show ?thesis
    using inequality_aux_sequence_unsatisfiable_iff[OF slacks] by simp
qed

end
