theory Tableau_Auxiliary_Sequence_Examples
  imports Tableau_Auxiliary_Sequence Imported_Marabou_Solver_Relu_Split
begin

text \<open>
  Explicit pre-tableau query from the relu_split scenario in
  tools/solver_capture/capture.cpp. Variables x0..x8 are b,f,a,t,u,p,q,r,s.
  The ReLU auxiliary a and its defining equation are already supplied by
  that input; this example introduces only the five scalar-fixed variables.
  The source and step list are hand-written HOL data, not a native step log.
\<close>

definition solver_split_input_query :: rat_query where
  "solver_split_input_query = \<lparr>
    rat_linear_atoms = [
      RatEq (RatExpr 0 [(1, 1), (-1, 3), (-1, 5)]) (1/4),
      RatEq (RatExpr 0 [(1, 1), (1, 3), (-1, 6)]) (1/4),
      RatEq (RatExpr 0 [(1, 2), (-1, 4), (-1, 7)]) (1/4),
      RatEq (RatExpr 0 [(1, 2), (1, 4), (-1, 8)]) (1/4),
      RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
    rat_query_bounds = [
      RatLower 0 (-1), RatUpper 0 1, RatLower 1 0, RatUpper 1 1,
      RatLower 2 0, RatUpper 2 1, RatLower 3 (-1), RatUpper 3 1,
      RatLower 4 (-1), RatUpper 4 1, RatLower 5 0, RatUpper 5 2,
      RatLower 6 0, RatUpper 6 2, RatLower 7 0, RatUpper 7 2,
      RatLower 8 0, RatUpper 8 2],
    rat_relu_atoms = [ReLU 0 1]\<rparr>"

text \<open>
  The capture snapshot and native JSON writer use column order. The final
  equation's input order is f-b-a; column order is -b+f-a. Prove equivalence
  before using the reordered query for an exact match to the saved snapshot.
\<close>

definition solver_split_column_query :: rat_query where
  "solver_split_column_query = solver_split_input_query\<lparr>
    rat_linear_atoms := (rat_linear_atoms solver_split_input_query)
      [4 := RatEq (RatExpr 0 [(-1, 0), (1, 1), (-1, 2)]) 0]\<rparr>"

lemma solver_split_term_order_semantics:
  "satisfies_query v (embed_query solver_split_column_query) \<longleftrightarrow>
    satisfies_query v (embed_query solver_split_input_query)"
  by (simp add: solver_split_column_query_def solver_split_input_query_def
      embed_query_def satisfies_query_def algebra_simps)

definition solver_split_aux_steps :: "fixed_aux_step list" where
  "solver_split_aux_steps = [(0, 9), (1, 10), (2, 11), (3, 12), (4, 13)]"

lemma solver_split_sequence_matches_snapshot:
  "rat_introduce_fixed_aux_sequence solver_split_column_query solver_split_aux_steps =
    Some imported_query"
  by code_simp

theorem solver_split_source_equisatisfiable:
  "satisfiable (embed_query imported_query) \<longleftrightarrow>
    satisfiable (embed_query solver_split_input_query)"
  using fixed_aux_sequence_satisfiable_iff[OF solver_split_sequence_matches_snapshot]
  by (simp add: satisfiable_def solver_split_term_order_semantics)

lemma solver_split_before_aux_checked:
  "check_after_fixed_aux_sequence solver_split_column_query
    solver_split_aux_steps imported_certificate"
  by code_simp

theorem solver_split_before_aux_unsatisfiable:
  "unsatisfiable (embed_query solver_split_input_query)"
proof -
  have "unsatisfiable (embed_query solver_split_column_query)"
    by (rule check_after_fixed_aux_sequence_sound[OF solver_split_before_aux_checked])
  then show ?thesis
    by (simp add: unsatisfiable_def satisfiable_def solver_split_term_order_semantics)
qed

text \<open>
  Reject a name that became occupied during the sequence, a late invalid
  equation index, and an attempted overwrite of an original variable.
  A failed prefix cannot be repaired by adding further steps.
\<close>

lemma solver_split_sequence_rejects_invalid_steps:
  "rat_introduce_fixed_aux_sequence solver_split_column_query [(0, 9), (1, 9)] = None \<and>
   rat_introduce_fixed_aux_sequence solver_split_column_query
     (take 4 solver_split_aux_steps @ [(5, 13)]) = None \<and>
   rat_introduce_fixed_aux_sequence solver_split_column_query [(0, 9), (1, 0)] = None"
  by code_simp

lemma solver_split_failed_prefix_stays_failed:
  "rat_introduce_fixed_aux_sequence solver_split_column_query
    ([(0, 9), (1, 9)] @ rest) = None"
  by (rule fixed_aux_sequence_failed_prefix)
     (use solver_split_sequence_rejects_invalid_steps in blast)

lemma solver_split_partial_sequence_rejects_saved_certificate:
  "\<not> check_after_fixed_aux_sequence solver_split_column_query [] imported_certificate \<and>
   \<not> check_after_fixed_aux_sequence solver_split_column_query
      (take 4 solver_split_aux_steps) imported_certificate"
  by code_simp

lemma solver_split_sequence_checks_both_terminal_children:
  "(case imported_certificate of
      Relu_Split x y active inactive \<Rightarrow>
        \<not> check_after_fixed_aux_sequence solver_split_column_query solver_split_aux_steps
          (Relu_Split x y (Linear_Unsat []) inactive) \<and>
        \<not> check_after_fixed_aux_sequence solver_split_column_query solver_split_aux_steps
          (Relu_Split x y active (Linear_Unsat []))
    | _ \<Rightarrow> False)"
  by code_simp

text \<open>
  Repeating an equation index with different fresh variables is sound and
  allowed, though the native loop processes each equation once. The second
  introduction must read the current zero scalar, not the original 3/4.
\<close>

definition sequence_sat_source :: rat_query where
  "sequence_sat_source = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0)]) (3/4)],
    rat_query_bounds = [], rat_relu_atoms = []\<rparr>"

definition sequence_sat_result :: rat_query where
  "sequence_sat_result = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 1), (-1, 2)]) 0],
    rat_query_bounds = [RatLower 1 (3/4), RatUpper 1 (3/4), RatLower 2 0, RatUpper 2 0],
    rat_relu_atoms = []\<rparr>"

lemma sequence_reads_current_scalar:
  "rat_introduce_fixed_aux_sequence sequence_sat_source [(0, 1), (0, 2)] =
    Some sequence_sat_result"
  by code_simp

lemma sequence_sat_source_has_model:
  "satisfies_query (\<lambda>x. if x = 0 then 3/4 else 0) (embed_query sequence_sat_source)"
  by (simp add: sequence_sat_source_def embed_query_def satisfies_query_def of_rat_divide)

lemma sequence_sat_result_has_model:
  "satisfies_query (\<lambda>x. if x = 0 \<or> x = 1 then 3/4 else 0)
    (embed_query sequence_sat_result)"
  by (simp add: sequence_sat_result_def embed_query_def satisfies_query_def of_rat_divide)

theorem sequence_sat_source_rejects_every_certificate:
  "\<not> check_after_fixed_aux_sequence sequence_sat_source steps cert"
  by (rule check_after_fixed_aux_sequence_rejects_model[OF sequence_sat_source_has_model])

end
