theory Tableau_Auxiliary_Examples
  imports Rational_Tableau_Auxiliary Imported_Marabou_Solver_Linear
begin

text \<open>
  The exact two-variable input from tools/solver_capture/capture.cpp, linear
  scenario. This is an explicit HOL description, not a verified C++ decoder.
  One checked auxiliary step produces exactly the earlier solver snapshot.
  Its existing, solver-produced certificate now proves this source query
  UNSAT through the verified step. No new solver execution is claimed here.
\<close>

definition solver_linear_before_aux :: rat_query where
  "solver_linear_before_aux = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 1)]) 0],
    rat_query_bounds = [RatLower 0 (-2), RatUpper 0 (1/4),
      RatLower 1 (1/2), RatUpper 1 2],
    rat_relu_atoms = []\<rparr>"

lemma solver_linear_aux_matches_snapshot:
  "rat_introduce_fixed_aux solver_linear_before_aux 0 2 = Some imported_query"
  by code_simp

lemma solver_linear_aux_equisatisfiable:
  "satisfiable (embed_query imported_query) \<longleftrightarrow>
    satisfiable (embed_query solver_linear_before_aux)"
  by (rule rat_introduce_fixed_aux_satisfiable_iff[OF solver_linear_aux_matches_snapshot])

lemma solver_linear_before_aux_checked:
  "check_after_fixed_aux solver_linear_before_aux 0 2 imported_certificate"
  by code_simp

theorem solver_linear_before_aux_unsatisfiable:
  "unsatisfiable (embed_query solver_linear_before_aux)"
  by (rule check_after_fixed_aux_sound[OF solver_linear_before_aux_checked])

lemma solver_linear_rejects_bad_step_or_leaf:
  "\<not> check_after_fixed_aux solver_linear_before_aux 0 0 imported_certificate \<and>
   \<not> check_after_fixed_aux solver_linear_before_aux 0 2 (Linear_Unsat [])"
  by code_simp

text \<open>
  A nonzero affine scalar, duplicate variable occurrences, a zero coefficient,
  a repeated equality, an inequality, unrelated bounds, and a ReLU.
  The chosen equality is at index 1; only this occurrence is replaced.
\<close>

definition affine_aux_expr :: rat_linexpr where
  "affine_aux_expr = RatExpr (1/2) [(2, 0), (-1, 0), (0, 9)]"

definition affine_aux_source :: rat_query where
  "affine_aux_source = \<lparr>
    rat_linear_atoms = [RatLe (RatExpr 0 [(1, 1)]) 2,
      RatEq affine_aux_expr (3/4), RatEq affine_aux_expr (3/4)],
    rat_query_bounds = [RatLower 4 (-1), RatUpper 4 1],
    rat_relu_atoms = [ReLU 2 3]\<rparr>"

definition affine_aux_result :: rat_query where
  "affine_aux_result = rat_fixed_aux_query affine_aux_source 1 5 affine_aux_expr (3/4)"

lemma affine_aux_step_checked:
  "rat_introduce_fixed_aux affine_aux_source 1 5 = Some affine_aux_result"
  by code_simp

lemma affine_aux_preserves_other_atoms:
  "rat_linear_atoms affine_aux_result ! 0 = rat_linear_atoms affine_aux_source ! 0 \<and>
   rat_linear_atoms affine_aux_result ! 2 = RatEq affine_aux_expr (3/4) \<and>
   rat_relu_atoms affine_aux_result = [ReLU 2 3]"
  by code_simp

definition affine_aux_witness :: valuation where
  "affine_aux_witness x = (if x = 0 then 1/4 else if x = 5 then 17 else 0)"

lemma affine_aux_source_has_model:
  "satisfies_query affine_aux_witness (embed_query affine_aux_source)"
  by (simp add: affine_aux_witness_def affine_aux_source_def affine_aux_expr_def
      embed_query_def satisfies_query_def satisfies_relu_def of_rat_divide)

lemma affine_aux_extended_model:
  "satisfies_query (affine_aux_witness(5 := 3/4)) (embed_query affine_aux_result)"
  by (simp add: affine_aux_result_def rat_fixed_aux_query_def
      affine_aux_witness_def affine_aux_source_def affine_aux_expr_def
      embed_query_def satisfies_query_def satisfies_relu_def of_rat_divide)

lemma affine_aux_needs_model_extension:
  "\<not> satisfies_query affine_aux_witness (embed_query affine_aux_result)"
  by (simp add: affine_aux_result_def rat_fixed_aux_query_def
      affine_aux_witness_def affine_aux_source_def affine_aux_expr_def
      embed_query_def satisfies_query_def of_rat_divide)

lemma all_syntactic_collisions_rejected:
  "\<forall>s \<in> set [0, 1, 2, 3, 4, 9].
    rat_introduce_fixed_aux affine_aux_source 1 s = None"
  by code_simp

lemma invalid_positions_and_inequalities_rejected:
  "rat_introduce_fixed_aux affine_aux_source 0 5 = None \<and>
   rat_introduce_fixed_aux affine_aux_source 3 5 = None \<and>
   rat_introduce_fixed_aux (affine_aux_source\<lparr>rat_linear_atoms := []\<rparr>) 0 5 = None \<and>
   rat_introduce_fixed_aux (affine_aux_source\<lparr>
     rat_linear_atoms := [RatGe affine_aux_expr 0]\<rparr>) 0 5 = None"
  by code_simp

lemma auxiliary_reuse_rejected:
  "rat_introduce_fixed_aux affine_aux_result 2 5 = None"
  by code_simp

lemma negative_scalar_introduction:
  "rat_introduce_fixed_aux
    \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0)]) (-3/2)],
     rat_query_bounds = [], rat_relu_atoms = []\<rparr> 0 1 =
   Some \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), (-1, 1)]) 0],
     rat_query_bounds = [RatLower 1 (-3/2), RatUpper 1 (-3/2)],
     rat_relu_atoms = []\<rparr>"
  by code_simp

text \<open>
  Freshness is necessary for lifting UNSAT. Reusing a variable that occurs
  only in another bound can make a satisfiable source inconsistent. The raw
  transformation below demonstrates the failure; the checked interface
  rejects it even when a valid certificate of the inconsistent result exists.
\<close>

definition collision_source :: rat_query where
  "collision_source = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0)]) 1],
    rat_query_bounds = [RatUpper 1 0], rat_relu_atoms = []\<rparr>"

definition collision_result :: rat_query where
  "collision_result = rat_fixed_aux_query collision_source 0 1 (RatExpr 0 [(1, 0)]) 1"

lemma collision_source_has_model:
  "satisfies_query (\<lambda>x. if x = 0 then 1 else 0) (embed_query collision_source)"
  by (simp add: collision_source_def embed_query_def satisfies_query_def)

theorem collision_source_satisfiable:
  "satisfiable (embed_query collision_source)"
  using collision_source_has_model unfolding satisfiable_def by blast

lemma collision_result_checked:
  "check_certificate collision_result (Linear_Unsat [0, 0, 1, 1, 0])"
  by code_simp

theorem collision_result_unsatisfiable:
  "unsatisfiable (embed_query collision_result)"
  by (rule check_certificate_sound[OF collision_result_checked])

lemma collision_cannot_be_used_to_certify_source:
  "rat_introduce_fixed_aux collision_source 0 1 = None \<and>
   \<not> check_after_fixed_aux collision_source 0 1 (Linear_Unsat [0, 0, 1, 1, 0])"
  by code_simp

end
