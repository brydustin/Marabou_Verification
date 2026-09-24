theory ReLU_Auxiliary_Sequence_Examples
  imports Imported_Marabou_Native_Relu_Sequence
begin

text \<open>
  A satisfiable sequence with negative and positive lower bounds, independent
  of the native UNSAT capture. The second auxiliary has upper bound zero.
\<close>

definition two_relu_intervals :: rat_query where
  "two_relu_intervals = \<lparr>rat_linear_atoms = [],
    rat_query_bounds = [RatLower 0 (-1), RatLower 2 1],
    rat_relu_atoms = [ReLU 0 1, ReLU 2 3]\<rparr>"

definition interval_introductions :: "relu_aux_step list" where
  "interval_introductions =
    [ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 2 3 5 (Some 1)]"

definition introduced_intervals :: rat_query where
  "introduced_intervals = \<lparr>
    rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), (-1, 0), (-1, 4)]) 0,
      RatEq (RatExpr 0 [(1, 3), (-1, 2), (-1, 5)]) 0],
    rat_query_bounds = [RatLower 0 (-1), RatLower 2 1,
      RatLower 4 0, RatUpper 4 1, RatLower 5 0, RatUpper 5 0],
    rat_relu_atoms = [ReLU 0 1, ReLU 2 3]\<rparr>"

lemma interval_sequence_computes:
  "rat_introduce_relu_aux_sequence two_relu_intervals interval_introductions =
    Some introduced_intervals"
  by code_simp

definition interval_witness :: valuation where
  "interval_witness i =
    (if i = 0 then -1 else if i = 2 \<or> i = 3 \<or> i = 4 then 1 else 0)"

lemma interval_source_has_model:
  "satisfies_query interval_witness (embed_query two_relu_intervals)"
  by (simp add: interval_witness_def two_relu_intervals_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def)

lemma interval_result_has_model:
  "satisfies_query interval_witness (embed_query introduced_intervals)"
  by (simp add: interval_witness_def introduced_intervals_def embed_query_def
      satisfies_query_def satisfies_relu_def relu_def)

theorem interval_source_rejects_all_sequence_certificates:
  "\<not> check_after_relu_aux_sequence two_relu_intervals relu_steps tableau_steps cert"
  by (rule check_after_relu_aux_sequence_rejects_model[OF interval_source_has_model])

lemma interval_sequence_prefix_succeeds:
  "rat_introduce_relu_aux_sequence two_relu_intervals
    [ReLU_Aux_Step 0 1 4 (Some (-1))] =
    Some (rat_relu_aux_query two_relu_intervals 0 1 4 (Some (-1)))"
  by code_simp

text \<open>
  Variable 4 is fresh in the original query, but occupied after the first
  step. Checking only against the original query would miss this collision.
  A bad later premise also fails the whole sequence.
\<close>

lemma sequence_rejects_late_collision:
  "rat_introduce_relu_aux_sequence two_relu_intervals
    [ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 2 3 4 (Some 1)] = None"
  by code_simp

lemma sequence_rejects_late_premise_or_selection:
  "rat_introduce_relu_aux_sequence two_relu_intervals
    [ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 2 3 5 (Some 2)] = None \<and>
   rat_introduce_relu_aux_sequence two_relu_intervals
    [ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 3 2 5 (Some 1)] = None"
  by code_simp

lemma failed_sequence_cannot_be_repaired_by_appending:
  "rat_introduce_relu_aux_sequence two_relu_intervals
    ([ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 2 3 4 (Some 1)] @ rest) = None"
  by (rule relu_aux_sequence_failed_prefix[OF sequence_rejects_late_collision])

text \<open>
  The mathematical interface permits a missing finite cap and multiple
  fresh auxiliaries for the same ReLU. The native importer is narrower:
  it requires one finite-bound introduction per initially plain ReLU.
\<close>

lemma same_relu_with_another_fresh_auxiliary:
  "rat_introduce_relu_aux_sequence two_relu_intervals
    [ReLU_Aux_Step 0 1 4 (Some (-1)), ReLU_Aux_Step 0 1 5 None] =
    Some (rat_relu_aux_query
      (rat_relu_aux_query two_relu_intervals 0 1 4 (Some (-1))) 0 1 5 None)"
  by code_simp

text \<open>
  The native six-variable source needs both ReLUs. Removing either gives
  an exact real model. These are explicit counterexamples to treating the
  second ReLU as irrelevant; they are not solver-produced SAT claims.
\<close>

definition without_first_relu :: rat_query where
  "without_first_relu =
    imported_before_relu_query\<lparr>rat_relu_atoms := [ReLU 2 3]\<rparr>"

definition without_second_relu :: rat_query where
  "without_second_relu =
    imported_before_relu_query\<lparr>rat_relu_atoms := [ReLU 0 1]\<rparr>"

definition first_removed_witness :: valuation where
  "first_removed_witness i = (if i = 0 \<or> i = 2 \<or> i = 4 then -1/2
    else if i = 1 \<or> i = 5 then 1/4 else 0)"

definition second_removed_witness :: valuation where
  "second_removed_witness i = (if i = 0 \<or> i = 2 \<or> i = 4 then -1/2
    else if i = 3 \<or> i = 5 then 1/4 else 0)"

lemma first_relu_removed_model:
  "satisfies_query first_removed_witness (embed_query without_first_relu)"
  by (simp add: without_first_relu_def imported_before_relu_query_def
      first_removed_witness_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def of_rat_divide of_rat_minus)

lemma second_relu_removed_model:
  "satisfies_query second_removed_witness (embed_query without_second_relu)"
  by (simp add: without_second_relu_def imported_before_relu_query_def
      second_removed_witness_def embed_query_def satisfies_query_def
      satisfies_relu_def relu_def of_rat_divide of_rat_minus)

theorem native_source_needs_both_relus:
  "unsatisfiable (embed_query imported_before_relu_query) \<and>
   satisfiable (embed_query without_first_relu) \<and>
   satisfiable (embed_query without_second_relu)"
  using imported_before_relu_query_unsatisfiable
    first_relu_removed_model second_relu_removed_model
  unfolding satisfiable_def by blast

lemma native_sequence_rejects_incomplete_bridge_or_proof:
  "\<not> check_after_relu_aux_sequence imported_before_relu_query (take 1 imported_relu_steps)
      imported_steps imported_certificate \<and>
   \<not> check_after_relu_aux_sequence imported_before_relu_query imported_relu_steps
      (take 4 imported_steps) imported_certificate \<and>
   \<not> check_after_relu_aux_sequence imported_before_relu_query imported_relu_steps
      imported_steps (Linear_Unsat [])"
  by code_simp

end
