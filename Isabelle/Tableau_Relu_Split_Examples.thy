theory Tableau_Relu_Split_Examples
  imports Tableau_Relu_Split Imported_Marabou_Example_Preprocess_Split_Unsat
begin

text \<open>Computations by code_simp; no evaluation oracle is used.\<close>

definition split_relu :: aux_relu where
  "split_relu = \<lparr>relu_b = 0, relu_f = 1, relu_aux = 2\<rparr>"

section \<open>A query that needs a split, solved by the HOL solver\<close>

text \<open>
  ReLU x0 \<rightarrow> x1 with auxiliary x2 (x1 - x0 - x2 = 0), and x1 - x0 = 1/2 with
  x1 \<ge> 1/4. The linear part alone is feasible (x0 = 0, x1 = 1/2). The active
  phase would need x1 = x0; the inactive phase x1 = 0 < 1/4.
\<close>

definition split_query :: query where
  "split_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0,
                      LinearEq (Linexpr 0 [(1, 1), (-1, 0)]) (1 / 2)],
      query_bounds = [Lower 0 (-1), Upper 0 1, Lower 1 (1 / 4), Upper 1 1, Lower 2 0, Upper 2 2],
      relu_atoms = [ReLU 0 1]\<rparr>"

text \<open>
  At the start x1 sits at its lower bound 1/4 > 0, so getCaseSplits tries the
  active child first. The inactive child's bound x1 \<le> 0 crosses x1 \<ge> 1/4 at
  once. The active child survives row tightening (single rows cannot combine
  x1 - x0 - x2 = 0 with x1 - x0 = 1/2), and one simplex step refutes it.
\<close>

lemma split_query_solved:
  "\<not> is_simplex_unsat (solve_linear_part 20 3 split_query)"
  "case_splits (initial_tableau 3 split_query) split_relu =
     [native_active_split split_relu, native_inactive_split split_relu]"
  "first_conflict (branch_store (apply_split (native_inactive_split split_relu)
     (root_branch (initial_tableau 3 split_query)))) = Some (1, Upper_Side, 0)"
  "solve_one_split 20 3 split_query split_relu"
  by code_simp+

theorem split_query_unsatisfiable: "unsatisfiable split_query"
  using solve_one_split_unsat split_query_solved(4) .

section \<open>A file refuted by the native split\<close>

text \<open>
  examples/preprocess_split_unsat.mqx has the bytes of the relu_split capture's
  query: ReLU x0 \<rightarrow> x1 with the auxiliary x2 in the file's own equation
  x1 - x0 - x2 = 0. Marabou refuted it with one binary split. Here the native
  split theorem applies to its starting tableau. Each child's emptiness
  follows from the tableau's bounded solutions by linear arithmetic: in the
  inactive child x1 = 0 forces x3 \<le> -1/4 and x3 \<ge> 1/4, in the active child
  x2 = 0 forces x4 \<le> -1/4 and x4 \<ge> 1/4. Running the executable solver on this
  14-column tableau by code_simp is too slow (see TABLEAU_RELU_SPLIT.md), so
  the children are refuted by linarith rather than by evaluation.
\<close>

abbreviation file_query :: query where
  "file_query \<equiv> embed_query Imported_Marabou_Preprocessed_Split_Unsat.imported_file_query"

lemma file_query_ready:
  "engine_ready 9 file_query" "relu_in_aux_form 9 file_query split_relu"
  by code_simp+

lemma file_query_solutions:
  assumes w: "w \<in> tableau_bounded_models (initial_tableau 9 file_query)"
  shows "w 1 - w 3 - w 5 = 1 / 4" "w 1 + w 3 - w 6 = 1 / 4"
    "w 2 - w 4 - w 7 = 1 / 4" "w 2 + w 4 - w 8 = 1 / 4"
    "0 \<le> w 1" "0 \<le> w 2" "0 \<le> w 5" "0 \<le> w 6" "0 \<le> w 7" "0 \<le> w 8"
proof -
  have len: "length (linear_atoms file_query) = 5"
    by (simp add: embed_query_def Imported_Marabou_Preprocessed_Split_Unsat.imported_file_query_def)
  have rows: "\<And>x. 9 \<le> x \<Longrightarrow> x < 14 \<Longrightarrow>
      w x = eval_terms w (aux_terms (linear_atoms file_query ! (x - 9))) \<and>
      w x = aux_scalar (linear_atoms file_query ! (x - 9))"
    and bnds: "\<And>x. x < 9 \<Longrightarrow> lower_of file_query x \<le> w x \<and> w x \<le> upper_of file_query x"
    using w initial_bounded_models[OF file_query_ready(1)] len by auto
  note defs = embed_query_def Imported_Marabou_Preprocessed_Split_Unsat.imported_file_query_def
    aux_terms_def aux_scalar_def lower_of_def upper_of_def of_rat_divide of_rat_numeral_eq
  show "w 1 - w 3 - w 5 = 1 / 4" using rows[of 9] by (simp add: defs)
  show "w 1 + w 3 - w 6 = 1 / 4" using rows[of 10] by (simp add: defs)
  show "w 2 - w 4 - w 7 = 1 / 4" using rows[of 11] by (simp add: defs)
  show "w 2 + w 4 - w 8 = 1 / 4" using rows[of 12] by (simp add: defs)
  show "0 \<le> w 1" using bnds[of 1] by (simp add: defs)
  show "0 \<le> w 2" using bnds[of 2] by (simp add: defs)
  show "0 \<le> w 5" using bnds[of 5] by (simp add: defs)
  show "0 \<le> w 6" using bnds[of 6] by (simp add: defs)
  show "0 \<le> w 7" using bnds[of 7] by (simp add: defs)
  show "0 \<le> w 8" using bnds[of 8] by (simp add: defs)
qed

lemma file_query_children_empty:
  "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
     decision_models (native_inactive_split split_relu) = {}"
  "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
     decision_models (native_active_split split_relu) = {}"
proof -
  show "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
          decision_models (native_inactive_split split_relu) = {}"
  proof (rule ccontr)
    assume "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
              decision_models (native_inactive_split split_relu) \<noteq> {}"
    then obtain w where w: "w \<in> tableau_bounded_models (initial_tableau 9 file_query)"
      and d: "w 1 \<le> 0" by (auto simp: decision_models_splits split_relu_def)
    note s = file_query_solutions[OF w]
    show False using s d by linarith
  qed
  show "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
          decision_models (native_active_split split_relu) = {}"
  proof (rule ccontr)
    assume "tableau_bounded_models (initial_tableau 9 file_query) \<inter>
              decision_models (native_active_split split_relu) \<noteq> {}"
    then obtain w where w: "w \<in> tableau_bounded_models (initial_tableau 9 file_query)"
      and d: "w 2 \<le> 0" by (auto simp: decision_models_splits split_relu_def)
    note s = file_query_solutions[OF w]
    show False using s d by linarith
  qed
qed

theorem preprocess_split_file_unsatisfiable_by_native_split:
  assumes "decode_query Imported_Marabou_Example_Preprocess_Split_Unsat.query_file = Some Q"
  shows "unsatisfiable (embed_query Q)"
  using decodes_like_unsatisfiable[OF
      Imported_Marabou_Example_Preprocess_Split_Unsat.query_file_decodes_like_capture
      root_split_children_unsat[OF file_query_ready file_query_children_empty] assms] .

section \<open>The auxiliary equation is necessary\<close>

text \<open>
  Without aux = f - b the two bound-only children do not cover the ReLU: here
  b = f = 1 satisfies the ReLU, but aux = 1 violates the active child's aux \<le> 0.
\<close>

lemma split_needs_aux_equation:
  "relu_holds split_relu (\<lambda>x. 1)"
  "(\<lambda>x. 1) \<notin> decision_models (native_inactive_split split_relu)"
  "(\<lambda>x. 1) \<notin> decision_models (native_active_split split_relu)"
  by (simp_all add: split_relu_def relu_holds_def satisfies_relu_def relu_def decision_models_splits)

text \<open>At the zero boundary b = f = aux = 0 both children contain the point.\<close>

lemma zero_point_in_both_children:
  "(\<lambda>x. 0) \<in> decision_models (native_inactive_split split_relu) \<inter>
              decision_models (native_active_split split_relu)"
  by (simp add: decision_models_splits)

section \<open>Queries the split does not refute\<close>

definition sat_relu_query :: query where
  "sat_relu_query =
     \<lparr>linear_atoms = [LinearEq (Linexpr 0 [(1, 1), (-1, 0), (-1, 2)]) 0],
      query_bounds = [Lower 0 (-1), Upper 0 1, Lower 1 0, Upper 1 1, Lower 2 0, Upper 2 1],
      relu_atoms = [ReLU 0 1]\<rparr>"

definition no_aux_query :: query where
  "no_aux_query = sat_relu_query\<lparr>linear_atoms := [LinearEq (Linexpr 0 [(1, 1), (1, 0)]) 1]\<rparr>"

lemma split_boundaries:
  "\<not> solve_one_split 20 3 sat_relu_query split_relu"
  "\<not> relu_in_aux_form 3 no_aux_query split_relu"
  "\<not> solve_one_split 20 3 no_aux_query split_relu"
  by code_simp+

lemma sat_relu_query_satisfiable: "satisfiable sat_relu_query"
proof -
  let ?v = "\<lambda>x::var. if x = 2 then 0 else (1 / 2 :: real)"
  have "satisfies_query ?v sat_relu_query"
    by (simp add: satisfies_query_def sat_relu_query_def satisfies_relu_def relu_def)
  then show ?thesis unfolding satisfiable_def by blast
qed

end
