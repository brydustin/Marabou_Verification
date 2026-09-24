theory Preprocessing_Projection_Examples
  imports Preprocessing_Projection Rational_Assignment
begin

section \<open>Merging, fixing, tightening and renumbering\<close>

text \<open>
  Original query: b = x0, f = x1, a fixed c = x2 = 1/2, a copy x3 = b, and
  z = x4 = f + c, with f = ReLU(x3). A preprocessor merges x3 into x0,
  eliminates the fixed x2, tightens z to [1/2, 3/2] and renumbers
  (x0, x1, x4) as (y0, y1, y2). The ReLU of the result names y0, so its link
  needs the proved equality x3 = x0. The facts and weights were proposed by
  the untrusted tools/import_marabou_preprocessing.py; code_simp rechecks
  them.
\<close>

definition merged_source :: rat_query where
  "merged_source = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 3), ((-1), 0)]) 0,
       RatEq (RatExpr 0 [(1, 1), (1, 2), ((-1), 4)]) 0],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1, RatLower 1 0, RatUpper 1 1,
       RatLower 2 (1 / 2), RatUpper 2 (1 / 2), RatLower 3 (-2), RatUpper 3 2, RatLower 4 0, RatUpper 4 3],
     rat_relu_atoms = [ReLU 3 1]\<rparr>"

definition merged_result :: rat_query where
  "merged_result = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), ((-1), 2)]) (-1 / 2)],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 1, RatLower 1 0, RatUpper 1 1,
       RatLower 2 (1 / 2), RatUpper 2 (3 / 2)],
     rat_relu_atoms = [ReLU 0 1]\<rparr>"

definition merged_facts :: "fact list" where
  "merged_facts =
    [Fact_Bound (RatUpper 3 1) [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
     Fact_Bound (RatLower 3 (-1)) [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     Fact_Bound (RatLower 4 (1 / 2)) [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
     Fact_Bound (RatUpper 4 (3 / 2)) [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0]]"

definition merged_rows :: "rat list list" where
  "merged_rows =
    [[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     [1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]"

definition merged_link :: relu_link where
  "merged_link = Relu_Link 3 1
     [[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] []"

definition merged_projection :: projection where
  "merged_projection = Projection merged_facts [0, 1, 4] merged_rows [merged_link]"

lemma merged_projection_checked:
  "check_projection merged_source merged_projection merged_result"
  by code_simp

theorem merged_models_project:
  "satisfies_query v (embed_query merged_source) \<Longrightarrow>
    satisfies_query (\<lambda>u. v (proj_var [0, 1, 4] u)) (embed_query merged_result)"
  using check_projection_model[OF merged_projection_checked]
  by (simp add: merged_projection_def)

text \<open>The renaming, the tightened bounds and the ReLU link are all checked.\<close>

lemma merged_projection_rejections:
  \<comment> \<open>Swapping two variables of the renaming.\<close>
  "\<not> check_projection merged_source (Projection merged_facts [0, 4, 1] merged_rows [merged_link]) merged_result"
  \<comment> \<open>A bound tighter than the source implies (z <= 5/4).\<close>
  "\<not> check_projection merged_source merged_projection
       (merged_result\<lparr>rat_query_bounds := [RatLower 0 (-1), RatUpper 0 1, RatLower 1 0, RatUpper 1 1,
          RatLower 2 (1 / 2), RatUpper 2 (5 / 4)]\<rparr>)"
  \<comment> \<open>A ReLU link without the equality witnesses for x3 = x0.\<close>
  "\<not> check_projection merged_source (Projection merged_facts [0, 1, 4] merged_rows [Relu_Link 3 1 [] []])
       merged_result"
  \<comment> \<open>A ReLU link to a ReLU the source does not have.\<close>
  "\<not> check_projection merged_source (Projection merged_facts [0, 1, 4] merged_rows [Relu_Link 0 1 [] []])
       merged_result"
  \<comment> \<open>A fact whose bound is not implied (x3 <= 1/2).\<close>
  "\<not> check_projection merged_source
       (Projection (Fact_Bound (RatUpper 3 (1 / 2)) [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] # tl merged_facts)
         [0, 1, 4] merged_rows [merged_link]) merged_result"
  by code_simp+

section \<open>ReLU facts\<close>

text \<open>
  Two auxiliary-form ReLUs: f = x1 = ReLU(x0), f - b - x2 = 0, with x0 in
  [-1, 1/2]; and g = x4 = ReLU(x3), g - c - x5 = 0, with x3 in [-2, -1].
  These are ReluConstraint::getEntailedTightenings conclusions in the
  unknown and inactive phases. The fact checks derive f <= 1/2
  (Relu_Upper), x2 <= 1 (Relu_Aux_Upper) and the inactive phase of the
  second ReLU, hence g <= 0.
\<close>

definition relu_facts_source :: rat_query where
  "relu_facts_source = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 1), ((-1), 0), ((-1), 2)]) 0,
       RatEq (RatExpr 0 [(1, 4), ((-1), 3), ((-1), 5)]) 0],
     rat_query_bounds = [RatLower 0 (-1), RatUpper 0 (1 / 2), RatLower 1 0, RatUpper 1 2, RatLower 2 0,
       RatUpper 2 3, RatLower 3 (-2), RatUpper 3 (-1), RatLower 4 0, RatUpper 4 2, RatLower 5 0, RatUpper 5 4],
     rat_relu_atoms = [ReLU 0 1, ReLU 3 4]\<rparr>"

definition relu_facts :: "fact list" where
  "relu_facts =
    [Fact_Hull 0 1, Fact_Hull 3 4,
     Fact_Bound (RatLower 5 1) [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0],
     Fact_Relu_Upper 0 1 (1 / 2) (1 / 2),
     Fact_Relu_Aux_Upper 0 1 2 (-1) 1
       [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
       [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
     Fact_Phase_Inactive 3 4 (RatUpper 3 (-1))
       [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
     Fact_Bound (RatUpper 4 0) [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]"

lemma relu_facts_derive_bounds:
  "(case apply_facts relu_facts_source relu_facts of
      None \<Rightarrow> False
    | Some R \<Rightarrow> {RatUpper 1 (1 / 2), RatUpper 2 1, RatUpper 4 0, RatLower 5 1} \<subseteq> set (rat_query_bounds R))"
  by code_simp

lemma relu_fact_rejections:
  \<comment> \<open>Relu_Upper cannot conclude less than max(0, u).\<close>
  "apply_facts relu_facts_source [Fact_Relu_Upper 0 1 (1 / 2) (1 / 4)] = None"
  \<comment> \<open>Relu_Aux_Upper cannot conclude less than max(0, -l).\<close>
  "apply_facts relu_facts_source [Fact_Relu_Aux_Upper 0 1 2 (-1) (1 / 2)
     [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] = None"
  \<comment> \<open>The first ReLU's phase is not decided: x0 <= 1/2 is not a nonpositive bound.\<close>
  "apply_facts relu_facts_source [Fact_Phase_Inactive 0 1 (RatUpper 0 (1 / 2))
     [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]] = None"
  \<comment> \<open>A hull fact needs the ReLU.\<close>
  "apply_facts relu_facts_source [Fact_Hull 1 0] = None"
  by code_simp+

section \<open>Tolerance-based snapping is rejected\<close>

text \<open>
  Marabou's preprocessor treats an interval narrower than 10^-5 as fixed and
  sets its upper bound to its lower bound (PREPROCESSOR_ALMOST_FIXED_THRESHOLD).
  Here x0 is in [0, 10^-6] and x1 = x0 >= 10^-6, so x0 = x1 = 10^-6 is the
  only model. Snapping x0 to 0 gives a query with no model. Since the source
  is satisfiable, no projection onto the snapped query can be accepted.
\<close>

definition narrow_source :: rat_query where
  "narrow_source = \<lparr>rat_linear_atoms = [RatEq (RatExpr 0 [(1, 0), ((-1), 1)]) 0],
     rat_query_bounds = [RatLower 0 0, RatUpper 0 (1 / 1000000), RatLower 1 (1 / 1000000), RatUpper 1 1],
     rat_relu_atoms = []\<rparr>"

definition snapped :: rat_query where
  "snapped = narrow_source\<lparr>rat_query_bounds :=
     [RatLower 0 0, RatUpper 0 0, RatLower 1 (1 / 1000000), RatUpper 1 1]\<rparr>"

lemma narrow_source_has_model:
  "check_rat_assignment narrow_source [(0, 1 / 1000000), (1, 1 / 1000000)]"
  by code_simp

lemma snapped_unsatisfiable:
  "unsatisfiable (embed_query snapped)"
  by (rule check_certificate_sound[of _ "Linear_Unsat [0, 1, 0, 1, 1, 0]"]) code_simp

theorem snapped_projection_rejected:
  "\<not> check_projection narrow_source pr snapped"
  by (rule check_projection_rejects_false_unsat[OF
        check_rat_assignment_sound[OF narrow_source_has_model] snapped_unsatisfiable])

end
