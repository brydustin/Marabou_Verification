theory ReLU_Output_Bound_Propagation
  imports ReLU_Aux_Bound_Propagation
begin

text \<open>
  A strictly positive lower bound on the OUTPUT fixes the active phase:
  y = ReLU(x), 0 < l <= y and y - x - a = 0 imply a = 0.
  This differs from the input-lower rule, which permits l = 0.

  Source: src/engine/ReluConstraint.cpp::notifyLowerBound, variable == _f
  in the positive-bound branch; src/proofs/Checker.cpp::checkReluLemma,
  causingVar == f, LB, affectedVar == aux, UB.
  The native checker uses epsilon; this checker requires exact positivity
  and independently checks both directions of the auxiliary equation.
\<close>

lemma relu_positive_output_aux_zero:
  assumes positive: "0 < l" and lower: "l \<le> y"
      and relu_eq: "y = relu x" and auxiliary: "y - x - a = 0"
  shows "a = 0"
proof -
  have "0 < y" using positive lower by linarith
  then have "y = x" using relu_eq by (auto simp: relu_def max_def split: if_splits)
  then show ?thesis using auxiliary by linarith
qed

definition check_relu_output_aux_upper_bound ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat \<Rightarrow> rat
    \<Rightarrow> rat list \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_relu_output_aux_upper_bound Q x y a l u pos neg \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and>
     RatLower y l \<in> set (rat_query_bounds Q) \<and> 0 < l \<and>
     check_linear_implication Q (relu_aux_expr x y a) pos \<and>
     check_linear_implication Q (rat_scale (-1) (relu_aux_expr x y a)) neg \<and>
     0 \<le> u"

theorem check_relu_output_aux_upper_bound_sound:
  assumes checked: "check_relu_output_aux_upper_bound Q x y a l u pos neg"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_bound v (embed_bound (RatUpper a u))"
proof -
  have relu: "v y = relu (v x)" and lower: "of_rat l \<le> v y"
    using checked model
    by (auto simp: check_relu_output_aux_upper_bound_def embed_query_def
        satisfies_query_def satisfies_relu_def)
  have positive_rat: "0 < l" and cap_rat: "0 \<le> u"
      and positive: "check_linear_implication Q (relu_aux_expr x y a) pos"
      and negative: "check_linear_implication Q (rat_scale (-1) (relu_aux_expr x y a)) neg"
    using checked by (simp_all add: check_relu_output_aux_upper_bound_def)
  have positive_real: "(0::real) < of_rat l"
    using positive_rat by (simp add: of_rat_less)
  have cap_real: "(0::real) \<le> of_rat u"
    using cap_rat by (simp add: of_rat_less_eq)
  have "v y - v x - v a \<le> 0"
    using check_linear_implication_sound[OF positive model] by simp
  moreover have "-(v y - v x - v a) \<le> 0"
    using check_linear_implication_sound[OF negative model] by simp
  ultimately have equation: "v y - v x - v a = 0" by linarith
  have "v a = 0"
    by (rule relu_positive_output_aux_zero[OF positive_real lower relu equation])
  with cap_real show ?thesis by simp
qed

theorem rat_relu_output_aux_upper_preserves_models:
  assumes "check_relu_output_aux_upper_bound Q x y a l u pos neg"
  shows "models (embed_query (rat_add_bound Q (RatUpper a u))) = models (embed_query Q)"
  using check_relu_output_aux_upper_bound_sound[OF assms]
  by (auto simp: models_def satisfies_rat_add_bound_iff)

corollary unsatisfiable_relu_output_aux_upper_bound:
  assumes "check_relu_output_aux_upper_bound Q x y a l u pos neg"
      and "unsatisfiable (embed_query (rat_add_bound Q (RatUpper a u)))"
  shows "unsatisfiable (embed_query Q)"
  using rat_relu_output_aux_upper_preserves_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

end
