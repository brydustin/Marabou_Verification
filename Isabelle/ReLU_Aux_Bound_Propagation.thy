theory ReLU_Aux_Bound_Propagation
  imports ReLU_Bound_Propagation Rational_Linear_Implication
begin

text \<open>
  With y = ReLU(x) and y - x - a = 0, a = ReLU(-x). Thus a lower
  bound on x gives an upper bound on a. The auxiliary equation is proved
  by two exact linear implications from the current query, not assumed
  from Marabou's auxiliary-variable metadata.

  Source: src/engine/ReluConstraint.cpp::notifyLowerBound, variable == _b,
  and src/proofs/Checker.cpp::checkReluLemma. The negative-input branch
  propagates -lower to aux; the nonnegative branches propagate zero.
  Our mathematical guard covers both, without floating-point tolerances.
\<close>

lemma relu_aux_identity:
  "relu x - x = relu (-x)"
  by (auto simp: relu_def max_def)

lemma relu_aux_upper_bound:
  assumes lower: "l \<le> x" and relu_eq: "y = relu x"
      and auxiliary: "y - x - a = 0"
  shows "a \<le> max 0 (-l)"
proof -
  have aux: "a = relu (-x)"
    using relu_eq auxiliary relu_aux_identity[of x] by linarith
  have "-x \<le> -l" using lower by simp
  from relu_upper_bound[OF this] show ?thesis by (simp only: aux)
qed

definition relu_aux_expr :: "var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_linexpr" where
  "relu_aux_expr x y a = RatExpr 0 [(1, y), (-1, x), (-1, a)]"

lemma eval_relu_aux_expr [simp]:
  "eval_rat_expr v (relu_aux_expr x y a) = v y - v x - v a"
  by (simp add: relu_aux_expr_def)

definition check_relu_aux_upper_bound ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat \<Rightarrow> rat
    \<Rightarrow> rat list \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_relu_aux_upper_bound Q x y a l u pos neg \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and>
     RatLower x l \<in> set (rat_query_bounds Q) \<and>
     check_linear_implication Q (relu_aux_expr x y a) pos \<and>
     check_linear_implication Q (rat_scale (-1) (relu_aux_expr x y a)) neg \<and>
     max 0 (-l) \<le> u"

theorem check_relu_aux_upper_bound_sound:
  assumes checked: "check_relu_aux_upper_bound Q x y a l u pos neg"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_bound v (embed_bound (RatUpper a u))"
proof -
  have relu: "v y = relu (v x)" and lower: "of_rat l \<le> v x"
    using checked model
    by (auto simp: check_relu_aux_upper_bound_def embed_query_def
        satisfies_query_def satisfies_relu_def)
  have positive: "check_linear_implication Q (relu_aux_expr x y a) pos"
      and negative: "check_linear_implication Q (rat_scale (-1) (relu_aux_expr x y a)) neg"
    using checked by (simp_all add: check_relu_aux_upper_bound_def)
  have "v y - v x - v a \<le> 0"
    using check_linear_implication_sound[OF positive model] by simp
  moreover have "-(v y - v x - v a) \<le> 0"
    using check_linear_implication_sound[OF negative model] by simp
  ultimately have equation: "v y - v x - v a = 0" by linarith
  have propagated: "v a \<le> max 0 (-(of_rat l))"
    by (rule relu_aux_upper_bound[OF lower relu equation])
  have nonnegative: "0 \<le> u" and cap: "-l \<le> u"
    using checked by (auto simp: check_relu_aux_upper_bound_def)
  have "(0::real) \<le> of_rat u" and "(of_rat (-l)::real) \<le> of_rat u"
    using nonnegative cap by (simp_all add: of_rat_less_eq)
  then have "max 0 (-(of_rat l)) \<le> (of_rat u::real)"
    by (simp add: of_rat_minus)
  with propagated have "v a \<le> of_rat u" by (rule order_trans)
  then show ?thesis by simp
qed

theorem rat_relu_aux_upper_preserves_models:
  assumes "check_relu_aux_upper_bound Q x y a l u pos neg"
  shows "models (embed_query (rat_add_bound Q (RatUpper a u))) = models (embed_query Q)"
  using check_relu_aux_upper_bound_sound[OF assms]
  by (auto simp: models_def satisfies_rat_add_bound_iff)

corollary unsatisfiable_relu_aux_upper_bound:
  assumes "check_relu_aux_upper_bound Q x y a l u pos neg"
      and "unsatisfiable (embed_query (rat_add_bound Q (RatUpper a u)))"
  shows "unsatisfiable (embed_query Q)"
  using rat_relu_aux_upper_preserves_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

end
