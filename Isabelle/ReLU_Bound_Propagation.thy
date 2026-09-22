theory ReLU_Bound_Propagation
  imports Rational_Linear_Constraints
begin

text \<open>
  One exact propagation rule: x \<le> u and y = ReLU(x) imply y \<le> max 0 u.
  Source: src/engine/ReluConstraint.cpp::notifyUpperBound, variable == _b,
  and src/proofs/Checker.cpp::checkReluLemma. The implementation separates
  negative and positive input bounds and uses tolerances. Our guard is exact.
  The input upper bound must already occur in the query. A checked linear
  implication can insert it before this rule is used.
\<close>

lemma relu_upper_bound:
  assumes "x \<le> u"
  shows "relu x \<le> max 0 u"
  using assms by (auto simp: relu_def max_def)

definition check_relu_upper_bound ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat \<Rightarrow> rat \<Rightarrow> bool" where
  "check_relu_upper_bound Q x y u b \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and>
     RatUpper x u \<in> set (rat_query_bounds Q) \<and> max 0 u \<le> b"

theorem check_relu_upper_bound_sound:
  assumes checked: "check_relu_upper_bound Q x y u b"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_bound v (embed_bound (RatUpper y b))"
proof -
  have relu: "satisfies_relu v x y"
    using checked model
    by (auto simp: check_relu_upper_bound_def embed_query_def satisfies_query_def)
  have input: "v x \<le> of_rat u"
    using checked model
    by (auto simp: check_relu_upper_bound_def embed_query_def satisfies_query_def)
  have nonnegative: "(0::real) \<le> of_rat b" and cap: "(of_rat u::real) \<le> of_rat b"
    using checked by (auto simp: check_relu_upper_bound_def of_rat_less_eq)
  have "max 0 (of_rat u) \<le> (of_rat b::real)"
    using nonnegative cap by simp
  with relu_upper_bound[OF input] have "relu (v x) \<le> of_rat b"
    by (rule order_trans)
  with relu show ?thesis by (simp add: satisfies_relu_def)
qed

theorem rat_relu_upper_preserves_models:
  assumes "check_relu_upper_bound Q x y u b"
  shows "models (embed_query (rat_add_bound Q (RatUpper y b))) = models (embed_query Q)"
  using check_relu_upper_bound_sound[OF assms]
  by (auto simp: models_def satisfies_rat_add_bound_iff)

corollary unsatisfiable_relu_upper_bound:
  assumes "check_relu_upper_bound Q x y u b"
      and "unsatisfiable (embed_query (rat_add_bound Q (RatUpper y b)))"
  shows "unsatisfiable (embed_query Q)"
  using rat_relu_upper_preserves_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

end
