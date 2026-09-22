theory Rational_Linear_Implication
  imports Rational_Linear_Certificates
begin

text \<open>
  To establish a target expression t \<le> 0, form a nonnegative weighted sum s
  of the current query's normalized inequalities. Check that t - s is a
  nonpositive constant. Exact cancellation permits duplicate variable terms;
  non-strict comparison permits equality and weaker target bounds.

  Marabou source counterpart: src/proofs/UnsatCertificateUtils.cpp,
  computeBound and getExplanationRowCombination. An imported explanation is
  reconstructed into these weights; this theory does not trust the decoder,
  floating-point calculation, or the claimed implication.
\<close>

definition constant_nonpositive :: "rat_linexpr \<Rightarrow> bool" where
  "constant_nonpositive e \<longleftrightarrow>
     rat_constant e \<le> 0 \<and>
     list_all (\<lambda>t. fst t = 0) (collect_terms (rat_terms e))"

lemma constant_nonpositive_sound:
  assumes "constant_nonpositive e"
  shows "eval_rat_expr v e \<le> 0"
proof -
  obtain c ts where e: "e = RatExpr c ts" by (cases e) simp
  have nonpos: "c \<le> 0" and zero: "list_all (\<lambda>t. fst t = 0) (collect_terms ts)"
    using assms by (simp_all add: e constant_nonpositive_def)
  have "eval_rat_terms v (collect_terms ts) = 0"
    using zero by (rule all_zero_terms_eval)
  then have "eval_rat_terms v ts = 0" by simp
  with nonpos show ?thesis by (simp add: e of_rat_less_eq)
qed

definition check_linear_implication ::
  "rat_query \<Rightarrow> rat_linexpr \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_linear_implication Q target ws \<longleftrightarrow>
     (case weighted_sum ws (normalize_query Q) of
        None \<Rightarrow> False
      | Some s \<Rightarrow> constant_nonpositive (rat_add target (rat_scale (-1) s)))"

theorem check_linear_implication_sound:
  assumes checked: "check_linear_implication Q target ws"
      and model: "satisfies_query v (embed_query Q)"
  shows "eval_rat_expr v target \<le> 0"
proof -
  obtain s where sum: "weighted_sum ws (normalize_query Q) = Some s"
      and residual: "constant_nonpositive (rat_add target (rat_scale (-1) s))"
    using checked by (auto simp: check_linear_implication_def split: option.splits)
  have rows: "\<forall>e \<in> set (normalize_query Q). eval_rat_expr v e \<le> 0"
    using model by (rule query_implies_normalized)
  have sum_le: "eval_rat_expr v s \<le> 0"
    by (rule weighted_sum_nonpositive[OF sum rows])
  have "eval_rat_expr v (rat_add target (rat_scale (-1) s)) \<le> 0"
    by (rule constant_nonpositive_sound[OF residual])
  then have "eval_rat_expr v target - eval_rat_expr v s \<le> 0" by simp
  with sum_le show ?thesis by linarith
qed

definition check_linear_bound :: "rat_query \<Rightarrow> rat_bound \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_linear_bound Q b ws \<longleftrightarrow> check_linear_implication Q (normalize_bound b) ws"

theorem check_linear_bound_sound:
  assumes "check_linear_bound Q b ws"
      and "satisfies_query v (embed_query Q)"
  shows "satisfies_bound v (embed_bound b)"
proof -
  have checked: "check_linear_implication Q (normalize_bound b) ws"
    using assms(1) by (simp add: check_linear_bound_def)
  have "eval_rat_expr v (normalize_bound b) \<le> 0"
    by (rule check_linear_implication_sound[OF checked assms(2)])
  then show ?thesis by (simp only: normalize_bound_correct)
qed

theorem rat_linear_bound_preserves_models:
  assumes "check_linear_bound Q b ws"
  shows "models (embed_query (rat_add_bound Q b)) = models (embed_query Q)"
  using check_linear_bound_sound[OF assms]
  by (auto simp: models_def satisfies_rat_add_bound_iff)

corollary unsatisfiable_linear_bound:
  assumes "check_linear_bound Q b ws"
      and "unsatisfiable (embed_query (rat_add_bound Q b))"
  shows "unsatisfiable (embed_query Q)"
  using rat_linear_bound_preserves_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

end
