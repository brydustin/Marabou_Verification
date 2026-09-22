theory Linear_Constraints
  imports Marabou_Semantics
begin

fun satisfies_linear :: "valuation \<Rightarrow> linear_constraint \<Rightarrow> bool" where
  "satisfies_linear v (LinearEq e b) = (eval_linexpr v e = b)"
| "satisfies_linear v (LinearLe e b) = (eval_linexpr v e \<le> b)"
| "satisfies_linear v (LinearGe e b) = (b \<le> eval_linexpr v e)"

fun satisfies_bound :: "valuation \<Rightarrow> bound \<Rightarrow> bool" where
  "satisfies_bound v (Lower x l) = (l \<le> v x)"
| "satisfies_bound v (Upper x u) = (v x \<le> u)"

lemma linear_eq_iff_two_inequalities:
  "satisfies_linear v (LinearEq e b) \<longleftrightarrow>
   satisfies_linear v (LinearLe e b) \<and> satisfies_linear v (LinearGe e b)"
  by auto

lemma lower_bound_as_linear:
  "satisfies_bound v (Lower x l) \<longleftrightarrow>
   satisfies_linear v (LinearGe (var_expr x) l)"
  by simp

lemma upper_bound_as_linear:
  "satisfies_bound v (Upper x u) \<longleftrightarrow>
   satisfies_linear v (LinearLe (var_expr x) u)"
  by simp

lemma inconsistent_bounds:
  assumes "u < l" "satisfies_bound v (Lower x l)" "satisfies_bound v (Upper x u)"
  shows False
  using assms by auto

text \<open>A first algebraic building block for exact linear certificates.\<close>

lemma linear_le_add:
  assumes "satisfies_linear v (LinearLe e b)"
      and "satisfies_linear v (LinearLe f c)"
  shows "satisfies_linear v (LinearLe (add_linexpr e f) (b + c))"
  using assms by (simp add: add_mono)

lemma linear_le_scale_nonnegative:
  assumes "0 \<le> a" "satisfies_linear v (LinearLe e b)"
  shows "satisfies_linear v (LinearLe (scale_linexpr a e) (a * b))"
  using assms by (simp add: mult_left_mono)

end
