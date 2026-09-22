theory Query_Semantics
  imports ReLU_Constraints
begin

definition satisfies_query :: "valuation \<Rightarrow> query \<Rightarrow> bool" where
  "satisfies_query v Q \<longleftrightarrow>
     (\<forall>c \<in> set (linear_atoms Q). satisfies_linear v c) \<and>
     (\<forall>b \<in> set (query_bounds Q). satisfies_bound v b) \<and>
     (\<forall>r \<in> set (relu_atoms Q). satisfies_relu_constraint v r)"

definition models :: "query \<Rightarrow> valuation set" where
  "models Q = {v. satisfies_query v Q}"

definition satisfiable :: "query \<Rightarrow> bool" where
  "satisfiable Q \<longleftrightarrow> (\<exists>v. satisfies_query v Q)"

definition unsatisfiable :: "query \<Rightarrow> bool" where
  "unsatisfiable Q \<longleftrightarrow> \<not> satisfiable Q"

lemma satisfiable_iff_models_nonempty:
  "satisfiable Q \<longleftrightarrow> models Q \<noteq> {}"
  by (auto simp: satisfiable_def models_def)

lemma unsatisfiable_iff_no_valuation:
  "unsatisfiable Q \<longleftrightarrow> (\<forall>v. \<not> satisfies_query v Q)"
  by (simp add: unsatisfiable_def satisfiable_def)

lemma unsatisfiable_iff_models_empty:
  "unsatisfiable Q \<longleftrightarrow> models Q = {}"
  by (simp add: unsatisfiable_def satisfiable_iff_models_nonempty)

lemma query_relu:
  assumes "satisfies_query v Q" "ReLU x y \<in> set (relu_atoms Q)"
  shows "satisfies_relu v x y"
  using assms by (auto simp: satisfies_query_def)

lemma query_inconsistent_bounds:
  assumes "Lower x l \<in> set (query_bounds Q)"
      and "Upper x u \<in> set (query_bounds Q)" and "u < l"
  shows "unsatisfiable Q"
proof (unfold unsatisfiable_iff_no_valuation, intro allI notI)
  fix v
  assume "satisfies_query v Q"
  then have "satisfies_bound v (Lower x l)" "satisfies_bound v (Upper x u)"
    using assms(1,2) unfolding satisfies_query_def by auto
  with assms(3) show False by (rule inconsistent_bounds)
qed

end
