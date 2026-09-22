theory ReLU_Splitting
  imports Query_Semantics
begin

text \<open>
  Mathematical replacement of a ReLU by one phase. All copies of the selected
  atom are removed: duplicate conjuncts have the same semantics. Source:
  src/engine/ReluConstraint.cpp, getActiveSplit and getInactiveSplit.
  Unlike the implementation, these definitions explicitly state the equalities
  and do not depend on auxiliary variables or an existing output lower bound.
\<close>

definition active_split :: "query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> query" where
  "active_split Q x y = Q\<lparr>
     linear_atoms := LinearEq (Linexpr 0 [(1, y), (-1, x)]) 0 # linear_atoms Q,
     query_bounds := Lower x 0 # query_bounds Q,
     relu_atoms := filter (\<lambda>r. r \<noteq> ReLU x y) (relu_atoms Q)\<rparr>"

definition inactive_split :: "query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> query" where
  "inactive_split Q x y = Q\<lparr>
     linear_atoms := LinearEq (var_expr y) 0 # linear_atoms Q,
     query_bounds := Upper x 0 # query_bounds Q,
     relu_atoms := filter (\<lambda>r. r \<noteq> ReLU x y) (relu_atoms Q)\<rparr>"

lemma satisfies_active_split_iff:
  "satisfies_query v (active_split Q x y) \<longleftrightarrow>
   satisfies_query v Q \<and> 0 \<le> v x \<and> v y = v x"
  by (auto simp: active_split_def satisfies_query_def satisfies_relu_def relu_def max_def)

lemma satisfied_relu_can_be_removed:
  assumes "satisfies_relu v x y"
  shows "(\<forall>r \<in> set (filter (\<lambda>r. r \<noteq> ReLU x y) rs).
            satisfies_relu_constraint v r) \<longleftrightarrow>
         (\<forall>r \<in> set rs. satisfies_relu_constraint v r)"
proof -
  have "satisfies_relu_constraint v (ReLU x y)" using assms by simp
  then show ?thesis by (simp only: set_filter; blast)
qed

lemma satisfies_inactive_split_iff:
  "satisfies_query v (inactive_split Q x y) \<longleftrightarrow>
   satisfies_query v Q \<and> v x \<le> 0 \<and> v y = 0"
proof (cases "v x \<le> 0 \<and> v y = 0")
  case True
  then have relu: "satisfies_relu v x y"
    by (simp add: satisfies_relu_def relu_of_nonpositive)
  show ?thesis
    using True satisfied_relu_can_be_removed[OF relu, of "relu_atoms Q"]
    by (auto simp: inactive_split_def satisfies_query_def)
next
  case False
  then show ?thesis by (auto simp: inactive_split_def satisfies_query_def)
qed

theorem query_relu_split:
  assumes member: "ReLU x y \<in> set (relu_atoms Q)"
  shows "satisfies_query v Q \<longleftrightarrow>
    satisfies_query v (active_split Q x y) \<or>
    satisfies_query v (inactive_split Q x y)"
proof -
  have phase: "satisfies_query v Q \<Longrightarrow>
    (v x \<le> 0 \<and> v y = 0) \<or> (0 \<le> v x \<and> v y = v x)"
    using query_relu[OF _ member] satisfies_relu_phase_decomposition by blast
  show ?thesis
    using phase by (auto simp: satisfies_active_split_iff satisfies_inactive_split_iff)
qed

theorem models_relu_split:
  assumes "ReLU x y \<in> set (relu_atoms Q)"
  shows "models Q = models (active_split Q x y) \<union> models (inactive_split Q x y)"
  using query_relu_split[OF assms] by (auto simp: models_def)

theorem satisfiable_relu_split:
  assumes "ReLU x y \<in> set (relu_atoms Q)"
  shows "satisfiable Q \<longleftrightarrow>
    satisfiable (active_split Q x y) \<or> satisfiable (inactive_split Q x y)"
  using query_relu_split[OF assms] unfolding satisfiable_def by blast

theorem unsatisfiable_relu_split:
  assumes "ReLU x y \<in> set (relu_atoms Q)"
      and "unsatisfiable (active_split Q x y)"
      and "unsatisfiable (inactive_split Q x y)"
  shows "unsatisfiable Q"
  using satisfiable_relu_split[OF assms(1)] assms(2,3)
  unfolding unsatisfiable_def by blast

lemma split_removes_selected_relu:
  "ReLU x y \<notin> set (relu_atoms (active_split Q x y))"
  "ReLU x y \<notin> set (relu_atoms (inactive_split Q x y))"
  by (simp_all add: active_split_def inactive_split_def)

end
