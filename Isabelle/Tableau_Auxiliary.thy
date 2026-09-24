theory Tableau_Auxiliary
  imports Query_Semantics
begin

text \<open>
  One exact mathematical step corresponding to
  src/engine/Engine.cpp::addAuxiliaryVariables: append coefficient -1 for a
  fresh variable, fix its lower and upper bounds to the old scalar, and set
  the equation scalar to zero. This does not verify C++ allocation or mutation.
  Syntactic support includes variables with zero coefficients.
\<close>

fun linexpr_vars :: "linexpr \<Rightarrow> var set" where
  "linexpr_vars (Linexpr c ts) = snd ` set ts"

fun linear_vars :: "linear_constraint \<Rightarrow> var set" where
  "linear_vars (LinearEq e b) = linexpr_vars e"
| "linear_vars (LinearLe e b) = linexpr_vars e"
| "linear_vars (LinearGe e b) = linexpr_vars e"

fun bound_vars :: "bound \<Rightarrow> var set" where
  "bound_vars (Lower x l) = {x}"
| "bound_vars (Upper x u) = {x}"

fun relu_vars :: "relu_constraint \<Rightarrow> var set" where
  "relu_vars (ReLU x y) = {x, y}"

definition query_vars :: "query \<Rightarrow> var set" where
  "query_vars Q =
    (\<Union>c \<in> set (linear_atoms Q). linear_vars c) \<union>
    (\<Union>b \<in> set (query_bounds Q). bound_vars b) \<union>
    (\<Union>r \<in> set (relu_atoms Q). relu_vars r)"

lemma eval_linexpr_vars_cong:
  assumes "\<And>x. x \<in> linexpr_vars e \<Longrightarrow> v x = w x"
  shows "eval_linexpr v e = eval_linexpr w e"
proof (cases e)
  case (Linexpr c ts)
  have "eval_terms v ts = eval_terms w ts"
  proof (rule eval_terms_cong)
    fix a x
    assume "(a, x) \<in> set ts"
    then have "snd (a, x) \<in> snd ` set ts" by (rule imageI)
    then show "v x = w x" using assms Linexpr by simp
  qed
  then show ?thesis by (simp add: Linexpr)
qed

lemma satisfies_linear_vars_cong:
  assumes "\<And>x. x \<in> linear_vars c \<Longrightarrow> v x = w x"
  shows "satisfies_linear v c \<longleftrightarrow> satisfies_linear w c"
proof (cases c)
  case (LinearEq e b)
  have "eval_linexpr v e = eval_linexpr w e"
    by (rule eval_linexpr_vars_cong) (use assms LinearEq in simp)
  then show ?thesis by (simp add: LinearEq)
next
  case (LinearLe e b)
  have "eval_linexpr v e = eval_linexpr w e"
    by (rule eval_linexpr_vars_cong) (use assms LinearLe in simp)
  then show ?thesis by (simp add: LinearLe)
next
  case (LinearGe e b)
  have "eval_linexpr v e = eval_linexpr w e"
    by (rule eval_linexpr_vars_cong) (use assms LinearGe in simp)
  then show ?thesis by (simp add: LinearGe)
qed

lemma satisfies_bound_vars_cong:
  assumes "\<And>x. x \<in> bound_vars b \<Longrightarrow> v x = w x"
  shows "satisfies_bound v b \<longleftrightarrow> satisfies_bound w b"
  using assms by (cases b) auto

lemma satisfies_relu_vars_cong:
  assumes "\<And>x. x \<in> relu_vars r \<Longrightarrow> v x = w x"
  shows "satisfies_relu_constraint v r \<longleftrightarrow> satisfies_relu_constraint w r"
  using assms by (cases r) (auto simp: satisfies_relu_def)

lemma satisfies_query_vars_cong:
  assumes "\<And>x. x \<in> query_vars Q \<Longrightarrow> v x = w x"
  shows "satisfies_query v Q \<longleftrightarrow> satisfies_query w Q"
proof -
  have linear: "\<And>c. c \<in> set (linear_atoms Q) \<Longrightarrow>
    satisfies_linear v c \<longleftrightarrow> satisfies_linear w c"
    by (rule satisfies_linear_vars_cong) (use assms in \<open>auto simp: query_vars_def\<close>)
  have bounds: "\<And>b. b \<in> set (query_bounds Q) \<Longrightarrow>
    satisfies_bound v b \<longleftrightarrow> satisfies_bound w b"
    by (rule satisfies_bound_vars_cong) (use assms in \<open>auto simp: query_vars_def\<close>)
  have relus: "\<And>r. r \<in> set (relu_atoms Q) \<Longrightarrow>
    satisfies_relu_constraint v r \<longleftrightarrow> satisfies_relu_constraint w r"
    by (rule satisfies_relu_vars_cong) (use assms in \<open>auto simp: query_vars_def\<close>)
  show ?thesis using linear bounds relus unfolding satisfies_query_def by blast
qed

lemma satisfies_query_fresh_update:
  assumes "s \<notin> query_vars Q"
  shows "satisfies_query (v(s := d)) Q \<longleftrightarrow> satisfies_query v Q"
  by (rule satisfies_query_vars_cong) (use assms in auto)

definition introduce_fixed_aux ::
  "query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> linexpr \<Rightarrow> real \<Rightarrow> query" where
  "introduce_fixed_aux Q i s e b = Q\<lparr>
    linear_atoms := (linear_atoms Q)[i := LinearEq (add_linexpr e (Linexpr 0 [(-1, s)])) 0],
    query_bounds := query_bounds Q @ [Lower s b, Upper s b]\<rparr>"

text \<open>
  Selection is by index, so the other atoms retain their order and duplicate
  equations are not deleted. The two bounds express s=b. Even without
  freshness the following pointwise characterization holds; freshness is
  essential for extending every original model and preserving satisfiability.
\<close>

lemma satisfies_introduce_fixed_aux_iff:
  assumes index: "i < length (linear_atoms Q)"
      and selected: "linear_atoms Q ! i = LinearEq e b"
  shows "satisfies_query v (introduce_fixed_aux Q i s e b) \<longleftrightarrow>
    satisfies_query v Q \<and> v s = b"
  using index selected
  by (auto simp: introduce_fixed_aux_def satisfies_query_def all_set_conv_all_nth
      nth_list_update split: if_splits)

lemma models_introduce_fixed_aux:
  assumes "i < length (linear_atoms Q)" "linear_atoms Q ! i = LinearEq e b"
  shows "models (introduce_fixed_aux Q i s e b) = {v \<in> models Q. v s = b}"
  using satisfies_introduce_fixed_aux_iff[OF assms]
  by (auto simp: models_def)

theorem fixed_aux_model_extension:
  assumes "i < length (linear_atoms Q)" "linear_atoms Q ! i = LinearEq e b"
      and "s \<notin> query_vars Q"
  shows "satisfies_query (v(s := b)) (introduce_fixed_aux Q i s e b) \<longleftrightarrow>
    satisfies_query v Q"
  by (simp add: satisfies_introduce_fixed_aux_iff[OF assms(1,2)]
      satisfies_query_fresh_update[OF assms(3)])

theorem fixed_aux_model_projection:
  assumes "i < length (linear_atoms Q)" "linear_atoms Q ! i = LinearEq e b"
      and "s \<notin> query_vars Q"
      and "satisfies_query v (introduce_fixed_aux Q i s e b)"
  shows "satisfies_query (v(s := d)) Q"
  using assms(4)
  by (simp add: satisfies_introduce_fixed_aux_iff[OF assms(1,2)]
      satisfies_query_fresh_update[OF assms(3)])

theorem satisfiable_introduce_fixed_aux_iff:
  assumes "i < length (linear_atoms Q)" "linear_atoms Q ! i = LinearEq e b"
      and "s \<notin> query_vars Q"
  shows "satisfiable (introduce_fixed_aux Q i s e b) \<longleftrightarrow> satisfiable Q"
proof
  assume "satisfiable (introduce_fixed_aux Q i s e b)"
  then obtain v where "satisfies_query v (introduce_fixed_aux Q i s e b)"
    unfolding satisfiable_def by blast
  then have "satisfies_query v Q"
    by (simp add: satisfies_introduce_fixed_aux_iff[OF assms(1,2)])
  then show "satisfiable Q" unfolding satisfiable_def by blast
next
  assume "satisfiable Q"
  then obtain v where "satisfies_query v Q" unfolding satisfiable_def by blast
  then have "satisfies_query (v(s := b)) (introduce_fixed_aux Q i s e b)"
    using fixed_aux_model_extension[OF assms] by blast
  then show "satisfiable (introduce_fixed_aux Q i s e b)"
    unfolding satisfiable_def by blast
qed

corollary unsatisfiable_introduce_fixed_aux_iff:
  assumes "i < length (linear_atoms Q)" "linear_atoms Q ! i = LinearEq e b"
      and "s \<notin> query_vars Q"
  shows "unsatisfiable (introduce_fixed_aux Q i s e b) \<longleftrightarrow> unsatisfiable Q"
  by (simp add: unsatisfiable_def satisfiable_introduce_fixed_aux_iff[OF assms])

end
