theory Inequality_Auxiliary
  imports Tableau_Auxiliary
begin

text \<open>
  One mathematical step corresponding to
  src/engine/Preprocessor.cpp::makeAllEquationsEqualities (lines 224--244).
  Marabou appends coefficient +1 in BOTH directions: e <= b becomes
  e+s=b with s>=0; e >= b becomes e+s=b with s<=0.
  No bound in the other direction is supplied by this transformation.
  We select one atom by index and require global freshness for model extension.
  C++ allocation, mutation and the surrounding preprocessor remain unverified.
\<close>

datatype inequality_direction = Slack_Le | Slack_Ge

fun inequality_atom :: "inequality_direction \<Rightarrow> linexpr \<Rightarrow> real \<Rightarrow> linear_constraint" where
  "inequality_atom Slack_Le e b = LinearLe e b"
| "inequality_atom Slack_Ge e b = LinearGe e b"

fun inequality_aux_bound :: "inequality_direction \<Rightarrow> var \<Rightarrow> bound" where
  "inequality_aux_bound Slack_Le s = Lower s 0"
| "inequality_aux_bound Slack_Ge s = Upper s 0"

definition introduce_inequality_aux ::
  "query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> inequality_direction \<Rightarrow> linexpr \<Rightarrow> real \<Rightarrow> query" where
  "introduce_inequality_aux Q i s dir e b = Q\<lparr>
    linear_atoms := (linear_atoms Q)[i := LinearEq (add_linexpr e (Linexpr 0 [(1, s)])) b],
    query_bounds := query_bounds Q @ [inequality_aux_bound dir s]\<rparr>"

lemma satisfies_introduce_inequality_aux_iff:
  assumes index: "i < length (linear_atoms Q)"
      and selected: "linear_atoms Q ! i = inequality_atom dir e b"
  shows "satisfies_query v (introduce_inequality_aux Q i s dir e b) \<longleftrightarrow>
    satisfies_query v Q \<and> v s = b - eval_linexpr v e"
  using index selected
  by (cases dir; auto simp: introduce_inequality_aux_def satisfies_query_def
      all_set_conv_all_nth nth_list_update split: if_splits; linarith)

lemma models_introduce_inequality_aux:
  assumes "i < length (linear_atoms Q)"
      and "linear_atoms Q ! i = inequality_atom dir e b"
  shows "models (introduce_inequality_aux Q i s dir e b) =
    {v \<in> models Q. v s = b - eval_linexpr v e}"
  using satisfies_introduce_inequality_aux_iff[OF assms]
  by (auto simp: models_def)

theorem inequality_aux_model_extension:
  assumes index: "i < length (linear_atoms Q)"
      and selected: "linear_atoms Q ! i = inequality_atom dir e b"
      and fresh: "s \<notin> query_vars Q"
  shows "satisfies_query (v(s := b - eval_linexpr v e))
      (introduce_inequality_aux Q i s dir e b) \<longleftrightarrow> satisfies_query v Q"
proof -
  have member: "inequality_atom dir e b \<in> set (linear_atoms Q)"
    using index selected by (metis nth_mem)
  have fresh_expr: "s \<notin> linexpr_vars e"
    using member fresh by (cases dir) (auto simp: query_vars_def)
  have eval: "eval_linexpr (v(s := b - eval_linexpr v e)) e = eval_linexpr v e"
    by (rule eval_linexpr_vars_cong) (use fresh_expr in auto)
  show ?thesis
    by (simp add: satisfies_introduce_inequality_aux_iff[OF index selected]
        satisfies_query_fresh_update[OF fresh] eval)
qed

theorem inequality_aux_model_projection:
  assumes "i < length (linear_atoms Q)"
      and "linear_atoms Q ! i = inequality_atom dir e b"
      and "s \<notin> query_vars Q"
      and "satisfies_query v (introduce_inequality_aux Q i s dir e b)"
  shows "satisfies_query (v(s := d)) Q"
  using assms(4)
  by (simp add: satisfies_introduce_inequality_aux_iff[OF assms(1,2)]
      satisfies_query_fresh_update[OF assms(3)])

theorem satisfiable_introduce_inequality_aux_iff:
  assumes "i < length (linear_atoms Q)"
      and "linear_atoms Q ! i = inequality_atom dir e b"
      and "s \<notin> query_vars Q"
  shows "satisfiable (introduce_inequality_aux Q i s dir e b) \<longleftrightarrow> satisfiable Q"
proof
  assume "satisfiable (introduce_inequality_aux Q i s dir e b)"
  then obtain v where "satisfies_query v (introduce_inequality_aux Q i s dir e b)"
    unfolding satisfiable_def by blast
  then have "satisfies_query v Q"
    by (simp add: satisfies_introduce_inequality_aux_iff[OF assms(1,2)])
  then show "satisfiable Q" unfolding satisfiable_def by blast
next
  assume "satisfiable Q"
  then obtain v where "satisfies_query v Q" unfolding satisfiable_def by blast
  then have "satisfies_query (v(s := b - eval_linexpr v e))
      (introduce_inequality_aux Q i s dir e b)"
    using inequality_aux_model_extension[OF assms] by blast
  then show "satisfiable (introduce_inequality_aux Q i s dir e b)"
    unfolding satisfiable_def by blast
qed

corollary unsatisfiable_introduce_inequality_aux_iff:
  assumes "i < length (linear_atoms Q)"
      and "linear_atoms Q ! i = inequality_atom dir e b"
      and "s \<notin> query_vars Q"
  shows "unsatisfiable (introduce_inequality_aux Q i s dir e b) \<longleftrightarrow> unsatisfiable Q"
  by (simp add: unsatisfiable_def satisfiable_introduce_inequality_aux_iff[OF assms])

end
