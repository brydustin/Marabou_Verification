theory ReLU_Auxiliary
  imports Tableau_Auxiliary ReLU_Aux_Bound_Propagation
begin

text \<open>
  One exact transformation corresponding to
  src/engine/ReluConstraint.cpp::transformToUseAuxVariables. Keep ReLU x y,
  append y-x-a=0, and add a nonnegative lower bound for the fresh auxiliary.
  A supplied input lower bound l also gives a <= max 0 (-l). None omits that
  finite upper bound; no real-valued infinity is introduced.

  The C++ code reads the constraint's stored lower bound and allocates at the
  query's variable count. Here a finite bound must occur in the query and
  freshness is checked against every syntactic variable occurrence.
  This does not model C++ auxiliary metadata, allocation, or mutation.
\<close>

fun relu_aux_bounds :: "var \<Rightarrow> real option \<Rightarrow> bound list" where
  "relu_aux_bounds a None = [Lower a 0]"
| "relu_aux_bounds a (Some l) = [Lower a 0, Upper a (max 0 (-l))]"

fun relu_aux_lower_present :: "query \<Rightarrow> var \<Rightarrow> real option \<Rightarrow> bool" where
  "relu_aux_lower_present Q x None = True"
| "relu_aux_lower_present Q x (Some l) = (Lower x l \<in> set (query_bounds Q))"

definition introduce_relu_aux ::
  "query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> real option \<Rightarrow> query" where
  "introduce_relu_aux Q x y a lower = Q\<lparr>
    linear_atoms := linear_atoms Q @ [LinearEq (Linexpr 0 [(1, y), (-1, x), (-1, a)]) 0],
    query_bounds := query_bounds Q @ relu_aux_bounds a lower\<rparr>"

lemma satisfies_introduce_relu_aux_raw:
  "satisfies_query v (introduce_relu_aux Q x y a lower) \<longleftrightarrow>
    satisfies_query v Q \<and> v a = v y - v x \<and> 0 \<le> v a \<and>
    (case lower of None \<Rightarrow> True | Some l \<Rightarrow> v a \<le> max 0 (-l))"
  by (cases lower; auto simp: introduce_relu_aux_def satisfies_query_def; linarith)

lemma relu_aux_added_bounds:
  assumes selected: "ReLU x y \<in> set (relu_atoms Q)"
      and lower: "relu_aux_lower_present Q x lower"
      and model: "satisfies_query v Q"
      and auxiliary: "v a = v y - v x"
  shows "0 \<le> v a \<and>
    (case lower of None \<Rightarrow> True | Some l \<Rightarrow> v a \<le> max 0 (-l))"
proof -
  have relu: "v y = relu (v x)"
    using query_relu[OF model selected] by (simp add: satisfies_relu_def)
  have nonnegative: "0 \<le> v a"
    using auxiliary relu relu_aux_identity[of "v x"] relu_nonnegative[of "- v x"]
    by linarith
  have cap: "case lower of None \<Rightarrow> True | Some l \<Rightarrow> v a \<le> max 0 (-l)"
  proof (cases lower)
    case None
    then show ?thesis by simp
  next
    case (Some l)
    have input: "l \<le> v x"
      using lower model Some by (auto simp: satisfies_query_def)
    have equation: "v y - v x - v a = 0" using auxiliary by simp
    show ?thesis using relu_aux_upper_bound[OF input relu equation] Some by simp
  qed
  show ?thesis using nonnegative cap by blast
qed

lemma satisfies_introduce_relu_aux_iff:
  assumes "ReLU x y \<in> set (relu_atoms Q)" "relu_aux_lower_present Q x lower"
  shows "satisfies_query v (introduce_relu_aux Q x y a lower) \<longleftrightarrow>
    satisfies_query v Q \<and> v a = v y - v x"
  using relu_aux_added_bounds[OF assms]
  by (auto simp: satisfies_introduce_relu_aux_raw)

lemma models_introduce_relu_aux:
  assumes "ReLU x y \<in> set (relu_atoms Q)" "relu_aux_lower_present Q x lower"
  shows "models (introduce_relu_aux Q x y a lower) =
    {v \<in> models Q. v a = v y - v x}"
  using satisfies_introduce_relu_aux_iff[OF assms]
  by (auto simp: models_def)

theorem relu_aux_model_extension:
  assumes selected: "ReLU x y \<in> set (relu_atoms Q)"
      and lower: "relu_aux_lower_present Q x lower"
      and fresh: "a \<notin> query_vars Q"
  shows "satisfies_query (v(a := v y - v x)) (introduce_relu_aux Q x y a lower)
    \<longleftrightarrow> satisfies_query v Q"
proof -
  have distinct: "x \<noteq> a" "y \<noteq> a"
    using selected fresh by (auto simp: query_vars_def)
  show ?thesis
    by (simp add: satisfies_introduce_relu_aux_iff[OF selected lower]
        satisfies_query_fresh_update[OF fresh] distinct)
qed

theorem relu_aux_model_projection:
  assumes fresh: "a \<notin> query_vars Q"
      and model: "satisfies_query v (introduce_relu_aux Q x y a lower)"
  shows "satisfies_query (v(a := d)) Q"
  using model
  by (simp add: satisfies_introduce_relu_aux_raw satisfies_query_fresh_update[OF fresh])

theorem satisfiable_introduce_relu_aux_iff:
  assumes selected: "ReLU x y \<in> set (relu_atoms Q)"
      and lower: "relu_aux_lower_present Q x lower"
      and fresh: "a \<notin> query_vars Q"
  shows "satisfiable (introduce_relu_aux Q x y a lower) \<longleftrightarrow> satisfiable Q"
proof
  assume "satisfiable (introduce_relu_aux Q x y a lower)"
  then obtain v where "satisfies_query v (introduce_relu_aux Q x y a lower)"
    unfolding satisfiable_def by blast
  then have "satisfies_query v Q" by (simp add: satisfies_introduce_relu_aux_raw)
  then show "satisfiable Q" unfolding satisfiable_def by blast
next
  assume "satisfiable Q"
  then obtain v where "satisfies_query v Q" unfolding satisfiable_def by blast
  then have "satisfies_query (v(a := v y - v x)) (introduce_relu_aux Q x y a lower)"
    using relu_aux_model_extension[OF assms] by blast
  then show "satisfiable (introduce_relu_aux Q x y a lower)"
    unfolding satisfiable_def by blast
qed

corollary unsatisfiable_introduce_relu_aux_iff:
  assumes "ReLU x y \<in> set (relu_atoms Q)" "relu_aux_lower_present Q x lower"
      and "a \<notin> query_vars Q"
  shows "unsatisfiable (introduce_relu_aux Q x y a lower) \<longleftrightarrow> unsatisfiable Q"
  by (simp add: unsatisfiable_def satisfiable_introduce_relu_aux_iff[OF assms])

end
