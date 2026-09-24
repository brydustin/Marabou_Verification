theory Rational_ReLU_Auxiliary
  imports ReLU_Auxiliary Tableau_Auxiliary_Sequence
begin

text \<open>
  Checked rational ReLU auxiliary introduction. ReLU membership, global
  freshness, and any selected finite input lower bound are checked here.
  The equation and auxiliary bounds are constructed, not trusted evidence.
  None requests no finite upper bound; Some l requires an explicit Lower x l.
\<close>

fun rat_relu_aux_bounds :: "var \<Rightarrow> rat option \<Rightarrow> rat_bound list" where
  "rat_relu_aux_bounds a None = [RatLower a 0]"
| "rat_relu_aux_bounds a (Some l) = [RatLower a 0, RatUpper a (max 0 (-l))]"

fun rat_relu_aux_lower_present :: "rat_query \<Rightarrow> var \<Rightarrow> rat option \<Rightarrow> bool" where
  "rat_relu_aux_lower_present Q x None = True"
| "rat_relu_aux_lower_present Q x (Some l) = (RatLower x l \<in> set (rat_query_bounds Q))"

definition rat_relu_aux_query ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat option \<Rightarrow> rat_query" where
  "rat_relu_aux_query Q x y a lower = Q\<lparr>
    rat_linear_atoms := rat_linear_atoms Q @ [RatEq (relu_aux_expr x y a) 0],
    rat_query_bounds := rat_query_bounds Q @ rat_relu_aux_bounds a lower\<rparr>"

lemma embed_rat_relu_aux_bounds:
  "map embed_bound (rat_relu_aux_bounds a lower) =
    relu_aux_bounds a (map_option of_rat lower)"
  by (cases lower) (simp_all add: max_def of_rat_minus)

lemma embed_rat_relu_aux_query:
  "embed_query (rat_relu_aux_query Q x y a lower) =
    introduce_relu_aux (embed_query Q) x y a (map_option of_rat lower)"
  by (simp add: rat_relu_aux_query_def introduce_relu_aux_def embed_query_def
      relu_aux_expr_def embed_rat_relu_aux_bounds)

definition rat_introduce_relu_aux ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat option \<Rightarrow> rat_query option" where
  "rat_introduce_relu_aux Q x y a lower =
    (if ReLU x y \<in> set (rat_relu_atoms Q) \<and> a \<notin> rat_query_vars Q \<and>
        rat_relu_aux_lower_present Q x lower
     then Some (rat_relu_aux_query Q x y a lower) else None)"

lemma rat_introduce_relu_aux_Some_iff:
  "rat_introduce_relu_aux Q x y a lower = Some P \<longleftrightarrow>
    ReLU x y \<in> set (rat_relu_atoms Q) \<and> a \<notin> rat_query_vars Q \<and>
    rat_relu_aux_lower_present Q x lower \<and> P = rat_relu_aux_query Q x y a lower"
  by (auto simp: rat_introduce_relu_aux_def)

lemma rat_introduce_relu_aux_real:
  assumes "rat_introduce_relu_aux Q x y a lower = Some P"
  shows "embed_query P = introduce_relu_aux (embed_query Q) x y a (map_option of_rat lower)"
    and "ReLU x y \<in> set (relu_atoms (embed_query Q))"
    and "relu_aux_lower_present (embed_query Q) x (map_option of_rat lower)"
    and "a \<notin> query_vars (embed_query Q)"
proof -
  have result: "P = rat_relu_aux_query Q x y a lower"
      and selected: "ReLU x y \<in> set (rat_relu_atoms Q)"
      and lower: "rat_relu_aux_lower_present Q x lower"
      and fresh: "a \<notin> rat_query_vars Q"
    using assms by (auto simp: rat_introduce_relu_aux_Some_iff)
  show "embed_query P = introduce_relu_aux (embed_query Q) x y a (map_option of_rat lower)"
    by (simp only: result embed_rat_relu_aux_query)
  show "ReLU x y \<in> set (relu_atoms (embed_query Q))"
    using selected by (simp add: embed_query_def)
  show "relu_aux_lower_present (embed_query Q) x (map_option of_rat lower)"
  proof (cases lower)
    case None
    then show ?thesis by simp
  next
    case (Some l)
    have member: "RatLower x l \<in> set (rat_query_bounds Q)"
      using lower Some by simp
    have "embed_bound (RatLower x l) \<in> embed_bound ` set (rat_query_bounds Q)"
      by (rule imageI[OF member])
    then show ?thesis by (simp add: Some embed_query_def)
  qed
  show "a \<notin> query_vars (embed_query Q)" using fresh by simp
qed

theorem rat_relu_aux_model_extension:
  assumes "rat_introduce_relu_aux Q x y a lower = Some P"
  shows "satisfies_query (v(a := v y - v x)) (embed_query P) \<longleftrightarrow>
    satisfies_query v (embed_query Q)"
proof -
  note real = rat_introduce_relu_aux_real[OF assms]
  show ?thesis
    unfolding real(1) by (rule relu_aux_model_extension[OF real(2,3,4)])
qed

theorem rat_relu_aux_model_projection:
  assumes step: "rat_introduce_relu_aux Q x y a lower = Some P"
      and model: "satisfies_query v (embed_query P)"
  shows "satisfies_query (v(a := d)) (embed_query Q)"
proof -
  note real = rat_introduce_relu_aux_real[OF step]
  show ?thesis
    by (rule relu_aux_model_projection[OF real(4)])
       (use model in \<open>simp only: real(1)\<close>)
qed

theorem rat_introduce_relu_aux_satisfiable_iff:
  assumes "rat_introduce_relu_aux Q x y a lower = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
proof -
  note real = rat_introduce_relu_aux_real[OF assms]
  show ?thesis
    unfolding real(1) by (rule satisfiable_introduce_relu_aux_iff[OF real(2,3,4)])
qed

corollary rat_introduce_relu_aux_unsatisfiable_iff:
  assumes "rat_introduce_relu_aux Q x y a lower = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def rat_introduce_relu_aux_satisfiable_iff[OF assms])

text \<open>
  Compose one ReLU introduction with the existing checked scalar-fixed
  tableau sequence and terminal proof tree. An empty sequence directly checks
  the query with its new ReLU auxiliary. No certificate constructor changes.
\<close>

definition check_after_relu_aux ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat option
    \<Rightarrow> fixed_aux_step list \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_relu_aux Q x y a lower steps cert =
    (case rat_introduce_relu_aux Q x y a lower of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_after_fixed_aux_sequence P steps cert)"

theorem check_after_relu_aux_sound:
  assumes "check_after_relu_aux Q x y a lower steps cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where step: "rat_introduce_relu_aux Q x y a lower = Some P"
      and checked: "check_after_fixed_aux_sequence P steps cert"
    using assms by (auto simp: check_after_relu_aux_def split: option.splits)
  have "unsatisfiable (embed_query P)"
    by (rule check_after_fixed_aux_sequence_sound[OF checked])
  then show ?thesis using rat_introduce_relu_aux_unsatisfiable_iff[OF step] by blast
qed

corollary check_after_relu_aux_rejects_model:
  assumes "satisfies_query v (embed_query Q)"
  shows "\<not> check_after_relu_aux Q x y a lower steps cert"
  using assms check_after_relu_aux_sound
  unfolding unsatisfiable_def satisfiable_def by blast

export_code rat_introduce_relu_aux check_after_relu_aux checking SML

end
