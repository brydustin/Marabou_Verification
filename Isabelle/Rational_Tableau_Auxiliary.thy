theory Rational_Tableau_Auxiliary
  imports Tableau_Auxiliary Rational_Proof_Trees
begin

text \<open>
  Executable, single-step interface. Its inputs are an original rational
  query, the position of an equality, and a proposed fresh variable. The
  transformed query is constructed here, not supplied by a certificate.
  Unsupported atom types, an invalid index, and any variable collision fail.
\<close>

fun rat_linexpr_vars :: "rat_linexpr \<Rightarrow> var set" where
  "rat_linexpr_vars (RatExpr c ts) = snd ` set ts"

fun rat_linear_vars :: "rat_linear_constraint \<Rightarrow> var set" where
  "rat_linear_vars (RatEq e b) = rat_linexpr_vars e"
| "rat_linear_vars (RatLe e b) = rat_linexpr_vars e"
| "rat_linear_vars (RatGe e b) = rat_linexpr_vars e"

fun rat_bound_vars :: "rat_bound \<Rightarrow> var set" where
  "rat_bound_vars (RatLower x l) = {x}"
| "rat_bound_vars (RatUpper x u) = {x}"

definition rat_query_vars :: "rat_query \<Rightarrow> var set" where
  "rat_query_vars Q =
    (\<Union>c \<in> set (rat_linear_atoms Q). rat_linear_vars c) \<union>
    (\<Union>b \<in> set (rat_query_bounds Q). rat_bound_vars b) \<union>
    (\<Union>r \<in> set (rat_relu_atoms Q). relu_vars r)"

lemma linexpr_vars_embed [simp]:
  "linexpr_vars (embed_linexpr e) = rat_linexpr_vars e"
  by (cases e) (simp add: image_image split_def)

lemma linear_vars_embed [simp]:
  "linear_vars (embed_linear c) = rat_linear_vars c"
  by (cases c) simp_all

lemma bound_vars_embed [simp]:
  "bound_vars (embed_bound b) = rat_bound_vars b"
  by (cases b) simp_all

lemma query_vars_embed [simp]:
  "query_vars (embed_query Q) = rat_query_vars Q"
  by (auto simp: query_vars_def rat_query_vars_def embed_query_def)

definition rat_fixed_aux_query ::
  "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> rat_linexpr \<Rightarrow> rat \<Rightarrow> rat_query" where
  "rat_fixed_aux_query Q i s e b = Q\<lparr>
    rat_linear_atoms := (rat_linear_atoms Q)[i := RatEq (rat_add e (RatExpr 0 [(-1, s)])) 0],
    rat_query_bounds := rat_query_bounds Q @ [RatLower s b, RatUpper s b]\<rparr>"

lemma embed_rat_fixed_aux_query:
  "embed_query (rat_fixed_aux_query Q i s e b) =
    introduce_fixed_aux (embed_query Q) i s (embed_linexpr e) (of_rat b)"
  by (cases e)
     (simp add: rat_fixed_aux_query_def introduce_fixed_aux_def embed_query_def map_update)

definition rat_introduce_fixed_aux ::
  "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> rat_query option" where
  "rat_introduce_fixed_aux Q i s =
    (if i < length (rat_linear_atoms Q) \<and> s \<notin> rat_query_vars Q then
       (case rat_linear_atoms Q ! i of
          RatEq e b \<Rightarrow> Some (rat_fixed_aux_query Q i s e b)
        | _ \<Rightarrow> None)
     else None)"

lemma rat_introduce_fixed_aux_Some_iff:
  "rat_introduce_fixed_aux Q i s = Some P \<longleftrightarrow>
    i < length (rat_linear_atoms Q) \<and> s \<notin> rat_query_vars Q \<and>
    (\<exists>e b. rat_linear_atoms Q ! i = RatEq e b \<and> P = rat_fixed_aux_query Q i s e b)"
  by (auto simp: rat_introduce_fixed_aux_def split: if_splits rat_linear_constraint.splits)

theorem rat_introduce_fixed_aux_satisfiable_iff:
  assumes "rat_introduce_fixed_aux Q i s = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
proof -
  obtain e b where index: "i < length (rat_linear_atoms Q)"
      and fresh: "s \<notin> rat_query_vars Q"
      and selected: "rat_linear_atoms Q ! i = RatEq e b"
      and result: "P = rat_fixed_aux_query Q i s e b"
    using assms by (auto simp: rat_introduce_fixed_aux_Some_iff)
  have real_index: "i < length (linear_atoms (embed_query Q))"
    using index by (simp add: embed_query_def)
  have real_selected: "linear_atoms (embed_query Q) ! i = LinearEq (embed_linexpr e) (of_rat b)"
    using index selected by (simp add: embed_query_def)
  have real_fresh: "s \<notin> query_vars (embed_query Q)" using fresh by simp
  show ?thesis
    unfolding result embed_rat_fixed_aux_query
    by (rule satisfiable_introduce_fixed_aux_iff[OF real_index real_selected real_fresh])
qed

corollary rat_introduce_fixed_aux_unsatisfiable_iff:
  assumes "rat_introduce_fixed_aux Q i s = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def rat_introduce_fixed_aux_satisfiable_iff[OF assms])

definition check_after_fixed_aux :: "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_fixed_aux Q i s cert =
    (case rat_introduce_fixed_aux Q i s of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_certificate P cert)"

theorem check_after_fixed_aux_sound:
  assumes "check_after_fixed_aux Q i s cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where step: "rat_introduce_fixed_aux Q i s = Some P"
      and checked: "check_certificate P cert"
    using assms by (auto simp: check_after_fixed_aux_def split: option.splits)
  have "unsatisfiable (embed_query P)" by (rule check_certificate_sound[OF checked])
  then show ?thesis using rat_introduce_fixed_aux_unsatisfiable_iff[OF step] by blast
qed

text \<open>
  Compilation checks the executable interface. Concrete acceptance theorems
  use proof-producing code_simp; no external execution is used as a premise.
\<close>

export_code rat_introduce_fixed_aux check_after_fixed_aux checking SML

end
