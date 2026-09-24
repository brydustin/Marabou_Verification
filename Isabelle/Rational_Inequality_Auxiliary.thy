theory Rational_Inequality_Auxiliary
  imports Inequality_Auxiliary Rational_Tableau_Auxiliary
begin

text \<open>
  An executable proposal consists only of an atom index and a fresh name.
  Its direction, expression, scalar and signed bound are read or constructed
  here. A certificate cannot substitute a different inequality or slack sign.
\<close>

fun rat_inequality_atom ::
  "inequality_direction \<Rightarrow> rat_linexpr \<Rightarrow> rat \<Rightarrow> rat_linear_constraint" where
  "rat_inequality_atom Slack_Le e b = RatLe e b"
| "rat_inequality_atom Slack_Ge e b = RatGe e b"

fun rat_inequality_aux_bound :: "inequality_direction \<Rightarrow> var \<Rightarrow> rat_bound" where
  "rat_inequality_aux_bound Slack_Le s = RatLower s 0"
| "rat_inequality_aux_bound Slack_Ge s = RatUpper s 0"

lemma embed_rat_inequality_atom [simp]:
  "embed_linear (rat_inequality_atom dir e b) = inequality_atom dir (embed_linexpr e) (of_rat b)"
  by (cases dir) simp_all

lemma embed_rat_inequality_aux_bound [simp]:
  "embed_bound (rat_inequality_aux_bound dir s) = inequality_aux_bound dir s"
  by (cases dir) simp_all

definition rat_inequality_aux_query ::
  "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> inequality_direction
    \<Rightarrow> rat_linexpr \<Rightarrow> rat \<Rightarrow> rat_query" where
  "rat_inequality_aux_query Q i s dir e b = Q\<lparr>
    rat_linear_atoms := (rat_linear_atoms Q)[i := RatEq (rat_add e (RatExpr 0 [(1, s)])) b],
    rat_query_bounds := rat_query_bounds Q @ [rat_inequality_aux_bound dir s]\<rparr>"

lemma embed_rat_inequality_aux_query:
  "embed_query (rat_inequality_aux_query Q i s dir e b) =
    introduce_inequality_aux (embed_query Q) i s dir (embed_linexpr e) (of_rat b)"
  by (cases e)
     (simp add: rat_inequality_aux_query_def introduce_inequality_aux_def embed_query_def map_update)

definition rat_introduce_inequality_aux ::
  "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> rat_query option" where
  "rat_introduce_inequality_aux Q i s =
    (if i < length (rat_linear_atoms Q) \<and> s \<notin> rat_query_vars Q then
       (case rat_linear_atoms Q ! i of
          RatLe e b \<Rightarrow> Some (rat_inequality_aux_query Q i s Slack_Le e b)
        | RatGe e b \<Rightarrow> Some (rat_inequality_aux_query Q i s Slack_Ge e b)
        | _ \<Rightarrow> None)
     else None)"

lemma rat_introduce_inequality_aux_Some_iff:
  "rat_introduce_inequality_aux Q i s = Some P \<longleftrightarrow>
    i < length (rat_linear_atoms Q) \<and> s \<notin> rat_query_vars Q \<and>
    (\<exists>dir e b. rat_linear_atoms Q ! i = rat_inequality_atom dir e b \<and>
      P = rat_inequality_aux_query Q i s dir e b)"
proof -
  have directions: "\<And>P. (\<exists>dir. P dir) \<longleftrightarrow> P Slack_Le \<or> P Slack_Ge"
    by (metis inequality_direction.exhaust)
  show ?thesis
    by (auto simp: directions rat_introduce_inequality_aux_def
        split: if_splits rat_linear_constraint.splits)
qed

lemma rat_inequality_aux_selection:
  assumes "i < length (rat_linear_atoms Q)"
      and "rat_linear_atoms Q ! i = rat_inequality_atom dir e b"
  shows "i < length (linear_atoms (embed_query Q))"
      and "linear_atoms (embed_query Q) ! i = inequality_atom dir (embed_linexpr e) (of_rat b)"
  using assms by (simp_all add: embed_query_def)

theorem rat_introduce_inequality_aux_model:
  assumes step: "rat_introduce_inequality_aux Q i s = Some P"
      and model: "satisfies_query v (embed_query P)"
  shows "satisfies_query v (embed_query Q)"
proof -
  obtain dir e b where index: "i < length (rat_linear_atoms Q)"
      and selected: "rat_linear_atoms Q ! i = rat_inequality_atom dir e b"
      and result: "P = rat_inequality_aux_query Q i s dir e b"
    using step by (auto simp: rat_introduce_inequality_aux_Some_iff)
  have "satisfies_query v (embed_query P) \<longleftrightarrow>
      satisfies_query v (embed_query Q) \<and> v s = of_rat b - eval_rat_expr v e"
    unfolding result embed_rat_inequality_aux_query
    by (rule satisfies_introduce_inequality_aux_iff[OF rat_inequality_aux_selection[OF index selected]])
  then show ?thesis using model by blast
qed

theorem rat_introduce_inequality_aux_satisfiable_iff:
  assumes "rat_introduce_inequality_aux Q i s = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
proof -
  obtain dir e b where index: "i < length (rat_linear_atoms Q)"
      and fresh: "s \<notin> rat_query_vars Q"
      and selected: "rat_linear_atoms Q ! i = rat_inequality_atom dir e b"
      and result: "P = rat_inequality_aux_query Q i s dir e b"
    using assms by (auto simp: rat_introduce_inequality_aux_Some_iff)
  have real_fresh: "s \<notin> query_vars (embed_query Q)" using fresh by simp
  show ?thesis
    unfolding result embed_rat_inequality_aux_query
    by (rule satisfiable_introduce_inequality_aux_iff[
          OF rat_inequality_aux_selection[OF index selected] real_fresh])
qed

corollary rat_introduce_inequality_aux_unsatisfiable_iff:
  assumes "rat_introduce_inequality_aux Q i s = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def rat_introduce_inequality_aux_satisfiable_iff[OF assms])

definition check_after_inequality_aux ::
  "rat_query \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_inequality_aux Q i s cert =
    (case rat_introduce_inequality_aux Q i s of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_certificate P cert)"

theorem check_after_inequality_aux_sound:
  assumes "check_after_inequality_aux Q i s cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where step: "rat_introduce_inequality_aux Q i s = Some P"
      and checked: "check_certificate P cert"
    using assms by (auto simp: check_after_inequality_aux_def split: option.splits)
  have "unsatisfiable (embed_query P)" by (rule check_certificate_sound[OF checked])
  then show ?thesis using rat_introduce_inequality_aux_unsatisfiable_iff[OF step] by blast
qed

export_code rat_introduce_inequality_aux check_after_inequality_aux checking SML

end
