theory Tableau_Auxiliary_Sequence
  imports Rational_Tableau_Auxiliary
begin

text \<open>
  A finite list of (equation index, proposed fresh variable) pairs.
  Each introduction checks the query produced by its predecessor. A failed
  step fails the whole sequence; no intermediate query or scalar is trusted.
  This composes the mathematical step corresponding to
  src/engine/Engine.cpp::addAuxiliaryVariables, without verifying its C++ loop.
\<close>

type_synonym fixed_aux_step = "nat \<times> var"

fun rat_introduce_fixed_aux_sequence ::
  "rat_query \<Rightarrow> fixed_aux_step list \<Rightarrow> rat_query option" where
  "rat_introduce_fixed_aux_sequence Q [] = Some Q"
| "rat_introduce_fixed_aux_sequence Q ((i, s) # steps) =
    (case rat_introduce_fixed_aux Q i s of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_fixed_aux_sequence P steps)"

lemma fixed_aux_sequence_singleton:
  "rat_introduce_fixed_aux_sequence Q [(i, s)] = rat_introduce_fixed_aux Q i s"
  by (simp split: option.splits)

lemma fixed_aux_sequence_append:
  "rat_introduce_fixed_aux_sequence Q (first @ rest) =
    (case rat_introduce_fixed_aux_sequence Q first of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_fixed_aux_sequence P rest)"
  by (induction first arbitrary: Q) (auto split: prod.splits option.splits)

corollary fixed_aux_sequence_failed_prefix:
  "rat_introduce_fixed_aux_sequence Q first = None \<Longrightarrow>
    rat_introduce_fixed_aux_sequence Q (first @ rest) = None"
  by (simp add: fixed_aux_sequence_append)

theorem fixed_aux_sequence_satisfiable_iff:
  assumes "rat_introduce_fixed_aux_sequence Q steps = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  obtain i s where pair: "step = (i, s)" by (cases step) simp
  obtain R where head: "rat_introduce_fixed_aux Q i s = Some R"
      and tail: "rat_introduce_fixed_aux_sequence R steps = Some P"
    using Cons.prems by (auto simp: pair split: option.splits)
  have head_equiv: "satisfiable (embed_query R) \<longleftrightarrow> satisfiable (embed_query Q)"
    by (rule rat_introduce_fixed_aux_satisfiable_iff[OF head])
  have tail_equiv: "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query R)"
    by (rule Cons.IH[OF tail])
  show ?case using head_equiv tail_equiv by blast
qed

corollary fixed_aux_sequence_unsatisfiable_iff:
  assumes "rat_introduce_fixed_aux_sequence Q steps = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def fixed_aux_sequence_satisfiable_iff[OF assms])

definition check_after_fixed_aux_sequence ::
  "rat_query \<Rightarrow> fixed_aux_step list \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_fixed_aux_sequence Q steps cert =
    (case rat_introduce_fixed_aux_sequence Q steps of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_certificate P cert)"

lemma check_after_fixed_aux_sequence_empty [simp]:
  "check_after_fixed_aux_sequence Q [] cert = check_certificate Q cert"
  by (simp add: check_after_fixed_aux_sequence_def)

lemma check_after_fixed_aux_sequence_singleton:
  "check_after_fixed_aux_sequence Q [(i, s)] cert = check_after_fixed_aux Q i s cert"
  by (simp add: check_after_fixed_aux_sequence_def check_after_fixed_aux_def
      fixed_aux_sequence_singleton split: option.splits)

theorem check_after_fixed_aux_sequence_sound:
  assumes "check_after_fixed_aux_sequence Q steps cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where steps: "rat_introduce_fixed_aux_sequence Q steps = Some P"
      and checked: "check_certificate P cert"
    using assms by (auto simp: check_after_fixed_aux_sequence_def split: option.splits)
  have "unsatisfiable (embed_query P)" by (rule check_certificate_sound[OF checked])
  then show ?thesis using fixed_aux_sequence_unsatisfiable_iff[OF steps] by blast
qed

corollary check_after_fixed_aux_sequence_rejects_model:
  assumes "satisfies_query v (embed_query Q)"
  shows "\<not> check_after_fixed_aux_sequence Q steps cert"
  using assms check_after_fixed_aux_sequence_sound
  unfolding unsatisfiable_def satisfiable_def by blast

export_code rat_introduce_fixed_aux_sequence check_after_fixed_aux_sequence checking SML

end
