theory Inequality_Auxiliary_Sequence
  imports Rational_Inequality_Auxiliary Rational_Assignment
begin

text \<open>
  Finite checked replacements compose before the existing ReLU and tableau
  introductions. Failed steps are never skipped. This models the inequality
  conversion part of Preprocessor::makeAllEquationsEqualities, not the whole
  native preprocessing pass. No opposite finite slack bound is assumed.
\<close>

type_synonym inequality_aux_step = "nat \<times> var"

fun rat_introduce_inequality_aux_sequence ::
  "rat_query \<Rightarrow> inequality_aux_step list \<Rightarrow> rat_query option" where
  "rat_introduce_inequality_aux_sequence Q [] = Some Q"
| "rat_introduce_inequality_aux_sequence Q ((i, s) # steps) =
    (case rat_introduce_inequality_aux Q i s of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_inequality_aux_sequence P steps)"

lemma inequality_aux_sequence_singleton:
  "rat_introduce_inequality_aux_sequence Q [(i, s)] = rat_introduce_inequality_aux Q i s"
  by (simp split: option.splits)

lemma inequality_aux_sequence_append:
  "rat_introduce_inequality_aux_sequence Q (first @ rest) =
    (case rat_introduce_inequality_aux_sequence Q first of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_inequality_aux_sequence P rest)"
  by (induction first arbitrary: Q) (auto split: prod.splits option.splits)

corollary inequality_aux_sequence_failed_prefix:
  "rat_introduce_inequality_aux_sequence Q first = None \<Longrightarrow>
    rat_introduce_inequality_aux_sequence Q (first @ rest) = None"
  by (simp add: inequality_aux_sequence_append)

theorem inequality_aux_sequence_model:
  assumes "rat_introduce_inequality_aux_sequence Q steps = Some P"
      and "satisfies_query v (embed_query P)"
  shows "satisfies_query v (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  obtain i s where pair: "step = (i, s)" by (cases step) simp
  obtain R where head: "rat_introduce_inequality_aux Q i s = Some R"
      and tail: "rat_introduce_inequality_aux_sequence R steps = Some P"
    using Cons.prems(1) by (auto simp: pair split: option.splits)
  have "satisfies_query v (embed_query R)" by (rule Cons.IH[OF tail Cons.prems(2)])
  then show ?case by (rule rat_introduce_inequality_aux_model[OF head])
qed

theorem inequality_aux_sequence_satisfiable_iff:
  assumes "rat_introduce_inequality_aux_sequence Q steps = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  obtain i s where pair: "step = (i, s)" by (cases step) simp
  obtain R where head: "rat_introduce_inequality_aux Q i s = Some R"
      and tail: "rat_introduce_inequality_aux_sequence R steps = Some P"
    using Cons.prems by (auto simp: pair split: option.splits)
  show ?case
    using Cons.IH[OF tail] rat_introduce_inequality_aux_satisfiable_iff[OF head] by blast
qed

corollary inequality_aux_sequence_unsatisfiable_iff:
  assumes "rat_introduce_inequality_aux_sequence Q steps = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def inequality_aux_sequence_satisfiable_iff[OF assms])

definition check_after_inequality_aux_sequence ::
  "rat_query \<Rightarrow> inequality_aux_step list \<Rightarrow> relu_aux_step list
    \<Rightarrow> fixed_aux_step list \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_inequality_aux_sequence Q steps relu_steps tableau_steps cert =
    (case rat_introduce_inequality_aux_sequence Q steps of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_after_relu_aux_sequence P relu_steps tableau_steps cert)"

lemma check_after_inequality_aux_sequence_empty [simp]:
  "check_after_inequality_aux_sequence Q [] relu_steps tableau_steps cert =
    check_after_relu_aux_sequence Q relu_steps tableau_steps cert"
  by (simp add: check_after_inequality_aux_sequence_def)

lemma check_after_inequality_aux_sequence_singleton:
  "check_after_inequality_aux_sequence Q [(i, s)] [] [] cert =
    check_after_inequality_aux Q i s cert"
  by (simp add: check_after_inequality_aux_sequence_def inequality_aux_sequence_singleton
      check_after_inequality_aux_def split: option.splits)

theorem check_after_inequality_aux_sequence_sound:
  assumes "check_after_inequality_aux_sequence Q steps relu_steps tableau_steps cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where steps: "rat_introduce_inequality_aux_sequence Q steps = Some P"
      and checked: "check_after_relu_aux_sequence P relu_steps tableau_steps cert"
    using assms by (auto simp: check_after_inequality_aux_sequence_def split: option.splits)
  have "unsatisfiable (embed_query P)" by (rule check_after_relu_aux_sequence_sound[OF checked])
  then show ?thesis using inequality_aux_sequence_unsatisfiable_iff[OF steps] by blast
qed

corollary check_after_inequality_aux_sequence_rejects_model:
  assumes "satisfies_query v (embed_query Q)"
  shows "\<not> check_after_inequality_aux_sequence Q steps relu_steps tableau_steps cert"
  using assms check_after_inequality_aux_sequence_sound
  unfolding unsatisfiable_def satisfiable_def by blast

definition check_assignment_after_inequality_aux_sequence ::
  "rat_query \<Rightarrow> inequality_aux_step list \<Rightarrow> rat_assignment \<Rightarrow> bool" where
  "check_assignment_after_inequality_aux_sequence Q steps \<sigma> =
    (case rat_introduce_inequality_aux_sequence Q steps of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_rat_assignment P \<sigma>)"

theorem check_assignment_after_inequality_aux_sequence_sound:
  assumes "check_assignment_after_inequality_aux_sequence Q steps \<sigma>"
  shows "satisfies_query (assignment_valuation \<sigma>) (embed_query Q)"
proof -
  obtain P where steps: "rat_introduce_inequality_aux_sequence Q steps = Some P"
      and checked: "check_rat_assignment P \<sigma>"
    using assms
    by (auto simp: check_assignment_after_inequality_aux_sequence_def split: option.splits)
  show ?thesis
    by (rule inequality_aux_sequence_model[OF steps check_rat_assignment_sound[OF checked]])
qed

corollary check_assignment_after_inequality_aux_sequence_satisfiable:
  "check_assignment_after_inequality_aux_sequence Q steps \<sigma> \<Longrightarrow> satisfiable (embed_query Q)"
  using check_assignment_after_inequality_aux_sequence_sound unfolding satisfiable_def by blast

theorem inequality_relu_fixed_assignment_satisfiable:
  assumes "rat_introduce_inequality_aux_sequence Q steps = Some R"
      and "rat_introduce_relu_aux_sequence R relu_steps = Some S"
      and "rat_introduce_fixed_aux_sequence S tableau_steps = Some P"
      and "check_rat_assignment P \<sigma>"
  shows "satisfiable (embed_query Q)"
  using inequality_aux_sequence_satisfiable_iff[OF assms(1)]
    relu_aux_sequence_assignment_satisfiable[OF assms(2,3,4)] by blast

export_code rat_introduce_inequality_aux_sequence check_after_inequality_aux_sequence
  check_assignment_after_inequality_aux_sequence checking SML
export_code rat_introduce_inequality_aux rat_introduce_inequality_aux_sequence
  check_after_inequality_aux_sequence check_assignment_after_inequality_aux_sequence
  RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU ReLU_Aux_Step Linear_Unsat
  rat_query.make Fract int_of_integer nat_of_integer
  in SML module_name Marabou_Inequality_Preprocessor file_prefix Marabou_Inequality_Preprocessor

end
