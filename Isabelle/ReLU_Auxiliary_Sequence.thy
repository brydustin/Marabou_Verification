theory ReLU_Auxiliary_Sequence
  imports Rational_ReLU_Auxiliary
begin

text \<open>
  Finite checked ReLU auxiliary introductions. Each step checks ReLU
  membership, freshness and its optional finite lower premise in the current
  query. It constructs the auxiliary equation and bounds itself.
  This composes the mathematical operation corresponding to
  src/engine/ReluConstraint.cpp::transformToUseAuxVariables; it does not
  verify the native transformation loop or its bound caches.
\<close>

datatype relu_aux_step = ReLU_Aux_Step var var var "rat option"

fun rat_introduce_relu_aux_sequence ::
  "rat_query \<Rightarrow> relu_aux_step list \<Rightarrow> rat_query option" where
  "rat_introduce_relu_aux_sequence Q [] = Some Q"
| "rat_introduce_relu_aux_sequence Q (ReLU_Aux_Step x y a lower # steps) =
    (case rat_introduce_relu_aux Q x y a lower of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_relu_aux_sequence P steps)"

lemma relu_aux_sequence_singleton:
  "rat_introduce_relu_aux_sequence Q [ReLU_Aux_Step x y a lower] =
    rat_introduce_relu_aux Q x y a lower"
  by (simp split: option.splits)

lemma relu_aux_sequence_append:
  "rat_introduce_relu_aux_sequence Q (first @ rest) =
    (case rat_introduce_relu_aux_sequence Q first of
       None \<Rightarrow> None
     | Some P \<Rightarrow> rat_introduce_relu_aux_sequence P rest)"
proof (induction first arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step first)
  then show ?case by (cases step) (auto split: option.splits)
qed

corollary relu_aux_sequence_failed_prefix:
  "rat_introduce_relu_aux_sequence Q first = None \<Longrightarrow>
    rat_introduce_relu_aux_sequence Q (first @ rest) = None"
  by (simp add: relu_aux_sequence_append)

theorem relu_aux_sequence_satisfiable_iff:
  assumes "rat_introduce_relu_aux_sequence Q steps = Some P"
  shows "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  obtain x y a lower where head_form: "step = ReLU_Aux_Step x y a lower"
    by (cases step) simp
  obtain R where head: "rat_introduce_relu_aux Q x y a lower = Some R"
      and tail: "rat_introduce_relu_aux_sequence R steps = Some P"
    using Cons.prems by (auto simp: head_form split: option.splits)
  have head_equiv: "satisfiable (embed_query R) \<longleftrightarrow> satisfiable (embed_query Q)"
    by (rule rat_introduce_relu_aux_satisfiable_iff[OF head])
  have tail_equiv: "satisfiable (embed_query P) \<longleftrightarrow> satisfiable (embed_query R)"
    by (rule Cons.IH[OF tail])
  show ?case using head_equiv tail_equiv by blast
qed

corollary relu_aux_sequence_unsatisfiable_iff:
  assumes "rat_introduce_relu_aux_sequence Q steps = Some P"
  shows "unsatisfiable (embed_query P) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def relu_aux_sequence_satisfiable_iff[OF assms])

definition check_after_relu_aux_sequence ::
  "rat_query \<Rightarrow> relu_aux_step list \<Rightarrow> fixed_aux_step list
    \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_after_relu_aux_sequence Q relu_steps tableau_steps cert =
    (case rat_introduce_relu_aux_sequence Q relu_steps of
       None \<Rightarrow> False
     | Some P \<Rightarrow> check_after_fixed_aux_sequence P tableau_steps cert)"

lemma check_after_relu_aux_sequence_empty [simp]:
  "check_after_relu_aux_sequence Q [] tableau_steps cert =
    check_after_fixed_aux_sequence Q tableau_steps cert"
  by (simp add: check_after_relu_aux_sequence_def)

lemma check_after_relu_aux_sequence_singleton:
  "check_after_relu_aux_sequence Q [ReLU_Aux_Step x y a lower] tableau_steps cert =
    check_after_relu_aux Q x y a lower tableau_steps cert"
  by (simp add: check_after_relu_aux_sequence_def check_after_relu_aux_def
      relu_aux_sequence_singleton split: option.splits)

theorem check_after_relu_aux_sequence_sound:
  assumes "check_after_relu_aux_sequence Q relu_steps tableau_steps cert"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where steps: "rat_introduce_relu_aux_sequence Q relu_steps = Some P"
      and checked: "check_after_fixed_aux_sequence P tableau_steps cert"
    using assms by (auto simp: check_after_relu_aux_sequence_def split: option.splits)
  have "unsatisfiable (embed_query P)"
    by (rule check_after_fixed_aux_sequence_sound[OF checked])
  then show ?thesis using relu_aux_sequence_unsatisfiable_iff[OF steps] by blast
qed

corollary check_after_relu_aux_sequence_rejects_model:
  assumes "satisfies_query v (embed_query Q)"
  shows "\<not> check_after_relu_aux_sequence Q relu_steps tableau_steps cert"
  using assms check_after_relu_aux_sequence_sound
  unfolding unsatisfiable_def satisfiable_def by blast

export_code rat_introduce_relu_aux_sequence check_after_relu_aux_sequence checking SML

end
