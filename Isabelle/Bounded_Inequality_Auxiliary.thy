theory Bounded_Inequality_Auxiliary
  imports Inequality_Auxiliary_Sequence Exact_Query_Format
begin

text \<open>
  The native Engine::processInputQuery and the current capture/import pipeline
  require finite bounds. Preprocessor::makeAllEquationsEqualities supplies
  only one signed zero bound. Here an independently checked linear implication
  justifies the opposite bound after the fresh introduction.
  This is an exact local preparation step, not a native preprocessor trace.
\<close>

fun opposite_inequality_bound ::
  "rat_linear_constraint \<Rightarrow> var \<Rightarrow> rat \<Rightarrow> rat_bound option" where
  "opposite_inequality_bound (RatLe e b) s c = Some (RatUpper s c)"
| "opposite_inequality_bound (RatGe e b) s c = Some (RatLower s c)"
| "opposite_inequality_bound (RatEq e b) s c = None"

datatype bounded_inequality_step = Bounded_Inequality_Step nat var rat "rat list"

definition rat_introduce_bounded_inequality_aux ::
  "rat_query \<Rightarrow> bounded_inequality_step \<Rightarrow> rat_query option" where
  "rat_introduce_bounded_inequality_aux Q step =
    (case step of Bounded_Inequality_Step i s c ws \<Rightarrow>
      case rat_introduce_inequality_aux Q i s of
        None \<Rightarrow> None
      | Some P \<Rightarrow>
          (case opposite_inequality_bound (rat_linear_atoms Q ! i) s c of
             None \<Rightarrow> None
           | Some b \<Rightarrow>
               if check_linear_bound P b ws then Some (rat_add_bound P b) else None))"

lemma bounded_inequality_step_parts:
  assumes "rat_introduce_bounded_inequality_aux Q step = Some R"
  obtains i s P b ws where "rat_introduce_inequality_aux Q i s = Some P"
    "check_linear_bound P b ws" "R = rat_add_bound P b"
  using assms
  by (auto simp: rat_introduce_bounded_inequality_aux_def
      split: bounded_inequality_step.splits option.splits if_splits)

theorem bounded_inequality_step_model:
  assumes step: "rat_introduce_bounded_inequality_aux Q step = Some R"
      and model: "satisfies_query v (embed_query R)"
  shows "satisfies_query v (embed_query Q)"
proof -
  obtain i s P b ws where intro: "rat_introduce_inequality_aux Q i s = Some P"
      and checked: "check_linear_bound P b ws" and result: "R = rat_add_bound P b"
    by (rule bounded_inequality_step_parts[OF step])
  have "satisfies_query v (embed_query P)"
    using model by (simp add: result satisfies_rat_add_bound_iff)
  then show ?thesis by (rule rat_introduce_inequality_aux_model[OF intro])
qed

theorem bounded_inequality_step_satisfiable_iff:
  assumes step: "rat_introduce_bounded_inequality_aux Q step = Some R"
  shows "satisfiable (embed_query R) \<longleftrightarrow> satisfiable (embed_query Q)"
proof -
  obtain i s P b ws where intro: "rat_introduce_inequality_aux Q i s = Some P"
      and checked: "check_linear_bound P b ws" and result: "R = rat_add_bound P b"
    by (rule bounded_inequality_step_parts[OF step])
  have "models (embed_query R) = models (embed_query P)"
    unfolding result by (rule rat_linear_bound_preserves_models[OF checked])
  then show ?thesis
    using rat_introduce_inequality_aux_satisfiable_iff[OF intro]
    by (simp add: satisfiable_iff_models_nonempty)
qed

fun rat_introduce_bounded_inequality_sequence ::
  "rat_query \<Rightarrow> bounded_inequality_step list \<Rightarrow> rat_query option" where
  "rat_introduce_bounded_inequality_sequence Q [] = Some Q"
| "rat_introduce_bounded_inequality_sequence Q (step # steps) =
    (case rat_introduce_bounded_inequality_aux Q step of
       None \<Rightarrow> None
     | Some R \<Rightarrow> rat_introduce_bounded_inequality_sequence R steps)"

lemma bounded_inequality_sequence_append:
  "rat_introduce_bounded_inequality_sequence Q (first @ rest) =
    (case rat_introduce_bounded_inequality_sequence Q first of
       None \<Rightarrow> None
     | Some R \<Rightarrow> rat_introduce_bounded_inequality_sequence R rest)"
  by (induction first arbitrary: Q) (auto split: option.splits)

corollary bounded_inequality_sequence_failed_prefix:
  "rat_introduce_bounded_inequality_sequence Q first = None \<Longrightarrow>
    rat_introduce_bounded_inequality_sequence Q (first @ rest) = None"
  by (simp add: bounded_inequality_sequence_append)

theorem bounded_inequality_sequence_model:
  assumes "rat_introduce_bounded_inequality_sequence Q steps = Some R"
      and "satisfies_query v (embed_query R)"
  shows "satisfies_query v (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  then obtain P where head: "rat_introduce_bounded_inequality_aux Q step = Some P"
      and tail: "rat_introduce_bounded_inequality_sequence P steps = Some R"
    by (auto split: option.splits)
  show ?case by (rule bounded_inequality_step_model[OF head Cons.IH[OF tail Cons.prems(2)]])
qed

theorem bounded_inequality_sequence_satisfiable_iff:
  assumes "rat_introduce_bounded_inequality_sequence Q steps = Some R"
  shows "satisfiable (embed_query R) \<longleftrightarrow> satisfiable (embed_query Q)"
  using assms
proof (induction steps arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons step steps)
  then obtain P where head: "rat_introduce_bounded_inequality_aux Q step = Some P"
      and tail: "rat_introduce_bounded_inequality_sequence P steps = Some R"
    by (auto split: option.splits)
  show ?case using bounded_inequality_step_satisfiable_iff[OF head] Cons.IH[OF tail] by blast
qed

corollary bounded_inequality_sequence_unsatisfiable_iff:
  assumes "rat_introduce_bounded_inequality_sequence Q steps = Some R"
  shows "unsatisfiable (embed_query R) \<longleftrightarrow> unsatisfiable (embed_query Q)"
  by (simp add: unsatisfiable_def bounded_inequality_sequence_satisfiable_iff[OF assms])

definition bounded_decodes_like ::
  "bytes \<Rightarrow> bounded_inequality_step list \<Rightarrow> rat_query \<Rightarrow> bool" where
  "bounded_decodes_like bs steps R \<longleftrightarrow>
    (case decode_query bs of None \<Rightarrow> False | Some Q \<Rightarrow>
      (case rat_introduce_bounded_inequality_sequence Q steps of
         None \<Rightarrow> False | Some P \<Rightarrow> same_constraints P R))"

lemma bounded_decodes_like_decodes:
  "bounded_decodes_like bs steps R \<Longrightarrow> \<exists>Q. decode_query bs = Some Q"
  by (auto simp: bounded_decodes_like_def split: option.splits)

lemma bounded_decodes_like_unsatisfiable:
  assumes checked: "bounded_decodes_like bs steps R"
      and unsat: "unsatisfiable (embed_query R)"
      and decoded: "decode_query bs = Some Q"
  shows "unsatisfiable (embed_query Q)"
proof -
  obtain P where step: "rat_introduce_bounded_inequality_sequence Q steps = Some P"
      and matching: "same_constraints P R"
    using checked decoded by (auto simp: bounded_decodes_like_def split: option.splits)
  show ?thesis
    using same_constraints_unsatisfiable[OF matching] unsat
      bounded_inequality_sequence_unsatisfiable_iff[OF step] by blast
qed

lemma bounded_decodes_like_model:
  assumes checked: "bounded_decodes_like bs steps R"
      and model: "satisfies_query v (embed_query R)"
      and decoded: "decode_query bs = Some Q"
  shows "satisfies_query v (embed_query Q)"
proof -
  obtain P where step: "rat_introduce_bounded_inequality_sequence Q steps = Some P"
      and matching: "same_constraints P R"
    using checked decoded by (auto simp: bounded_decodes_like_def split: option.splits)
  have "satisfies_query v (embed_query P)" using same_constraints_models[OF matching] model by blast
  then show ?thesis by (rule bounded_inequality_sequence_model[OF step])
qed

export_code rat_introduce_bounded_inequality_aux rat_introduce_bounded_inequality_sequence
  bounded_decodes_like checking SML

end
