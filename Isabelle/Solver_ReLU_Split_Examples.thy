theory Solver_ReLU_Split_Examples
  imports Imported_Marabou_Solver_Relu_Split
begin

text \<open>
  These are the two children of the captured solver certificate, selected
  without repeating their numeric data. HOL stores active then inactive;
  the native JSON writer emits inactive then active. The importer identifies
  the phases by their bounds. See notes/SOLVER_RELU_SPLIT_CAPTURE.md.
\<close>

definition captured_active_child :: certificate where
  "captured_active_child =
    (case imported_certificate of
       Relu_Split x y active inactive \<Rightarrow> active
     | _ \<Rightarrow> Linear_Unsat [])"

definition captured_inactive_child :: certificate where
  "captured_inactive_child =
    (case imported_certificate of
       Relu_Split x y active inactive \<Rightarrow> inactive
     | _ \<Rightarrow> Linear_Unsat [])"

lemma captured_split_shape:
  "imported_certificate =
    Relu_Split 0 1 captured_active_child captured_inactive_child"
  by (simp add: imported_certificate_def
      captured_active_child_def captured_inactive_child_def)

lemma captured_active_child_checked:
  "check_certificate (rat_active_split imported_query 0 1) captured_active_child"
  by code_simp

lemma captured_inactive_child_checked:
  "check_certificate (rat_inactive_split imported_query 0 1) captured_inactive_child"
  by code_simp

theorem captured_active_child_unsatisfiable:
  "unsatisfiable (embed_query (rat_active_split imported_query 0 1))"
  by (rule check_certificate_sound[OF captured_active_child_checked])

theorem captured_inactive_child_unsatisfiable:
  "unsatisfiable (embed_query (rat_inactive_split imported_query 0 1))"
  by (rule check_certificate_sound[OF captured_inactive_child_checked])

text \<open>
  The root's linear relaxation has a real model:
  b=0, f=a=1/2, t=u=0, p=q=r=s=1/4, h0=h1=h2=h3=1/4, h4=0.
  Thus an exact linear leaf cannot close the unsplit root.
\<close>

definition split_linear_relaxation :: rat_query where
  "split_linear_relaxation = imported_query\<lparr>rat_relu_atoms := []\<rparr>"

definition split_relaxation_witness :: valuation where
  "split_relaxation_witness x =
    (if x = 1 \<or> x = 2 then 1/2
     else if 5 \<le> x \<and> x \<le> 12 then 1/4 else 0)"

lemma split_linear_relaxation_has_model:
  "satisfies_query split_relaxation_witness (embed_query split_linear_relaxation)"
  by (simp add: split_linear_relaxation_def split_relaxation_witness_def
      imported_query_def embed_query_def satisfies_query_def
      of_rat_divide of_rat_minus)

theorem split_linear_relaxation_satisfiable:
  "satisfiable (embed_query split_linear_relaxation)"
  using split_linear_relaxation_has_model
  unfolding satisfiable_def by blast

theorem captured_split_requires_nonlinear_evidence:
  "\<not> check_linear_leaf imported_query ws"
proof -
  have "\<not> check_linear_leaf split_linear_relaxation ws"
    by (rule check_linear_leaf_rejects_model[OF split_linear_relaxation_has_model])
  then show ?thesis
    by (simp add: split_linear_relaxation_def check_linear_leaf_def normalize_query_def)
qed

end
