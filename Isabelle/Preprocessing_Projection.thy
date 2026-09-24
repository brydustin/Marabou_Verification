theory Preprocessing_Projection
  imports Rational_Proof_Trees
begin

text \<open>
  Checking the result of Marabou's Preprocessor::preprocess (Preprocessor.cpp
  61-180). After the slack and ReLU auxiliary introductions, which are
  checked separately, the native pass tightens bounds with equations and
  ReLU entailments (processEquations, processConstraints). It merges
  variables related by x1 - x2 = 0 (processIdenticalVariables), fixes and
  eliminates variables, removes redundant equations and obsolete ReLUs, and
  renumbers the rest (eliminateVariables).

  None of this is trusted. A projection certificate first adds checked
  facts, each of which keeps every real model of the query Q. It names, for
  every variable u of the proposed preprocessed query P, a variable proj u of
  Q. It then proves, for every normalized row of P renamed through proj, an
  exact linear implication from the enriched query. Each ReLU of P, renamed,
  must be a ReLU of Q up to proved equalities of its input and output.
  Then every real model v of Q gives the model v o proj of P, so UNSAT of P
  proves UNSAT of Q. Nothing in P needs to match the native computation;
  bounds rounded or snapped by native tolerances simply fail to be implied.
\<close>

section \<open>Checked facts\<close>

definition relu_active_facts :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_query" where
  "relu_active_facts Q x y = Q\<lparr>
     rat_linear_atoms := RatEq (RatExpr 0 [(1, y), (-1, x)]) 0 # rat_linear_atoms Q,
     rat_query_bounds := RatLower x 0 # rat_query_bounds Q\<rparr>"

definition relu_inactive_facts :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_query" where
  "relu_inactive_facts Q x y = Q\<lparr>
     rat_linear_atoms := RatEq (RatExpr 0 [(1, y)]) 0 # rat_linear_atoms Q,
     rat_query_bounds := RatUpper x 0 # rat_query_bounds Q\<rparr>"

datatype fact =
    Fact_Bound rat_bound "rat list"
  | Fact_Hull var var
  | Fact_Phase_Active var var rat_bound "rat list"
  | Fact_Phase_Inactive var var rat_bound "rat list"
  | Fact_Relu_Upper var var rat rat
  | Fact_Relu_Aux_Upper var var var rat rat "rat list" "rat list"
  | Fact_Relu_Output_Aux_Upper var var var rat rat "rat list" "rat list"
  | Fact_Relu_Aux_Lower_Output_Upper var var var rat rat "rat list" "rat list"

text \<open>
  Unlike Relu_Fix_Active/Inactive, the phase facts keep the ReLU: the
  preprocessed query may still contain it. Each fact adds constraints only.
\<close>

fun apply_fact :: "rat_query \<Rightarrow> fact \<Rightarrow> rat_query option" where
  "apply_fact Q (Fact_Bound b ws) =
     (if check_linear_bound Q b ws then Some (rat_add_bound Q b) else None)"
| "apply_fact Q (Fact_Hull x y) =
     (if ReLU x y \<in> set (rat_relu_atoms Q) then Some (relu_hull_query Q x y) else None)"
| "apply_fact Q (Fact_Phase_Active x y b ws) =
     (if check_relu_fixed_active Q x y b ws then Some (relu_active_facts Q x y) else None)"
| "apply_fact Q (Fact_Phase_Inactive x y b ws) =
     (if check_relu_fixed_inactive Q x y b ws then Some (relu_inactive_facts Q x y) else None)"
| "apply_fact Q (Fact_Relu_Upper x y u b) =
     (if check_relu_upper_bound Q x y u b then Some (rat_add_bound Q (RatUpper y b)) else None)"
| "apply_fact Q (Fact_Relu_Aux_Upper x y a l u pos neg) =
     (if check_relu_aux_upper_bound Q x y a l u pos neg
      then Some (rat_add_bound Q (RatUpper a u)) else None)"
| "apply_fact Q (Fact_Relu_Output_Aux_Upper x y a l u pos neg) =
     (if check_relu_output_aux_upper_bound Q x y a l u pos neg
      then Some (rat_add_bound Q (RatUpper a u)) else None)"
| "apply_fact Q (Fact_Relu_Aux_Lower_Output_Upper x y a l u pos neg) =
     (if check_relu_aux_lower_output_upper_bound Q x y a l u pos neg
      then Some (rat_add_bound Q (RatUpper y u)) else None)"

lemma apply_fact_models:
  assumes applied: "apply_fact Q f = Some R"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_query v (embed_query R)"
proof (cases f)
  case (Fact_Bound b ws)
  then show ?thesis
    using applied model rat_linear_bound_preserves_models[of Q b ws]
    by (auto simp: models_def split: if_splits)
next
  case (Fact_Hull x y)
  then show ?thesis
    using applied relu_hull_query_models[OF _ model] by (auto split: if_splits)
next
  case (Fact_Phase_Active x y b ws)
  with applied have checked: "check_relu_fixed_active Q x y b ws"
      and result: "R = relu_active_facts Q x y"
    by (auto split: if_splits)
  have "0 \<le> v x \<and> v y = v x" by (rule check_relu_fixed_active_sound[OF checked model])
  then show ?thesis
    using model by (simp add: result relu_active_facts_def embed_query_def satisfies_query_def)
next
  case (Fact_Phase_Inactive x y b ws)
  with applied have checked: "check_relu_fixed_inactive Q x y b ws"
      and result: "R = relu_inactive_facts Q x y"
    by (auto split: if_splits)
  have "v x \<le> 0 \<and> v y = 0" by (rule check_relu_fixed_inactive_sound[OF checked model])
  then show ?thesis
    using model by (simp add: result relu_inactive_facts_def embed_query_def satisfies_query_def)
next
  case (Fact_Relu_Upper x y u b)
  then show ?thesis
    using applied model rat_relu_upper_preserves_models[of Q x y u b]
    by (auto simp: models_def split: if_splits)
next
  case (Fact_Relu_Aux_Upper x y a l u pos neg)
  then show ?thesis
    using applied model rat_relu_aux_upper_preserves_models[of Q x y a l u pos neg]
    by (auto simp: models_def split: if_splits)
next
  case (Fact_Relu_Output_Aux_Upper x y a l u pos neg)
  then show ?thesis
    using applied model rat_relu_output_aux_upper_preserves_models[of Q x y a l u pos neg]
    by (auto simp: models_def split: if_splits)
next
  case (Fact_Relu_Aux_Lower_Output_Upper x y a l u pos neg)
  then show ?thesis
    using applied model rat_relu_aux_lower_output_upper_preserves_models[of Q x y a l u pos neg]
    by (auto simp: models_def split: if_splits)
qed

fun apply_facts :: "rat_query \<Rightarrow> fact list \<Rightarrow> rat_query option" where
  "apply_facts Q [] = Some Q"
| "apply_facts Q (f # fs) =
     (case apply_fact Q f of None \<Rightarrow> None | Some R \<Rightarrow> apply_facts R fs)"

lemma apply_facts_models:
  assumes "apply_facts Q fs = Some R"
      and "satisfies_query v (embed_query Q)"
  shows "satisfies_query v (embed_query R)"
  using assms
proof (induction fs arbitrary: Q)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  then obtain P where head: "apply_fact Q f = Some P" and tail: "apply_facts P fs = Some R"
    by (auto split: option.splits)
  show ?case by (rule Cons.IH[OF tail apply_fact_models[OF head Cons.prems(2)]])
qed

section \<open>Renaming and projection\<close>

definition proj_var :: "var list \<Rightarrow> var \<Rightarrow> var" where
  "proj_var \<sigma> u = (if u < length \<sigma> then \<sigma> ! u else u)"

fun rename_expr :: "var list \<Rightarrow> rat_linexpr \<Rightarrow> rat_linexpr" where
  "rename_expr \<sigma> (RatExpr c ts) = RatExpr c (map (\<lambda>(a, x). (a, proj_var \<sigma> x)) ts)"

lemma eval_rename_terms:
  "eval_rat_terms v (map (\<lambda>(a, x). (a, proj_var \<sigma> x)) ts) =
    eval_rat_terms (\<lambda>u. v (proj_var \<sigma> u)) ts"
  by (induction ts) auto

lemma eval_rename_expr:
  "eval_rat_expr v (rename_expr \<sigma> e) = eval_rat_expr (\<lambda>u. v (proj_var \<sigma> u)) e"
  by (cases e) (simp only: rename_expr.simps eval_rat_expr_simps eval_rename_terms)

definition same_value :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat list list \<Rightarrow> bool" where
  "same_value Q a b ws \<longleftrightarrow> a = b \<or>
     (case ws of
        [p, n] \<Rightarrow> check_linear_implication Q (RatExpr 0 [(1, a), (-1, b)]) p \<and>
                  check_linear_implication Q (RatExpr 0 [(1, b), (-1, a)]) n
      | _ \<Rightarrow> False)"

lemma same_value_sound:
  assumes "same_value Q a b ws" and "satisfies_query v (embed_query Q)"
  shows "v a = v b"
proof (cases "a = b")
  case False
  then obtain p n where ws: "ws = [p, n]"
      and pos: "check_linear_implication Q (RatExpr 0 [(1, a), (-1, b)]) p"
      and neg: "check_linear_implication Q (RatExpr 0 [(1, b), (-1, a)]) n"
    using assms(1) by (auto simp: same_value_def split: list.splits)
  have "v a - v b \<le> 0" using check_linear_implication_sound[OF pos assms(2)] by simp
  moreover have "v b - v a \<le> 0" using check_linear_implication_sound[OF neg assms(2)] by simp
  ultimately show ?thesis by simp
qed simp

datatype relu_link = Relu_Link var var "rat list list" "rat list list"

text \<open>
  Relu_Link x y wx wy links a ReLU x' y' of P to ReLU x y of Q: the witnesses
  prove x = proj x' and y = proj y' (or the variables coincide).
\<close>

fun check_relu_link :: "rat_query \<Rightarrow> var list \<Rightarrow> relu_constraint \<Rightarrow> relu_link \<Rightarrow> bool" where
  "check_relu_link Q \<sigma> (ReLU x' y') (Relu_Link x y wx wy) \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and>
     same_value Q x (proj_var \<sigma> x') wx \<and> same_value Q y (proj_var \<sigma> y') wy"

datatype projection = Projection "fact list" "var list" "rat list list" "relu_link list"

fun check_projection :: "rat_query \<Rightarrow> projection \<Rightarrow> rat_query \<Rightarrow> bool" where
  "check_projection Q (Projection facts \<sigma> rows links) P \<longleftrightarrow>
     (case apply_facts Q facts of
        None \<Rightarrow> False
      | Some R \<Rightarrow>
          list_all2 (\<lambda>e ws. check_linear_implication R (rename_expr \<sigma> e) ws)
            (normalize_query P) rows \<and>
          list_all2 (check_relu_link R \<sigma>) (rat_relu_atoms P) links)"

fun projection_map :: "projection \<Rightarrow> var list" where
  "projection_map (Projection facts \<sigma> rows links) = \<sigma>"

lemma list_all2_left_witness:
  "list_all2 P xs ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. P x y"
  by (induction xs ys rule: list_all2_induct) auto

theorem check_projection_model:
  assumes checked: "check_projection Q pr P"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_query (\<lambda>u. v (proj_var (projection_map pr) u)) (embed_query P)"
proof -
  obtain facts \<sigma> rows links where pr: "pr = Projection facts \<sigma> rows links"
    by (cases pr)
  let ?w = "\<lambda>u. v (proj_var \<sigma> u)"
  obtain R where facts: "apply_facts Q facts = Some R"
      and implied: "list_all2 (\<lambda>e ws. check_linear_implication R (rename_expr \<sigma> e) ws)
                      (normalize_query P) rows"
      and linked: "list_all2 (check_relu_link R \<sigma>) (rat_relu_atoms P) links"
    using checked by (auto simp: pr split: option.splits)
  have enriched: "satisfies_query v (embed_query R)"
    by (rule apply_facts_models[OF facts model])
  have rows_hold: "\<forall>e \<in> set (normalize_query P). eval_rat_expr ?w e \<le> 0"
  proof
    fix e assume "e \<in> set (normalize_query P)"
    then obtain ws where "check_linear_implication R (rename_expr \<sigma> e) ws"
      using list_all2_left_witness[OF implied] by blast
    from check_linear_implication_sound[OF this enriched]
    show "eval_rat_expr ?w e \<le> 0" by (simp add: eval_rename_expr)
  qed
  have relus_hold: "\<forall>r \<in> set (rat_relu_atoms P). satisfies_relu_constraint ?w r"
  proof
    fix r assume member: "r \<in> set (rat_relu_atoms P)"
    obtain x' y' where r: "r = ReLU x' y'" by (cases r)
    obtain l where "check_relu_link R \<sigma> r l"
      using list_all2_left_witness[OF linked member] by blast
    then obtain x y wx wy where source: "ReLU x y \<in> set (rat_relu_atoms R)"
        and same_x: "same_value R x (proj_var \<sigma> x') wx"
        and same_y: "same_value R y (proj_var \<sigma> y') wy"
      by (cases l) (auto simp: r)
    have "satisfies_relu v x y"
      using query_relu[OF enriched] source by (simp add: embed_query_def)
    moreover have "v x = ?w x'" "v y = ?w y'"
      using same_value_sound[OF same_x enriched] same_value_sound[OF same_y enriched] by simp_all
    ultimately show "satisfies_relu_constraint ?w r"
      by (simp add: r satisfies_relu_def)
  qed
  show ?thesis
    using rows_hold relus_hold by (simp add: pr embed_query_normalization)
qed

corollary check_projection_unsatisfiable:
  assumes "check_projection Q pr P"
      and "unsatisfiable (embed_query P)"
  shows "unsatisfiable (embed_query Q)"
  using check_projection_model[OF assms(1)] assms(2)
  unfolding unsatisfiable_def satisfiable_def by blast

corollary check_projection_rejects_false_unsat:
  assumes "satisfies_query v (embed_query Q)"
      and "unsatisfiable (embed_query P)"
  shows "\<not> check_projection Q pr P"
  using check_projection_unsatisfiable[of Q pr P] assms
  unfolding unsatisfiable_def satisfiable_def by blast

export_code check_projection apply_facts Projection Relu_Link
  Fact_Bound Fact_Hull Fact_Phase_Active Fact_Phase_Inactive Fact_Relu_Upper
  Fact_Relu_Aux_Upper Fact_Relu_Output_Aux_Upper Fact_Relu_Aux_Lower_Output_Upper
  checking SML

end
