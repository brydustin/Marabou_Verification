theory Rational_Linear_Certificates
  imports Rational_Linear_Constraints
begin

text \<open>
  A leaf certificate is a list of rational weights aligned with normalize_query.
  Repeated variable occurrences are added exactly before testing cancellation.
  The executable functions below never inspect a real number or a valuation.

  This is a normalized-inequality checker, not Marabou's row-vector checker.
  Relevant source evidence: src/proofs/Contradiction.h, BoundExplainer.cpp,
  UnsatCertificateUtils.cpp, and AletheProofWriter.cpp::linearCombinationMpq.
  No decoder or equivalence with those C++ operations is asserted here.
\<close>

fun merge_term :: "rat \<times> var \<Rightarrow> (rat \<times> var) list \<Rightarrow> (rat \<times> var) list" where
  "merge_term t [] = [t]"
| "merge_term (a, x) ((b, y) # ts) =
     (if x = y then (a + b, y) # ts else (b, y) # merge_term (a, x) ts)"

fun collect_terms :: "(rat \<times> var) list \<Rightarrow> (rat \<times> var) list" where
  "collect_terms [] = []"
| "collect_terms (t # ts) = merge_term t (collect_terms ts)"

lemma eval_merge_term [simp]:
  "eval_rat_terms v (merge_term (a, x) ts) = of_rat a * v x + eval_rat_terms v ts"
  by (induction ts) (auto simp: of_rat_add algebra_simps split: prod.splits)

lemma eval_collect_terms [simp]:
  "eval_rat_terms v (collect_terms ts) = eval_rat_terms v ts"
  by (induction ts) (auto split: prod.splits)

lemma all_zero_terms_eval:
  assumes "list_all (\<lambda>t. fst t = 0) ts"
  shows "eval_rat_terms v ts = 0"
  using assms by (induction ts) (auto split: prod.splits)

definition constant_contradiction :: "rat_linexpr \<Rightarrow> bool" where
  "constant_contradiction e \<longleftrightarrow>
     0 < rat_constant e \<and>
     list_all (\<lambda>t. fst t = 0) (collect_terms (rat_terms e))"

lemma constant_contradiction_positive:
  assumes "constant_contradiction e"
  shows "0 < eval_rat_expr v e"
proof -
  obtain c ts where e: "e = RatExpr c ts" by (cases e) simp
  have positive: "0 < c" and zero: "list_all (\<lambda>t. fst t = 0) (collect_terms ts)"
    using assms by (simp_all add: e constant_contradiction_def)
  have "eval_rat_terms v (collect_terms ts) = 0"
    using zero by (rule all_zero_terms_eval)
  then have "eval_rat_terms v ts = 0" by simp
  with positive show ?thesis by (simp add: e)
qed

text \<open>
  None rejects unequal list lengths or any negative weight. In particular,
  this function does not silently truncate a zip of rows and weights.
\<close>

fun weighted_sum :: "rat list \<Rightarrow> rat_linexpr list \<Rightarrow> rat_linexpr option" where
  "weighted_sum [] [] = Some (RatExpr 0 [])"
| "weighted_sum (w # ws) (e # es) =
     (if 0 \<le> w then map_option (rat_add (rat_scale w e)) (weighted_sum ws es)
      else None)"
| "weighted_sum [] (e # es) = None"
| "weighted_sum (w # ws) [] = None"

lemma weighted_sum_wellformed:
  assumes "weighted_sum ws es = Some s"
  shows "length ws = length es \<and> list_all (\<lambda>w. 0 \<le> w) ws"
  using assms
  by (induction ws es arbitrary: s rule: weighted_sum.induct)
     (auto split: if_splits option.splits)

lemma weighted_sum_nonpositive:
  assumes sum: "weighted_sum ws es = Some s"
      and rows: "\<forall>e \<in> set es. eval_rat_expr v e \<le> 0"
  shows "eval_rat_expr v s \<le> 0"
  using sum rows
proof (induction ws arbitrary: es s)
  case Nil
  then show ?case by (cases es) auto
next
  case (Cons w ws)
  obtain e rest where es: "es = e # rest"
    using Cons.prems(1) by (cases es) auto
  obtain t where nonneg: "0 \<le> w" and tail: "weighted_sum ws rest = Some t"
      and s: "s = rat_add (rat_scale w e) t"
    using Cons.prems(1) by (auto simp: es split: if_splits option.splits)
  have head_le: "eval_rat_expr v e \<le> 0"
      and rest_le: "\<forall>f \<in> set rest. eval_rat_expr v f \<le> 0"
    using Cons.prems(2) by (auto simp: es)
  have tail_le: "eval_rat_expr v t \<le> 0"
    by (rule Cons.IH[OF tail rest_le])
  have "(0::real) \<le> of_rat w" using nonneg by simp
  then have scaled_le: "of_rat w * eval_rat_expr v e \<le> 0"
    using head_le by (rule mult_nonneg_nonpos)
  show ?case using scaled_le tail_le by (simp add: s add_nonpos_nonpos)
qed

definition check_linear_leaf :: "rat_query \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_linear_leaf Q ws \<longleftrightarrow>
     (case weighted_sum ws (normalize_query Q) of
        None \<Rightarrow> False
      | Some e \<Rightarrow> constant_contradiction e)"

theorem check_linear_leaf_sound:
  assumes accepted: "check_linear_leaf Q ws"
  shows "unsatisfiable (embed_query Q)"
proof (unfold unsatisfiable_iff_no_valuation, intro allI notI)
  fix v
  assume model: "satisfies_query v (embed_query Q)"
  obtain s where sum: "weighted_sum ws (normalize_query Q) = Some s"
      and contradiction: "constant_contradiction s"
    using accepted by (auto simp: check_linear_leaf_def split: option.splits)
  have rows: "\<forall>e \<in> set (normalize_query Q). eval_rat_expr v e \<le> 0"
    using model by (rule query_implies_normalized)
  have "eval_rat_expr v s \<le> 0" by (rule weighted_sum_nonpositive[OF sum rows])
  moreover have "0 < eval_rat_expr v s"
    by (rule constant_contradiction_positive[OF contradiction])
  ultimately show False by simp
qed

corollary check_linear_leaf_no_model:
  "check_linear_leaf Q ws \<Longrightarrow> \<not> (\<exists>v. satisfies_query v (embed_query Q))"
  using check_linear_leaf_sound unfolding unsatisfiable_def satisfiable_def by blast

corollary check_linear_leaf_rejects_model:
  "satisfies_query v (embed_query Q) \<Longrightarrow> \<not> check_linear_leaf Q ws"
  using check_linear_leaf_no_model by blast

text \<open>
  Compile the generated checker with the installed SML compiler. The second
  command also stores its source in the session exports. The ROOT export rule
  writes it to Isabelle/generated when building with the -e option.
\<close>

export_code check_linear_leaf RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU
  rat_query.make Fract int_of_integer nat_of_integer checking SML
export_code check_linear_leaf RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU
  rat_query.make Fract int_of_integer nat_of_integer in SML
  module_name Marabou_Linear_Leaf file_prefix Marabou_Linear_Leaf

end
