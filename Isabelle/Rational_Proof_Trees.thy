theory Rational_Proof_Trees
  imports Rational_Linear_Implication ReLU_Splitting ReLU_Aux_Bound_Propagation
begin

text \<open>
  Split nodes select an existing ReLU and prove both canonical phases.
  Propagation nodes add a bound only after checking its linear or ReLU rule.
  The checker constructs the children itself; certificates cannot supply
  arbitrary child queries. Source counterparts are UnsatCertificateNode and
  ReluConstraint::getActiveSplit/getInactiveSplit. The mathematical phases
  explicitly state their equalities, independent of C++ auxiliary variables.
\<close>

definition rat_active_split :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_query" where
  "rat_active_split Q x y = Q\<lparr>
     rat_linear_atoms := RatEq (RatExpr 0 [(1, y), (-1, x)]) 0 # rat_linear_atoms Q,
     rat_query_bounds := RatLower x 0 # rat_query_bounds Q,
     rat_relu_atoms := filter (\<lambda>r. r \<noteq> ReLU x y) (rat_relu_atoms Q)\<rparr>"

definition rat_inactive_split :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_query" where
  "rat_inactive_split Q x y = Q\<lparr>
     rat_linear_atoms := RatEq (RatExpr 0 [(1, y)]) 0 # rat_linear_atoms Q,
     rat_query_bounds := RatUpper x 0 # rat_query_bounds Q,
     rat_relu_atoms := filter (\<lambda>r. r \<noteq> ReLU x y) (rat_relu_atoms Q)\<rparr>"

lemma embed_rat_active_split:
  "embed_query (rat_active_split Q x y) = active_split (embed_query Q) x y"
  by (simp add: embed_query_def rat_active_split_def active_split_def)

lemma embed_rat_inactive_split:
  "embed_query (rat_inactive_split Q x y) = inactive_split (embed_query Q) x y"
  by (simp add: embed_query_def rat_inactive_split_def inactive_split_def var_expr_def)

datatype certificate =
    Linear_Unsat "rat list"
  | Relu_Split var var certificate certificate
  | Relu_Upper var var rat rat certificate
  | Relu_Aux_Upper var var var rat rat "rat list" "rat list" certificate
  | Linear_Bound rat_bound "rat list" certificate

text \<open>
  Relu_Split stores the active child, then the inactive child. Relu_Upper stores
  the input upper bound, the output upper bound, and a checked continuation.
  Relu_Aux_Upper stores input/output/auxiliary variables, an input lower bound,
  an auxiliary upper bound, and two linear witnesses for the auxiliary equation.
  Linear_Bound stores a proposed bound, nonnegative normalized-row weights,
  and a continuation. The implication is checked before the bound is added.
  There are no holes.
\<close>

fun check_certificate :: "rat_query \<Rightarrow> certificate \<Rightarrow> bool" where
  "check_certificate Q (Linear_Unsat ws) = check_linear_leaf Q ws"
| "check_certificate Q (Relu_Split x y active inactive) =
     (ReLU x y \<in> set (rat_relu_atoms Q) \<and>
      check_certificate (rat_active_split Q x y) active \<and>
      check_certificate (rat_inactive_split Q x y) inactive)"
| "check_certificate Q (Relu_Upper x y u b child) =
     (check_relu_upper_bound Q x y u b \<and>
      check_certificate (rat_add_bound Q (RatUpper y b)) child)"
| "check_certificate Q (Relu_Aux_Upper x y a l u pos neg child) =
     (check_relu_aux_upper_bound Q x y a l u pos neg \<and>
      check_certificate (rat_add_bound Q (RatUpper a u)) child)"
| "check_certificate Q (Linear_Bound b ws child) =
     (check_linear_bound Q b ws \<and>
      check_certificate (rat_add_bound Q b) child)"

theorem check_certificate_sound:
  assumes "check_certificate Q cert"
  shows "unsatisfiable (embed_query Q)"
  using assms
proof (induction cert arbitrary: Q)
  case (Linear_Unsat ws)
  then show ?case by (simp add: check_linear_leaf_sound)
next
  case (Relu_Split x y active inactive)
  have member: "ReLU x y \<in> set (relu_atoms (embed_query Q))"
    using Relu_Split.prems by (simp add: embed_query_def)
  have active: "unsatisfiable (embed_query (rat_active_split Q x y))"
    using Relu_Split.IH(1) Relu_Split.prems by simp
  have inactive: "unsatisfiable (embed_query (rat_inactive_split Q x y))"
    using Relu_Split.IH(2) Relu_Split.prems by simp
  show ?case
    using unsatisfiable_relu_split[OF member] active inactive
    by (simp only: embed_rat_active_split embed_rat_inactive_split)
next
  case (Relu_Upper x y u b child)
  have checked: "check_relu_upper_bound Q x y u b"
      and accepted: "check_certificate (rat_add_bound Q (RatUpper y b)) child"
    using Relu_Upper.prems by simp_all
  have "unsatisfiable (embed_query (rat_add_bound Q (RatUpper y b)))"
    by (rule Relu_Upper.IH[OF accepted])
  then show ?case by (rule unsatisfiable_relu_upper_bound[OF checked])
next
  case (Relu_Aux_Upper x y a l u pos neg child)
  have checked: "check_relu_aux_upper_bound Q x y a l u pos neg"
      and accepted: "check_certificate (rat_add_bound Q (RatUpper a u)) child"
    using Relu_Aux_Upper.prems by simp_all
  have "unsatisfiable (embed_query (rat_add_bound Q (RatUpper a u)))"
    by (rule Relu_Aux_Upper.IH[OF accepted])
  then show ?case by (rule unsatisfiable_relu_aux_upper_bound[OF checked])
next
  case (Linear_Bound b ws child)
  have checked: "check_linear_bound Q b ws"
      and accepted: "check_certificate (rat_add_bound Q b) child"
    using Linear_Bound.prems by simp_all
  have "unsatisfiable (embed_query (rat_add_bound Q b))"
    by (rule Linear_Bound.IH[OF accepted])
  then show ?case by (rule unsatisfiable_linear_bound[OF checked])
qed

corollary check_certificate_no_model:
  "check_certificate Q cert \<Longrightarrow> \<not> (\<exists>v. satisfies_query v (embed_query Q))"
  using check_certificate_sound unfolding unsatisfiable_def satisfiable_def by blast

corollary check_certificate_rejects_model:
  "satisfies_query v (embed_query Q) \<Longrightarrow> \<not> check_certificate Q cert"
  using check_certificate_no_model by blast

export_code check_certificate check_relu_upper_bound check_relu_aux_upper_bound check_linear_bound check_linear_implication
  Linear_Unsat Relu_Split Relu_Upper Relu_Aux_Upper Linear_Bound
  RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU
  rat_query.make Fract int_of_integer nat_of_integer checking SML
export_code check_certificate check_relu_upper_bound check_relu_aux_upper_bound check_linear_bound check_linear_implication
  Linear_Unsat Relu_Split Relu_Upper Relu_Aux_Upper Linear_Bound
  RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU
  rat_query.make Fract int_of_integer nat_of_integer in SML
  module_name Marabou_Proof_Checker file_prefix Marabou_Proof_Checker

end
