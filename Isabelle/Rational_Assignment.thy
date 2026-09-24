theory Rational_Assignment
  imports ReLU_Auxiliary_Sequence
begin

text \<open>
  Exact SAT witnesses. An assignment is a finite list of (variable, rational)
  pairs with distinct variables; every unlisted variable has value 0.
  The checker evaluates every linear atom, bound and ReLU of the rational
  query exactly. Acceptance gives a real model of the embedded query.
  No floating-point value is interpreted here: a native assignment must first
  be reconstructed as exact rationals by an untrusted adapter, and only this
  check decides whether the reconstruction is a model.
  Source: src/engine/Engine.cpp::extractSolution copies Tableau::getValue
  doubles into IQuery::setSolutionValue; no refinement is claimed.
\<close>

type_synonym rat_assignment = "(var \<times> rat) list"

definition assignment_value :: "rat_assignment \<Rightarrow> var \<Rightarrow> rat" where
  "assignment_value \<sigma> x = (case map_of \<sigma> x of Some q \<Rightarrow> q | None \<Rightarrow> 0)"

definition assignment_valuation :: "rat_assignment \<Rightarrow> valuation" where
  "assignment_valuation \<sigma> x = of_rat (assignment_value \<sigma> x)"

fun rat_eval_terms :: "(var \<Rightarrow> rat) \<Rightarrow> (rat \<times> var) list \<Rightarrow> rat" where
  "rat_eval_terms f [] = 0"
| "rat_eval_terms f ((a, x) # ts) = a * f x + rat_eval_terms f ts"

fun rat_eval_expr :: "(var \<Rightarrow> rat) \<Rightarrow> rat_linexpr \<Rightarrow> rat" where
  "rat_eval_expr f (RatExpr c ts) = c + rat_eval_terms f ts"

lemma of_rat_eval_terms:
  "of_rat (rat_eval_terms f ts) = eval_rat_terms (\<lambda>x. of_rat (f x)) ts"
  by (induction ts) (auto simp: of_rat_add of_rat_mult split: prod.splits)

lemma of_rat_eval_expr:
  "of_rat (rat_eval_expr f e) = eval_rat_expr (\<lambda>x. of_rat (f x)) e"
  by (cases e) (simp add: of_rat_add of_rat_eval_terms)

fun check_rat_linear :: "(var \<Rightarrow> rat) \<Rightarrow> rat_linear_constraint \<Rightarrow> bool" where
  "check_rat_linear f (RatEq e b) = (rat_eval_expr f e = b)"
| "check_rat_linear f (RatLe e b) = (rat_eval_expr f e \<le> b)"
| "check_rat_linear f (RatGe e b) = (b \<le> rat_eval_expr f e)"

fun check_rat_bound :: "(var \<Rightarrow> rat) \<Rightarrow> rat_bound \<Rightarrow> bool" where
  "check_rat_bound f (RatLower x l) = (l \<le> f x)"
| "check_rat_bound f (RatUpper x u) = (f x \<le> u)"

fun check_rat_relu :: "(var \<Rightarrow> rat) \<Rightarrow> relu_constraint \<Rightarrow> bool" where
  "check_rat_relu f (ReLU x y) = (f y = max 0 (f x))"

definition check_rat_assignment :: "rat_query \<Rightarrow> rat_assignment \<Rightarrow> bool" where
  "check_rat_assignment Q \<sigma> \<longleftrightarrow>
     distinct (map fst \<sigma>) \<and>
     list_all (check_rat_linear (assignment_value \<sigma>)) (rat_linear_atoms Q) \<and>
     list_all (check_rat_bound (assignment_value \<sigma>)) (rat_query_bounds Q) \<and>
     list_all (check_rat_relu (assignment_value \<sigma>)) (rat_relu_atoms Q)"

lemma check_rat_linear_iff:
  "check_rat_linear f c \<longleftrightarrow> satisfies_linear (\<lambda>x. of_rat (f x)) (embed_linear c)"
proof (cases c)
  case (RatEq e b)
  have "rat_eval_expr f e = b \<longleftrightarrow> (of_rat (rat_eval_expr f e) :: real) = of_rat b"
    by (simp only: of_rat_eq_iff)
  then show ?thesis by (simp add: RatEq of_rat_eval_expr)
next
  case (RatLe e b)
  have "rat_eval_expr f e \<le> b \<longleftrightarrow> (of_rat (rat_eval_expr f e) :: real) \<le> of_rat b"
    by (simp only: of_rat_less_eq)
  then show ?thesis by (simp add: RatLe of_rat_eval_expr)
next
  case (RatGe e b)
  have "b \<le> rat_eval_expr f e \<longleftrightarrow> (of_rat b :: real) \<le> of_rat (rat_eval_expr f e)"
    by (simp only: of_rat_less_eq)
  then show ?thesis by (simp add: RatGe of_rat_eval_expr)
qed

lemma check_rat_bound_iff:
  "check_rat_bound f b \<longleftrightarrow> satisfies_bound (\<lambda>x. of_rat (f x)) (embed_bound b)"
  by (cases b) (simp_all add: of_rat_less_eq)

lemma of_rat_max_zero: "(of_rat (max 0 q) :: real) = max 0 (of_rat q)"
  by (simp add: max_def of_rat_less_eq)

lemma check_rat_relu_iff:
  "check_rat_relu f r \<longleftrightarrow> satisfies_relu_constraint (\<lambda>x. of_rat (f x)) r"
proof (cases r)
  case (ReLU x y)
  have "f y = max 0 (f x) \<longleftrightarrow> (of_rat (f y) :: real) = of_rat (max 0 (f x))"
    by (simp only: of_rat_eq_iff)
  then show ?thesis by (simp add: ReLU satisfies_relu_def relu_def of_rat_max_zero)
qed

lemma assignment_valuation_eq:
  "assignment_valuation \<sigma> = (\<lambda>x. of_rat (assignment_value \<sigma> x))"
  by (simp add: assignment_valuation_def fun_eq_iff)

theorem check_rat_assignment_iff:
  assumes "distinct (map fst \<sigma>)"
  shows "check_rat_assignment Q \<sigma> \<longleftrightarrow>
    satisfies_query (assignment_valuation \<sigma>) (embed_query Q)"
  using assms
  by (simp add: check_rat_assignment_def satisfies_query_def embed_query_def list_all_iff
      check_rat_linear_iff check_rat_bound_iff check_rat_relu_iff assignment_valuation_eq)

theorem check_rat_assignment_sound:
  assumes "check_rat_assignment Q \<sigma>"
  shows "satisfies_query (assignment_valuation \<sigma>) (embed_query Q)"
  using assms check_rat_assignment_iff by (auto simp: check_rat_assignment_def)

corollary check_rat_assignment_satisfiable:
  "check_rat_assignment Q \<sigma> \<Longrightarrow> satisfiable (embed_query Q)"
  using check_rat_assignment_sound unfolding satisfiable_def by blast

corollary check_rat_assignment_excludes_certificate:
  "check_rat_assignment Q \<sigma> \<Longrightarrow> \<not> check_certificate Q cert"
  by (rule check_certificate_rejects_model[OF check_rat_assignment_sound])

corollary unsatisfiable_rejects_assignment:
  "unsatisfiable (embed_query Q) \<Longrightarrow> \<not> check_rat_assignment Q \<sigma>"
  using check_rat_assignment_satisfiable unfolding unsatisfiable_def by blast

text \<open>
  Checked introductions are equisatisfiable, so an assignment accepted for a
  processed query also proves its explicit starting query satisfiable.
  (The checked sequences only add constraints on fresh variables, so the
  same assignment can also be checked against the starting query directly.)
\<close>

theorem fixed_aux_sequence_assignment_satisfiable:
  assumes "rat_introduce_fixed_aux_sequence Q steps = Some P"
      and "check_rat_assignment P \<sigma>"
  shows "satisfiable (embed_query Q)"
  using fixed_aux_sequence_satisfiable_iff[OF assms(1)] check_rat_assignment_satisfiable[OF assms(2)]
  by blast

theorem relu_aux_sequence_assignment_satisfiable:
  assumes "rat_introduce_relu_aux_sequence Q relu_steps = Some R"
      and "rat_introduce_fixed_aux_sequence R steps = Some P"
      and "check_rat_assignment P \<sigma>"
  shows "satisfiable (embed_query Q)"
  using relu_aux_sequence_satisfiable_iff[OF assms(1)]
    fixed_aux_sequence_assignment_satisfiable[OF assms(2,3)]
  by blast

export_code check_rat_assignment checking SML
export_code check_rat_assignment RatExpr RatEq RatLe RatGe RatLower RatUpper ReLU
  rat_query.make Fract int_of_integer nat_of_integer in SML
  module_name Marabou_Assignment_Checker file_prefix Marabou_Assignment_Checker

end
