theory Rational_Linear_Constraints
  imports Query_Semantics
begin

text \<open>
  Exact rational data with an interpretation in the existing real semantics.
  This is our certificate-facing representation, not a decoder for C++ doubles.
  Source counterparts: src/engine/Equation.h and Tightening.h. The mathematical
  normalization below is not a formalization of Preprocessor.cpp.
\<close>

datatype rat_linexpr = RatExpr (rat_constant: rat) (rat_terms: "(rat \<times> var) list")

datatype rat_linear_constraint =
    RatEq rat_linexpr rat
  | RatLe rat_linexpr rat
  | RatGe rat_linexpr rat

datatype rat_bound = RatLower var rat | RatUpper var rat

record rat_query =
  rat_linear_atoms :: "rat_linear_constraint list"
  rat_query_bounds :: "rat_bound list"
  rat_relu_atoms :: "relu_constraint list"

fun embed_linexpr :: "rat_linexpr \<Rightarrow> linexpr" where
  "embed_linexpr (RatExpr c ts) =
     Linexpr (of_rat c) (map (\<lambda>(a, x). (of_rat a, x)) ts)"

fun embed_linear :: "rat_linear_constraint \<Rightarrow> linear_constraint" where
  "embed_linear (RatEq e b) = LinearEq (embed_linexpr e) (of_rat b)"
| "embed_linear (RatLe e b) = LinearLe (embed_linexpr e) (of_rat b)"
| "embed_linear (RatGe e b) = LinearGe (embed_linexpr e) (of_rat b)"

fun embed_bound :: "rat_bound \<Rightarrow> bound" where
  "embed_bound (RatLower x l) = Lower x (of_rat l)"
| "embed_bound (RatUpper x u) = Upper x (of_rat u)"

definition embed_query :: "rat_query \<Rightarrow> query" where
  "embed_query Q = \<lparr>
     linear_atoms = map embed_linear (rat_linear_atoms Q),
     query_bounds = map embed_bound (rat_query_bounds Q),
     relu_atoms = rat_relu_atoms Q\<rparr>"

abbreviation eval_rat_expr :: "valuation \<Rightarrow> rat_linexpr \<Rightarrow> real" where
  "eval_rat_expr v e \<equiv> eval_linexpr v (embed_linexpr e)"

fun eval_rat_terms :: "valuation \<Rightarrow> (rat \<times> var) list \<Rightarrow> real" where
  "eval_rat_terms v [] = 0"
| "eval_rat_terms v ((a, x) # ts) = of_rat a * v x + eval_rat_terms v ts"

lemma eval_embedded_terms [simp]:
  "eval_terms v (map (\<lambda>(a, x). (of_rat a, x)) ts) = eval_rat_terms v ts"
  by (induction ts) (auto split: prod.splits)

lemma eval_rat_expr_simps [simp]:
  "eval_rat_expr v (RatExpr c ts) = of_rat c + eval_rat_terms v ts"
  by simp

fun rat_add :: "rat_linexpr \<Rightarrow> rat_linexpr \<Rightarrow> rat_linexpr" where
  "rat_add (RatExpr c ts) (RatExpr d us) = RatExpr (c + d) (ts @ us)"

fun rat_scale :: "rat \<Rightarrow> rat_linexpr \<Rightarrow> rat_linexpr" where
  "rat_scale a (RatExpr c ts) =
     RatExpr (a * c) (map (\<lambda>(b, x). (a * b, x)) ts)"

definition rat_sub_rhs :: "rat_linexpr \<Rightarrow> rat \<Rightarrow> rat_linexpr" where
  "rat_sub_rhs e b = rat_add e (RatExpr (-b) [])"

lemma eval_rat_terms_append [simp]:
  "eval_rat_terms v (ts @ us) = eval_rat_terms v ts + eval_rat_terms v us"
  by (induction ts) (auto simp: add.assoc split: prod.splits)

lemma eval_rat_terms_scale:
  "eval_rat_terms v (map (\<lambda>(b, x). (a * b, x)) ts) =
     of_rat a * eval_rat_terms v ts"
  by (induction ts) (auto simp: of_rat_mult algebra_simps split: prod.splits)

lemma eval_rat_add [simp]:
  "eval_rat_expr v (rat_add e f) = eval_rat_expr v e + eval_rat_expr v f"
  by (cases e; cases f) (simp add: of_rat_add algebra_simps)

lemma eval_rat_scale [simp]:
  "eval_rat_expr v (rat_scale a e) = of_rat a * eval_rat_expr v e"
  by (cases e)
     (simp only: rat_scale.simps eval_rat_expr_simps eval_rat_terms_scale of_rat_mult distrib_left)

lemma eval_rat_sub_rhs [simp]:
  "eval_rat_expr v (rat_sub_rhs e b) = eval_rat_expr v e - of_rat b"
  by (simp add: rat_sub_rhs_def of_rat_minus)

text \<open>
  Each normalized expression denotes an inequality e \<le> 0. An equality
  contributes two rows, in the order e - b, then -(e - b). A lower bound
  contributes l - x; an upper bound contributes x - u. List order is part of
  the certificate interface and does not depend on a solver's tableau order.
\<close>

fun normalize_linear :: "rat_linear_constraint \<Rightarrow> rat_linexpr list" where
  "normalize_linear (RatEq e b) = [rat_sub_rhs e b, rat_scale (-1) (rat_sub_rhs e b)]"
| "normalize_linear (RatLe e b) = [rat_sub_rhs e b]"
| "normalize_linear (RatGe e b) = [rat_scale (-1) (rat_sub_rhs e b)]"

fun normalize_bound :: "rat_bound \<Rightarrow> rat_linexpr" where
  "normalize_bound (RatLower x l) = RatExpr l [(-1, x)]"
| "normalize_bound (RatUpper x u) = RatExpr (-u) [(1, x)]"

definition normalize_query :: "rat_query \<Rightarrow> rat_linexpr list" where
  "normalize_query Q = concat (map normalize_linear (rat_linear_atoms Q)) @
     map normalize_bound (rat_query_bounds Q)"

lemma normalize_linear_correct:
  "(\<forall>e \<in> set (normalize_linear c). eval_rat_expr v e \<le> 0) \<longleftrightarrow>
   satisfies_linear v (embed_linear c)"
  by (cases c; auto; linarith)

lemma normalize_bound_correct:
  "eval_rat_expr v (normalize_bound b) \<le> 0 \<longleftrightarrow>
   satisfies_bound v (embed_bound b)"
  by (cases b) (simp_all add: of_rat_minus)

lemma normalize_query_correct:
  "(\<forall>e \<in> set (normalize_query Q). eval_rat_expr v e \<le> 0) \<longleftrightarrow>
   (\<forall>c \<in> set (rat_linear_atoms Q). satisfies_linear v (embed_linear c)) \<and>
   (\<forall>b \<in> set (rat_query_bounds Q). satisfies_bound v (embed_bound b))"
  by (simp add: normalize_query_def ball_Un ball_UN
      normalize_linear_correct normalize_bound_correct)

theorem embed_query_normalization:
  "satisfies_query v (embed_query Q) \<longleftrightarrow>
   (\<forall>e \<in> set (normalize_query Q). eval_rat_expr v e \<le> 0) \<and>
   (\<forall>r \<in> set (rat_relu_atoms Q). satisfies_relu_constraint v r)"
  by (simp add: embed_query_def satisfies_query_def normalize_query_correct)

lemma query_implies_normalized:
  assumes "satisfies_query v (embed_query Q)"
  shows "\<forall>e \<in> set (normalize_query Q). eval_rat_expr v e \<le> 0"
  using assms by (simp add: embed_query_normalization)

definition rat_add_bound :: "rat_query \<Rightarrow> rat_bound \<Rightarrow> rat_query" where
  "rat_add_bound Q b = Q\<lparr>rat_query_bounds := b # rat_query_bounds Q\<rparr>"

lemma satisfies_rat_add_bound_iff:
  "satisfies_query v (embed_query (rat_add_bound Q b)) \<longleftrightarrow>
   satisfies_bound v (embed_bound b) \<and> satisfies_query v (embed_query Q)"
  by (auto simp: rat_add_bound_def embed_query_def satisfies_query_def)

end
