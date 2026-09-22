theory Marabou_Semantics
  imports Marabou_Syntax
begin

fun eval_terms :: "valuation \<Rightarrow> (real \<times> var) list \<Rightarrow> real" where
  "eval_terms v [] = 0"
| "eval_terms v ((a, x) # ts) = a * v x + eval_terms v ts"

fun eval_linexpr :: "valuation \<Rightarrow> linexpr \<Rightarrow> real" where
  "eval_linexpr v (Linexpr c ts) = c + eval_terms v ts"

definition const_expr :: "real \<Rightarrow> linexpr" where
  "const_expr c = Linexpr c []"

definition var_expr :: "var \<Rightarrow> linexpr" where
  "var_expr x = Linexpr 0 [(1, x)]"

fun add_linexpr :: "linexpr \<Rightarrow> linexpr \<Rightarrow> linexpr" where
  "add_linexpr (Linexpr c ts) (Linexpr d us) = Linexpr (c + d) (ts @ us)"

fun scale_linexpr :: "real \<Rightarrow> linexpr \<Rightarrow> linexpr" where
  "scale_linexpr a (Linexpr c ts) =
     Linexpr (a * c) (map (\<lambda>(b, x). (a * b, x)) ts)"

lemma eval_terms_append [simp]:
  "eval_terms v (ts @ us) = eval_terms v ts + eval_terms v us"
  by (induction ts) (auto simp: algebra_simps split: prod.splits)

lemma eval_terms_scale:
  "eval_terms v (map (\<lambda>(b, x). (a * b, x)) ts) = a * eval_terms v ts"
  by (induction ts) (auto simp: algebra_simps split: prod.splits)

lemma eval_const_expr [simp]: "eval_linexpr v (const_expr c) = c"
  by (simp add: const_expr_def)

lemma eval_var_expr [simp]: "eval_linexpr v (var_expr x) = v x"
  by (simp add: var_expr_def)

lemma eval_add_linexpr [simp]:
  "eval_linexpr v (add_linexpr e f) = eval_linexpr v e + eval_linexpr v f"
  by (cases e; cases f) (simp add: algebra_simps)

lemma eval_scale_linexpr [simp]:
  "eval_linexpr v (scale_linexpr a e) = a * eval_linexpr v e"
  by (cases e) (simp add: eval_terms_scale distrib_left)

lemma eval_terms_cong:
  assumes "\<And>a x. (a, x) \<in> set ts \<Longrightarrow> v x = w x"
  shows "eval_terms v ts = eval_terms w ts"
  using assms
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  obtain a x where t: "t = (a, x)" by (cases t) simp
  have head: "v x = w x" using Cons.prems t by auto
  have tail: "eval_terms v ts = eval_terms w ts"
    by (rule Cons.IH) (use Cons.prems in auto)
  show ?case by (simp add: t head tail)
qed

end
