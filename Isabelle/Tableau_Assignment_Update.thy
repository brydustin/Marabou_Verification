theory Tableau_Assignment_Update
  imports Tableau_State
begin

text \<open>The coefficient list may mention a variable more than once.\<close>

fun linexpr_coefficient :: "(real \<times> var) list \<Rightarrow> var \<Rightarrow> real" where
  "linexpr_coefficient [] x = 0"
| "linexpr_coefficient ((a,y)#ts) x =
     (if y = x then a else 0) + linexpr_coefficient ts x"

lemma eval_terms_update:
  "eval_terms (v(x := r)) ts =
    eval_terms v ts + linexpr_coefficient ts x * (r - v x)"
  by (induction ts) (auto simp: linexpr_coefficient.simps algebra_simps)

lemma eval_linexpr_update:
  "eval_linexpr (v(x := r)) e =
    eval_linexpr v e +
      (case e of Linexpr c ts \<Rightarrow> linexpr_coefficient ts x) * (r - v x)"
  by (cases e) (simp add: eval_terms_update)

definition update_nonbasic_assignment ::
  "tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> tableau_state" where
  "update_nonbasic_assignment S x r = S\<lparr>
      tableau_nonbasic_value := (tableau_nonbasic_value S)(x := r),
      tableau_basic_value := (\<lambda>b.
        if b \<in> tableau_basics S then
          tableau_basic_value S b +
            linexpr_coefficient (case tableau_rows S b of Linexpr c ts \<Rightarrow> ts) x *
              (r - tableau_nonbasic_value S x)
        else tableau_basic_value S b)\<rparr>"

text \<open>This is the solved-row form of the native nonbasic assignment
update. The C++ code computes d = B⁻¹Aⱼ and performs x_B := x_B − d*delta.
Here a row stores coefficient −d.\<close>

theorem update_nonbasic_preserves_rows:
  assumes x: "x \<in> tableau_nonbasics S"
      and rows: "tableau_rows_satisfied S"
  shows "tableau_rows_satisfied (update_nonbasic_assignment S x r)"
proof -
  have row_eq:
    "\<And>b. b \<in> tableau_basics S \<Longrightarrow>
      tableau_basic_value S b = eval_linexpr (tableau_nonbasic_value S)
        (tableau_rows S b)"
    using rows unfolding tableau_rows_satisfied_def by blast
  show ?thesis
    using x row_eq
    unfolding tableau_rows_satisfied_def update_nonbasic_assignment_def
    by (auto simp: eval_linexpr_update split: linexpr.splits)
qed

theorem update_nonbasic_preserves_well_formed:
  assumes "tableau_well_formed S"
  shows "tableau_well_formed (update_nonbasic_assignment S x r)"
  using assms unfolding tableau_well_formed_def update_nonbasic_assignment_def
  by simp

theorem update_nonbasic_preserves_bounds:
  assumes x: "x \<in> tableau_nonbasics S"
      and bounds: "tableau_nonbasic_bounds_satisfied S"
      and target: "tableau_lower S x \<le> r" "r \<le> tableau_upper S x"
  shows "tableau_nonbasic_bounds_satisfied
           (update_nonbasic_assignment S x r)"
  using x bounds target
  unfolding tableau_nonbasic_bounds_satisfied_def
    update_nonbasic_assignment_def
  by (auto simp: fun_upd_apply)

theorem update_nonbasic_candidate_satisfies_rows:
  assumes wf: "tableau_well_formed S"
      and rows: "tableau_rows_satisfied S"
      and x: "x \<in> tableau_nonbasics S"
  shows "\<forall>b\<in>tableau_basics (update_nonbasic_assignment S x r).
      tableau_candidate (update_nonbasic_assignment S x r) b =
       eval_linexpr (tableau_candidate (update_nonbasic_assignment S x r))
         (tableau_rows (update_nonbasic_assignment S x r) b)"
  by (rule tableau_candidate_satisfies_rows)
     (auto intro: update_nonbasic_preserves_well_formed[OF wf]
       update_nonbasic_preserves_rows[OF x rows])

end
