theory Tableau_State
  imports Tableau_Auxiliary
begin

text \<open>An exact mathematical tableau state in solved-row form.\<close>

record tableau_state =
  tableau_basics :: "var set"
  tableau_nonbasics :: "var set"
  tableau_rows :: "var \<Rightarrow> linexpr"
  tableau_lower :: "var \<Rightarrow> real"
  tableau_upper :: "var \<Rightarrow> real"
  tableau_nonbasic_value :: valuation
  tableau_basic_value :: valuation

definition tableau_well_formed :: "tableau_state \<Rightarrow> bool" where
  "tableau_well_formed S \<longleftrightarrow>
     finite (tableau_basics S) \<and>
     finite (tableau_nonbasics S) \<and>
     tableau_basics S \<inter> tableau_nonbasics S = {} \<and>
     (\<forall>b\<in>tableau_basics S.
        linexpr_vars (tableau_rows S b) \<subseteq> tableau_nonbasics S) \<and>
     (\<forall>j\<in>tableau_nonbasics S. tableau_lower S j \<le> tableau_upper S j)"

definition tableau_rows_satisfied :: "tableau_state \<Rightarrow> bool" where
  "tableau_rows_satisfied S \<longleftrightarrow>
     (\<forall>b\<in>tableau_basics S.
        tableau_basic_value S b =
          eval_linexpr (tableau_nonbasic_value S) (tableau_rows S b))"

definition tableau_nonbasic_bounds_satisfied :: "tableau_state \<Rightarrow> bool" where
  "tableau_nonbasic_bounds_satisfied S \<longleftrightarrow>
     (\<forall>j\<in>tableau_nonbasics S.
        tableau_lower S j \<le> tableau_nonbasic_value S j \<and>
        tableau_nonbasic_value S j \<le> tableau_upper S j)"

definition tableau_candidate :: "tableau_state \<Rightarrow> valuation" where
  "tableau_candidate S x =
     (if x \<in> tableau_basics S
      then tableau_basic_value S x
      else tableau_nonbasic_value S x)"

definition tableau_models :: "tableau_state \<Rightarrow> valuation set" where
  "tableau_models S =
     {v. \<forall>b\<in>tableau_basics S.
           v b = eval_linexpr v (tableau_rows S b)}"

lemma tableau_candidate_satisfies_rows:
  assumes wf: "tableau_well_formed S"
      and rows: "tableau_rows_satisfied S"
  shows "\<forall>b\<in>tableau_basics S.
           tableau_candidate S b =
             eval_linexpr (tableau_candidate S) (tableau_rows S b)"
proof -
  have disj: "tableau_basics S \<inter> tableau_nonbasics S = {}"
    using wf unfolding tableau_well_formed_def by blast
  have support:
    "\<And>b. b \<in> tableau_basics S \<Longrightarrow>
       linexpr_vars (tableau_rows S b) \<subseteq> tableau_nonbasics S"
    using wf unfolding tableau_well_formed_def by blast
  have roweq:
    "\<And>b. b \<in> tableau_basics S \<Longrightarrow>
       tableau_basic_value S b =
         eval_linexpr (tableau_nonbasic_value S) (tableau_rows S b)"
    using rows unfolding tableau_rows_satisfied_def by blast
  show ?thesis
  proof (intro ballI)
    fix b
    assume b: "b \<in> tableau_basics S"
    have agree:
      "\<And>x. x \<in> linexpr_vars (tableau_rows S b) \<Longrightarrow>
         tableau_candidate S x = tableau_nonbasic_value S x"
    proof -
      fix x
      assume x: "x \<in> linexpr_vars (tableau_rows S b)"
      have xn: "x \<in> tableau_nonbasics S"
        using support[OF b] x by blast
      have xb: "x \<notin> tableau_basics S"
        using disj xn by blast
      show "tableau_candidate S x = tableau_nonbasic_value S x"
        using xb unfolding tableau_candidate_def by simp
    qed
    have evaleq:
      "eval_linexpr (tableau_candidate S) (tableau_rows S b) =
       eval_linexpr (tableau_nonbasic_value S) (tableau_rows S b)"
      by (rule eval_linexpr_vars_cong[OF agree])
    show "tableau_candidate S b =
          eval_linexpr (tableau_candidate S) (tableau_rows S b)"
      using roweq[OF b] evaleq b unfolding tableau_candidate_def by simp
  qed
qed

lemma tableau_models_update_independent:
  "tableau_models S = tableau_models
     (S\<lparr>tableau_nonbasic_value := (tableau_nonbasic_value S)(j := t),
        tableau_basic_value := tableau_basic_value S\<rparr>)"
  unfolding tableau_models_def by simp

end
