theory Tableau_Simplex_Run
  imports Tableau_Index_Layout
begin

text \<open>
  A fuelled exact loop of the linear part of Engine::solve: while a basic is
  out of bounds, pick an eligible entering variable, run the exact Harris
  ratio test and apply the choice (Engine::performSimplexStep,
  Engine.cpp:632-831). The native entering strategy
  (_activeEntryStrategy->select) is a heuristic; this loop takes the first
  eligible nonbasic in index order. Soundness does not depend on the
  choice. Termination is not claimed: exhausted fuel is reported as
  Out_Of_Fuel, which is not a result about the query.
\<close>

datatype simplex_outcome = Feasible | Infeasible | Out_Of_Fuel

fun first_eligible :: "tableau_state \<Rightarrow> var list \<Rightarrow> (var \<times> direction) option" where
  "first_eligible S [] = None"
| "first_eligible S (j # js) =
     (case entering_direction S j of
        Some d \<Rightarrow> Some (j, d)
      | None \<Rightarrow> first_eligible S js)"

definition all_between :: "tableau_state \<Rightarrow> var list \<Rightarrow> bool" where
  "all_between S bs \<longleftrightarrow> list_all (\<lambda>x. status_of S x = Between) bs"

text \<open>
  A pivot writes the entering variable into the leaving variable's basic
  index and the leaving variable into the entering variable's nonbasic index,
  as in Tableau.cpp:779-782.
\<close>

fun simplex_run ::
  "nat \<Rightarrow> tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow>
   simplex_outcome \<times> tableau_state \<times> var list \<times> var list" where
  "simplex_run 0 S bs ns = (Out_Of_Fuel, S, bs, ns)"
| "simplex_run (Suc n) S bs ns =
     (if all_between S bs then (Feasible, S, bs, ns)
      else (case first_eligible S ns of
              None \<Rightarrow> (Infeasible, S, bs, ns)
            | Some (e, d) \<Rightarrow>
                (case exact_harris_ratio_test S e d bs of
                   Bound_Flip \<tau> \<Rightarrow> simplex_run n (apply_choice S e d (Bound_Flip \<tau>)) bs ns
                 | Leaving b \<tau> \<Rightarrow>
                     simplex_run n (apply_choice S e d (Leaving b \<tau>))
                       (bs[position bs b := e]) (ns[position ns e := b]))))"

definition simplex_invariant :: "tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "simplex_invariant S bs ns \<longleftrightarrow>
     tableau_rows_supported S \<and> tableau_rows_satisfied S \<and>
     tableau_nonbasic_bounds_satisfied S \<and> tableau_bounds_ordered S \<and>
     distinct bs \<and> distinct ns \<and>
     set bs = tableau_basics S \<and> set ns = tableau_nonbasics S"

lemma first_eligible_some:
  "first_eligible S ns = Some (e, d) \<Longrightarrow> e \<in> set ns \<and> entering_direction S e = Some d"
  by (induction S ns rule: first_eligible.induct) (auto split: option.splits)

lemma first_eligible_none:
  "first_eligible S ns = None \<Longrightarrow> \<forall>j\<in>set ns. entering_direction S j = None"
  by (induction S ns rule: first_eligible.induct) (auto split: option.splits)

lemma entering_direction_range:
  assumes "entering_direction S e = Some d"
  shows "0 < entering_range S e d"
  using assms by (auto simp: entering_direction_def entering_range_def split: if_splits)

lemma all_between_iff:
  "all_between S bs \<longleftrightarrow> (\<forall>x\<in>set bs. status_of S x = Between)"
  by (simp add: all_between_def list_all_iff)

lemma update_position:
  assumes "distinct xs" "x \<in> set xs" "y \<notin> set xs"
  shows "distinct (xs[position xs x := y])"
    and "set (xs[position xs x := y]) = insert y (set xs - {x})"
  using assms position_less[OF assms(2)]
  by (simp_all add: distinct_list_update set_update_distinct)

lemma simplex_step_invariant:
  assumes inv: "simplex_invariant S bs ns"
      and elig: "first_eligible S ns = Some (e, d)"
      and choice: "exact_harris_ratio_test S e d bs = c"
  defines "S' \<equiv> apply_choice S e d c"
  shows "tableau_bounded_models S' = tableau_bounded_models S"
    and "c = Bound_Flip \<tau> \<Longrightarrow> simplex_invariant S' bs ns"
    and "c = Leaving b \<tau> \<Longrightarrow>
           simplex_invariant S' (bs[position bs b := e]) (ns[position ns e := b])"
proof -
  have sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
    and nb: "tableau_nonbasic_bounds_satisfied S" and ord: "tableau_bounds_ordered S"
    and dbs: "distinct bs" and dns: "distinct ns"
    and sbs: "set bs = tableau_basics S" and sns: "set ns = tableau_nonbasics S"
    using inv unfolding simplex_invariant_def by auto
  have e: "e \<in> tableau_nonbasics S" and d: "entering_direction S e = Some d"
    using first_eligible_some[OF elig] sns by auto
  have "0 \<le> entering_range S e d" using entering_direction_range[OF d] by simp
  then have adm: "choice_admissible S e d c"
    using exact_harris_admissible[OF sbs, of e d] choice by simp
  note step = choice_invariants[OF sup rows nb ord e adm, folded S'_def]
  show "tableau_bounded_models S' = tableau_bounded_models S" using step(4) .
  show "c = Bound_Flip \<tau> \<Longrightarrow> simplex_invariant S' bs ns"
    using step dbs dns sbs sns by (simp add: simplex_invariant_def S'_def)
  assume c: "c = Leaving b \<tau>"
  have b: "b \<in> tableau_basics S" using adm c by simp
  have eB: "e \<notin> set bs" and bN: "b \<notin> set ns"
    using sup e b sbs sns unfolding tableau_rows_supported_def by blast+
  have "tableau_basics S' = insert e (tableau_basics S - {b})"
    "tableau_nonbasics S' = insert b (tableau_nonbasics S - {e})"
    using c by (simp_all add: S'_def)
  then show "simplex_invariant S' (bs[position bs b := e]) (ns[position ns e := b])"
    using step update_position[OF dbs _ eB, of b] update_position[OF dns _ bN, of e] b e sbs sns
    by (simp add: simplex_invariant_def)
qed

lemma simplex_run_sound_all:
  "simplex_invariant S bs ns \<Longrightarrow> simplex_run n S bs ns = (r, S', bs', ns') \<Longrightarrow>
     tableau_bounded_models S' = tableau_bounded_models S \<and> simplex_invariant S' bs' ns' \<and>
     (r = Feasible \<longrightarrow> tableau_candidate S' \<in> tableau_bounded_models S) \<and>
     (r = Infeasible \<longrightarrow> tableau_bounded_models S = {})"
proof (induction n arbitrary: S bs ns)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have inv: "simplex_invariant S bs ns" and run: "simplex_run (Suc n) S bs ns = (r, S', bs', ns')"
    using Suc.prems by auto
  have sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
    and nb: "tableau_nonbasic_bounds_satisfied S"
    and sbs: "set bs = tableau_basics S" and sns: "set ns = tableau_nonbasics S"
    using inv unfolding simplex_invariant_def by auto
  show ?case
  proof (cases "all_between S bs")
    case True
    then have "r = Feasible" "S' = S" "bs' = bs" "ns' = ns" using run by auto
    moreover have "tableau_candidate S \<in> tableau_bounded_models S"
      using all_between_candidate_feasible[OF sup rows nb] True sbs
      by (simp add: all_between_iff)
    ultimately show ?thesis using inv by simp
  next
    case notall: False
    show ?thesis
    proof (cases "first_eligible S ns")
      case None
      then have "r = Infeasible" "S' = S" "bs' = bs" "ns' = ns" using run notall by auto
      moreover have "tableau_bounded_models S = {}"
      proof (rule no_entering_candidate_infeasible[OF sup _ _ rows nb])
        show "finite (tableau_basics S)" "finite (tableau_nonbasics S)"
          using sbs sns by (metis finite_set)+
        show "\<exists>x\<in>tableau_basics S. status_of S x \<noteq> Between"
          using notall sbs by (auto simp: all_between_iff)
        show "\<forall>j\<in>tableau_nonbasics S. entering_direction S j = None"
          using first_eligible_none[OF None] sns by simp
      qed
      ultimately show ?thesis using inv by simp
    next
      case (Some ed)
      obtain e d where ed: "ed = (e, d)" by (cases ed)
      have elig: "first_eligible S ns = Some (e, d)" using Some ed by simp
      show ?thesis
      proof (cases "exact_harris_ratio_test S e d bs")
        case (Bound_Flip \<tau>)
        let ?S1 = "apply_choice S e d (Bound_Flip \<tau>)"
        have run1: "simplex_run n ?S1 bs ns = (r, S', bs', ns')"
          using run notall elig Bound_Flip by simp
        have inv1: "simplex_invariant ?S1 bs ns"
          using simplex_step_invariant(2)[OF inv elig Bound_Flip] by simp
        have same: "tableau_bounded_models ?S1 = tableau_bounded_models S"
          using simplex_step_invariant(1)[OF inv elig Bound_Flip] .
        show ?thesis
          using Suc.IH[OF inv1 run1] same by simp
      next
        case (Leaving b \<tau>)
        let ?S1 = "apply_choice S e d (Leaving b \<tau>)"
        let ?bs1 = "bs[position bs b := e]" and ?ns1 = "ns[position ns e := b]"
        have run1: "simplex_run n ?S1 ?bs1 ?ns1 = (r, S', bs', ns')"
          using run notall elig Leaving by simp
        have inv1: "simplex_invariant ?S1 ?bs1 ?ns1"
          using simplex_step_invariant(3)[OF inv elig Leaving] by simp
        have same: "tableau_bounded_models ?S1 = tableau_bounded_models S"
          using simplex_step_invariant(1)[OF inv elig Leaving] .
        show ?thesis
          using Suc.IH[OF inv1 run1] same by simp
      qed
    qed
  qed
qed

theorem simplex_run_sound:
  assumes "simplex_invariant S bs ns"
      and "simplex_run n S bs ns = (r, S', bs', ns')"
  shows "tableau_bounded_models S' = tableau_bounded_models S"
    and "simplex_invariant S' bs' ns'"
    and "r = Feasible \<Longrightarrow> tableau_candidate S' \<in> tableau_bounded_models S"
    and "r = Infeasible \<Longrightarrow> tableau_bounded_models S = {}"
  using simplex_run_sound_all[OF assms] by auto

text \<open>
  Relation to the equations the tableau represents: a Feasible result gives a
  real solution of the equations within the bounds, and an Infeasible result
  proves that none exists.
\<close>

corollary simplex_run_represented:
  assumes inv: "simplex_invariant S bs ns" and rep: "tableau_represents S E"
      and run: "simplex_run n S bs ns = (r, S', bs', ns')"
  defines "within v \<equiv> \<forall>x\<in>tableau_basics S \<union> tableau_nonbasics S.
                          tableau_lower S x \<le> v x \<and> v x \<le> tableau_upper S x"
  shows "r = Feasible \<Longrightarrow>
           (\<forall>c\<in>set E. satisfies_linear (tableau_candidate S') c) \<and> within (tableau_candidate S')"
    and "r = Infeasible \<Longrightarrow> \<not> (\<exists>v. (\<forall>c\<in>set E. satisfies_linear v c) \<and> within v)"
proof -
  have models: "tableau_bounded_models S = {v. (\<forall>c\<in>set E. satisfies_linear v c) \<and> within v}"
    using rep unfolding tableau_bounded_models_def tableau_represents_def within_def by auto
  show "r = Feasible \<Longrightarrow>
      (\<forall>c\<in>set E. satisfies_linear (tableau_candidate S') c) \<and> within (tableau_candidate S')"
    using simplex_run_sound(3)[OF inv run] models by blast
  show "r = Infeasible \<Longrightarrow> \<not> (\<exists>v. (\<forall>c\<in>set E. satisfies_linear v c) \<and> within v)"
    using simplex_run_sound(4)[OF inv run] models by blast
qed

text \<open>The loop and its parts are executable; this compiles the generated SML.\<close>

export_code simplex_run exact_harris_ratio_test apply_choice exchange_basis
  native_pivot native_degenerate_pivot native_bound_flip checking SML

end
