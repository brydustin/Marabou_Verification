theory Tableau_Search
  imports Tableau_Relu_Split
begin

text \<open>
  Native search over ReLU splits on the tableau state. Source, at the pinned
  revision (src/engine):
  \<^item> SearchTreeHandler::performSplit (SearchTreeHandler.cpp:133-230) obtains
    the case splits, disables the constraint, stores the engine state with
    bounds only (STORE_BOUNDS_ONLY), pushes the context (after
    Engine::preContextPushHook saves the bounds through
    BoundManager::storeLocalBounds, BoundManager.cpp:223-230), applies the
    first split and keeps the others as alternatives of a
    SearchTreeStackEntry;
  \<^item> SearchTreeHandler::popSplit (267-401) removes entries without
    alternatives; for the next entry it pops the context, restores the saved
    bounds (Engine::postContextPopHook, Engine.cpp:2556-2570:
    BoundManager::restoreLocalBounds, BoundManager.cpp:232-239, and
    Tableau::updateVariablesToComplyWithBounds, Tableau.cpp:1703-1717),
    restores the engine state, which keeps the basis and the assignment, and
    applies the next alternative, repeating while the bounds are
    inconsistent. An empty stack means the query is unsat;
  \<^item> Engine::solve (Engine.cpp:196-461) runs the main loop: row tightening,
    a pending split, the bound check (an InfeasibleQueryException triggers
    popSplit), and then either the ReLU check at a point within bounds or one
    simplex step.
  The tableau matrix is shared by the whole search: only bounds are saved
  and restored. Everything is exact real arithmetic, not a proof about the
  C++ code.
\<close>

section \<open>Frames and search states\<close>

text \<open>
  A frame keeps the ReLU it split, the branch before the split, whose bounds,
  pending sets and conflict are what the native context restores, and the
  remaining alternatives. The head of the stack is the native _stack.back().
\<close>

record search_frame =
  frame_relu :: aux_relu
  frame_parent :: branch
  frame_alternatives :: "split_bounds list"

record search_state =
  search_branch :: branch
  search_basics :: "var list"
  search_nonbasics :: "var list"
  search_stack :: "search_frame list"

definition with_tableau :: "branch \<Rightarrow> tableau_state \<Rightarrow> branch" where
  "with_tableau Br T = Br\<lparr>branch_store := (branch_store Br)\<lparr>store_tableau := T\<rparr>\<rparr>"

section \<open>Restoring bounds\<close>

text \<open>
  Tableau::updateVariablesToComplyWithBounds: each nonbasic, in index order,
  complies with its lower and then its upper bound.
\<close>

fun comply_all :: "tableau_state \<Rightarrow> var list \<Rightarrow> tableau_state" where
  "comply_all S [] = S"
| "comply_all S (x # xs) =
     comply_all (comply Upper_Side (comply Lower_Side S x (tableau_lower S x)) x (tableau_upper S x)) xs"

text \<open>
  Backtracking to a frame: the current tableau (basis, rows and assignment)
  with the parent's bounds, pending sets and conflict status, and the
  parent's decisions.
\<close>

definition restore_branch :: "branch \<Rightarrow> tableau_state \<Rightarrow> var list \<Rightarrow> branch" where
  "restore_branch P T ns =
     (let Sp = store_tableau (branch_store P) in
      with_tableau P (comply_all (T\<lparr>tableau_lower := tableau_lower Sp, tableau_upper := tableau_upper Sp\<rparr>) ns))"

lemma comply_all_simps [simp]:
  "tableau_basics (comply_all S xs) = tableau_basics S"
  "tableau_nonbasics (comply_all S xs) = tableau_nonbasics S"
  "tableau_rows (comply_all S xs) = tableau_rows S"
  "tableau_lower (comply_all S xs) = tableau_lower S"
  "tableau_upper (comply_all S xs) = tableau_upper S"
  by (induction S xs rule: comply_all.induct) simp_all

lemma comply_rows_satisfied:
  assumes rows: "tableau_rows_satisfied S" and x: "x \<in> carrier S"
  shows "tableau_rows_satisfied (comply side S x v)"
proof (cases "x \<in> tableau_basics S")
  case True
  then show ?thesis using rows by (cases side) simp_all
next
  case False
  then have "x \<in> tableau_nonbasics S" using x by blast
  then show ?thesis using rows update_nonbasic_preserves_rows[OF _ rows] by (cases side) simp_all
qed

lemma comply_all_rows_satisfied:
  "tableau_rows_satisfied S \<Longrightarrow> set xs \<subseteq> carrier S \<Longrightarrow> tableau_rows_satisfied (comply_all S xs)"
proof (induction S xs rule: comply_all.induct)
  case (1 S)
  then show ?case by simp
next
  case (2 S x xs)
  let ?S1 = "comply Lower_Side S x (tableau_lower S x)"
  have r1: "tableau_rows_satisfied ?S1"
    using 2 by (intro comply_rows_satisfied) auto
  have r2: "tableau_rows_satisfied (comply Upper_Side ?S1 x (tableau_upper S x))"
    using 2 by (intro comply_rows_satisfied r1) auto
  have c: "set xs \<subseteq> carrier (comply Upper_Side ?S1 x (tableau_upper S x))"
    using 2 by simp
  show ?case using "2.IH"[OF r2 c] by (simp only: comply_all.simps)
qed

lemma comply_value_other:
  assumes "y \<noteq> x"
  shows "tableau_nonbasic_value (comply side S x v) y = tableau_nonbasic_value S y"
  using assms by (cases side) (auto simp: update_nonbasic_assignment_def)

lemma comply_both_within:
  assumes "tableau_lower S x \<le> tableau_upper S x" "x \<notin> tableau_basics S"
  defines "S2 \<equiv> comply Upper_Side (comply Lower_Side S x (tableau_lower S x)) x (tableau_upper S x)"
  shows "tableau_lower S x \<le> tableau_nonbasic_value S2 x \<and> tableau_nonbasic_value S2 x \<le> tableau_upper S x"
  using assms by (auto simp: update_nonbasic_assignment_def)

lemma comply_all_within:
  assumes "\<forall>y\<in>set xs. tableau_lower S y \<le> tableau_upper S y \<and> y \<notin> tableau_basics S"
  shows "\<forall>y\<in>set xs. tableau_lower S y \<le> tableau_nonbasic_value (comply_all S xs) y \<and>
                      tableau_nonbasic_value (comply_all S xs) y \<le> tableau_upper S y"
  using assms
proof (induction S xs rule: comply_all.induct)
  case (1 S)
  then show ?case by simp
next
  case (2 S x xs)
  let ?S2 = "comply Upper_Side (comply Lower_Side S x (tableau_lower S x)) x (tableau_upper S x)"
  have rest: "\<forall>y\<in>set xs. tableau_lower ?S2 y \<le> tableau_nonbasic_value (comply_all ?S2 xs) y \<and>
                          tableau_nonbasic_value (comply_all ?S2 xs) y \<le> tableau_upper ?S2 y"
    using 2 by (simp del: comply.simps)
  have kept: "tableau_nonbasic_value (comply_all T ys) x = tableau_nonbasic_value T x"
    if "x \<notin> set ys" for T ys
    using that
  proof (induction T ys rule: comply_all.induct)
    case (2 T y ys)
    then show ?case by (simp del: comply.simps add: comply_value_other)
  qed simp
  have x: "tableau_lower S x \<le> tableau_nonbasic_value ?S2 x \<and> tableau_nonbasic_value ?S2 x \<le> tableau_upper S x"
    using comply_both_within 2 by simp
  show ?case
  proof
    fix y
    assume y: "y \<in> set (x # xs)"
    show "tableau_lower S y \<le> tableau_nonbasic_value (comply_all S (x # xs)) y \<and>
          tableau_nonbasic_value (comply_all S (x # xs)) y \<le> tableau_upper S y"
    proof (cases "y \<in> set xs")
      case True
      then show ?thesis using rest by (simp del: comply.simps)
    next
      case False
      then have yx: "y = x" and nx: "x \<notin> set xs" using y by auto
      have "tableau_nonbasic_value (comply_all ?S2 xs) x = tableau_nonbasic_value ?S2 x"
        using kept[OF nx] .
      then show ?thesis using x yx by (simp del: comply.simps)
    qed
  qed
qed

section \<open>Sound branches\<close>

text \<open>
  A branch of the search is sound for the root S0 when it is a ReLU-aware
  branch, when its conflict records are sound and complete and, without a
  conflict, it satisfies the simplex invariant. It also has the root's
  equations and variables, and rows that hold for the assignment and lists
  that index the basis, whether or not a conflict is recorded.
\<close>

definition same_space :: "tableau_state \<Rightarrow> tableau_state \<Rightarrow> bool" where
  "same_space S0 S \<longleftrightarrow> tableau_models S = tableau_models S0 \<and> carrier S = carrier S0"

definition tableau_structure :: "tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "tableau_structure S bs ns \<longleftrightarrow>
     tableau_rows_supported S \<and> tableau_rows_satisfied S \<and> lists_match S bs ns"

definition branch_sound :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> branch \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "branch_sound S0 R Br bs ns \<longleftrightarrow>
     relu_branch_of S0 R Br \<and> branch_ok Br bs ns \<and>
     same_space S0 (store_tableau (branch_store Br)) \<and>
     tableau_structure (store_tableau (branch_store Br)) bs ns"

text \<open>What a frame keeps of its parent: the parts that do not depend on the basis.\<close>

definition frame_ok :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> branch \<Rightarrow> bool" where
  "frame_ok S0 R P \<longleftrightarrow>
     relu_branch_of S0 R P \<and> same_space S0 (store_tableau (branch_store P)) \<and>
     conflict_sound (branch_store P) \<and> conflict_complete (branch_store P)"

lemma branch_sound_frame_ok: "branch_sound S0 R Br bs ns \<Longrightarrow> frame_ok S0 R Br"
  unfolding branch_sound_def frame_ok_def branch_ok_def by blast

lemma models_cong:
  "tableau_basics T = tableau_basics S \<Longrightarrow> tableau_rows T = tableau_rows S \<Longrightarrow>
     tableau_models T = tableau_models S"
  by (simp add: tableau_models_def)

lemma bounded_models_space:
  "tableau_bounded_models S =
     {v \<in> tableau_models S. \<forall>x\<in>carrier S. tableau_lower S x \<le> v x \<and> v x \<le> tableau_upper S x}"
  by (simp add: tableau_bounded_models_def)

lemma conflict_cong:
  assumes "carrier (store_tableau B') = carrier (store_tableau B)"
      "tableau_lower (store_tableau B') = tableau_lower (store_tableau B)"
      "tableau_upper (store_tableau B') = tableau_upper (store_tableau B)"
      "first_conflict B' = first_conflict B"
  shows "conflict_sound B' = conflict_sound B" "conflict_complete B' = conflict_complete B"
proof -
  have cr: "crossed (store_tableau B') = crossed (store_tableau B)"
    using assms(2,3) by (simp add: crossed_def fun_eq_iff)
  show "conflict_sound B' = conflict_sound B"
    unfolding conflict_sound_def assms(1,4) cr by (rule refl)
  show "conflict_complete B' = conflict_complete B"
    unfolding conflict_complete_def assms(1,4) cr by (rule refl)
qed

lemma structure_invariant:
  "simplex_invariant S bs ns \<Longrightarrow> tableau_structure S bs ns"
  unfolding simplex_invariant_def tableau_structure_def lists_match_def by blast

lemma complete_ordered:
  "conflict_complete B \<Longrightarrow> first_conflict B = None \<Longrightarrow> tableau_bounds_ordered (store_tableau B)"
  unfolding conflict_complete_def tableau_bounds_ordered_def crossed_def by (auto simp: not_less)

section \<open>Bound application keeps branches sound\<close>

lemma tighten_kept:
  assumes x: "x \<in> carrier (store_tableau B)"
  shows "same_space S0 (store_tableau (fst (tighten_bound side x v B))) \<longleftrightarrow>
           same_space S0 (store_tableau B)"
    and "tableau_structure (store_tableau B) bs ns \<Longrightarrow>
           tableau_structure (store_tableau (fst (tighten_bound side x v B))) bs ns"
proof -
  have m: "tableau_models (store_tableau (fst (tighten_bound side x v B))) = tableau_models (store_tableau B)"
    by (rule models_cong) simp_all
  then show "same_space S0 (store_tableau (fst (tighten_bound side x v B))) \<longleftrightarrow>
               same_space S0 (store_tableau B)"
    by (simp add: same_space_def)
  assume st: "tableau_structure (store_tableau B) bs ns"
  have rows: "tableau_rows_satisfied (store_tableau (fst (tighten_bound side x v B)))"
  proof (cases "stronger side (store_tableau B) x v")
    case False
    then show ?thesis using st by (simp add: tighten_weaker tableau_structure_def)
  next
    case True
    have "tableau_rows_satisfied (with_bound side (store_tableau B) x v)"
      using st unfolding tableau_structure_def tableau_rows_satisfied_def by simp
    then show ?thesis
      using comply_rows_satisfied[of "with_bound side (store_tableau B) x v" x side v] x
        tighten_stronger(2)[OF True] by simp
  qed
  show "tableau_structure (store_tableau (fst (tighten_bound side x v B))) bs ns"
    using st rows unfolding tableau_structure_def tableau_rows_supported_def lists_match_def by simp
qed

lemma apply_split_kept:
  assumes "targets_in ts (store_tableau (branch_store Br))"
      "same_space S0 (store_tableau (branch_store Br))"
      "tableau_structure (store_tableau (branch_store Br)) bs ns"
  shows "same_space S0 (store_tableau (branch_store (apply_split ts Br))) \<and>
         tableau_structure (store_tableau (branch_store (apply_split ts Br))) bs ns"
  using assms
proof (induction ts Br rule: apply_split.induct)
  case (1 Br)
  then show ?case by simp
next
  case (2 side x v ts Br)
  have x: "x \<in> carrier (store_tableau (branch_store Br))"
    using "2.prems"(1) unfolding targets_in_def by auto
  let ?Br = "apply_decision side x v Br"
  have kept: "same_space S0 (store_tableau (branch_store ?Br))"
    "tableau_structure (store_tableau (branch_store ?Br)) bs ns"
    using tighten_kept(1)[OF x] tighten_kept(2)[OF x] "2.prems"(2,3)
    by (simp_all add: apply_decision_def)
  have "targets_in ts (store_tableau (branch_store ?Br))"
    using "2.prems"(1) unfolding targets_in_def by (auto simp: apply_decision_def)
  then show ?case using "2.IH"[OF _ kept] by simp
qed

theorem apply_split_sound:
  assumes "branch_sound S0 R Br bs ns" "targets_in ts (store_tableau (branch_store Br))"
  shows "branch_sound S0 R (apply_split ts Br) bs ns"
    and "branch_decisions (apply_split ts Br) = branch_decisions Br @ ts"
  using assms apply_split_relu_branch apply_split_ok apply_split_kept apply_split_decisions
  unfolding branch_sound_def by blast+

lemma apply_rules_kept:
  assumes "tableau_rows_supported (store_tableau (branch_store Br))"
      "same_space S0 (store_tableau (branch_store Br))"
      "tableau_structure (store_tableau (branch_store Br)) bs ns"
  shows "same_space S0 (store_tableau (branch_store (apply_rules rls Br))) \<and>
         tableau_structure (store_tableau (branch_store (apply_rules rls Br))) bs ns"
  using assms
proof (induction rls arbitrary: Br)
  case Nil
  then show ?case by simp
next
  case (Cons rl rls)
  let ?S = "store_tableau (branch_store Br)"
  show ?case
  proof (cases "rule_valid ?S rl")
    case False
    then show ?thesis using Cons by simp
  next
    case True
    obtain side x v where rb: "rule_bound ?S rl = (side, x, v)" by (cases "rule_bound ?S rl") auto
    have x: "x \<in> carrier ?S" using rule_target_in_carrier[OF Cons.prems(1) True rb] .
    let ?Br = "apply_derived side x v Br"
    have kept: "same_space S0 (store_tableau (branch_store ?Br))"
      "tableau_structure (store_tableau (branch_store ?Br)) bs ns"
      using tighten_kept(1)[OF x] tighten_kept(2)[OF x] Cons.prems(2,3)
      by (simp_all add: apply_derived_def)
    have sup: "tableau_rows_supported (store_tableau (branch_store ?Br))"
      using Cons.prems(1) unfolding tableau_rows_supported_def apply_derived_def by simp
    show ?thesis using Cons.IH[OF sup kept] True rb by simp
  qed
qed

theorem tighten_rows_sound:
  assumes "branch_sound S0 R Br bs ns"
  shows "branch_sound S0 R (tighten_rows bs Br) bs ns"
    and "branch_decisions (tighten_rows bs Br) = branch_decisions Br"
proof -
  have sup: "tableau_rows_supported (store_tableau (branch_store Br))"
    using assms unfolding branch_sound_def tableau_structure_def by blast
  have br: "relu_branch_of S0 R Br" and ok: "branch_ok Br bs ns"
    and sp: "same_space S0 (store_tableau (branch_store Br))"
    and st: "tableau_structure (store_tableau (branch_store Br)) bs ns"
    using assms unfolding branch_sound_def by auto
  note pres = apply_rules_preserves[OF br ok sup, of "all_row_rules (store_tableau (branch_store Br)) bs"]
  note kept = apply_rules_kept[OF sup sp st, of "all_row_rules (store_tableau (branch_store Br)) bs"]
  show "branch_sound S0 R (tighten_rows bs Br) bs ns"
    using pres kept unfolding branch_sound_def tighten_rows_def by blast
  show "branch_decisions (tighten_rows bs Br) = branch_decisions Br"
    using pres unfolding tighten_rows_def by blast
qed

text \<open>A sound branch with a recorded conflict has no ReLU-respecting solution.\<close>

lemma branch_sound_conflict:
  assumes "branch_sound S0 R Br bs ns" "first_conflict (branch_store Br) \<noteq> None"
  shows "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) = {}"
proof -
  have "tableau_bounded_models (store_tableau (branch_store Br)) = {}"
    using assms conflict_no_bounded_model unfolding branch_sound_def branch_ok_def by blast
  then show ?thesis using assms(1) unfolding branch_sound_def relu_branch_of_def by auto
qed

section \<open>Simplex runs keep branches sound\<close>

lemma apply_choice_frame:
  assumes sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
      and nb: "tableau_nonbasic_bounds_satisfied S" and ord: "tableau_bounds_ordered S"
      and e: "e \<in> tableau_nonbasics S" and adm: "choice_admissible S e d c"
  shows "tableau_models (apply_choice S e d c) = tableau_models S"
    and "carrier (apply_choice S e d c) = carrier S"
    and "tableau_lower (apply_choice S e d c) = tableau_lower S"
    and "tableau_upper (apply_choice S e d c) = tableau_upper S"
proof -
  show "tableau_models (apply_choice S e d c) = tableau_models S"
    using choice_invariants(3)[OF sup rows nb ord e adm] .
  show "tableau_lower (apply_choice S e d c) = tableau_lower S"
    "tableau_upper (apply_choice S e d c) = tableau_upper S"
    by (cases c; simp add: move_entering_def update_nonbasic_assignment_def exchange_basis_def)+
  show "carrier (apply_choice S e d c) = carrier S"
  proof (cases c)
    case (Bound_Flip \<tau>)
    then show ?thesis by (simp add: move_entering_def update_nonbasic_assignment_def)
  next
    case (Leaving b \<tau>)
    have "b \<in> tableau_basics S" using adm Leaving by simp
    then show ?thesis
      using e Leaving by (auto simp: move_entering_def update_nonbasic_assignment_def exchange_basis_def)
  qed
qed

lemma simplex_run_frame:
  "simplex_invariant S bs ns \<Longrightarrow> simplex_run n S bs ns = (r, S', bs', ns') \<Longrightarrow>
     tableau_models S' = tableau_models S \<and> carrier S' = carrier S \<and>
     tableau_lower S' = tableau_lower S \<and> tableau_upper S' = tableau_upper S"
proof (induction n arbitrary: S bs ns)
  case 0
  then show ?case by simp
next
  case (Suc n)
  have inv: "simplex_invariant S bs ns" and run: "simplex_run (Suc n) S bs ns = (r, S', bs', ns')"
    using Suc.prems by auto
  have sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
    and nb: "tableau_nonbasic_bounds_satisfied S" and ord: "tableau_bounds_ordered S"
    and sbs: "set bs = tableau_basics S" and sns: "set ns = tableau_nonbasics S"
    using inv unfolding simplex_invariant_def by auto
  show ?case
  proof (cases "all_between S bs")
    case True
    then show ?thesis using run by auto
  next
    case notall: False
    show ?thesis
    proof (cases "first_eligible S ns")
      case None
      then show ?thesis using run notall None by auto
    next
      case (Some ed)
      obtain e d where elig: "first_eligible S ns = Some (e, d)" using Some by (cases ed) auto
      have e: "e \<in> tableau_nonbasics S" and dir: "entering_direction S e = Some d"
        using first_eligible_some[OF elig] sns by auto
      have adm: "choice_admissible S e d (exact_harris_ratio_test S e d bs)"
        using exact_harris_admissible[OF sbs] entering_direction_range[OF dir] by simp
      note fr = apply_choice_frame[OF sup rows nb ord e adm]
      show ?thesis
      proof (cases "exact_harris_ratio_test S e d bs")
        case (Bound_Flip \<tau>)
        have run1: "simplex_run n (apply_choice S e d (Bound_Flip \<tau>)) bs ns = (r, S', bs', ns')"
          using run notall elig Bound_Flip by simp
        have inv1: "simplex_invariant (apply_choice S e d (Bound_Flip \<tau>)) bs ns"
          using simplex_step_invariant(2)[OF inv elig Bound_Flip] by simp
        show ?thesis using Suc.IH[OF inv1 run1] fr Bound_Flip by simp
      next
        case (Leaving b \<tau>)
        let ?bs1 = "bs[position bs b := e]" and ?ns1 = "ns[position ns e := b]"
        have run1: "simplex_run n (apply_choice S e d (Leaving b \<tau>)) ?bs1 ?ns1 = (r, S', bs', ns')"
          using run notall elig Leaving by simp
        have inv1: "simplex_invariant (apply_choice S e d (Leaving b \<tau>)) ?bs1 ?ns1"
          using simplex_step_invariant(3)[OF inv elig Leaving] by simp
        show ?thesis using Suc.IH[OF inv1 run1] fr Leaving by simp
      qed
    qed
  qed
qed

theorem simplex_run_branch_sound:
  assumes sound: "branch_sound S0 R Br bs ns" and none: "first_conflict (branch_store Br) = None"
      and run: "simplex_run n (store_tableau (branch_store Br)) bs ns = (r, T, bs', ns')"
  shows "branch_sound S0 R (with_tableau Br T) bs' ns'"
    and "branch_decisions (with_tableau Br T) = branch_decisions Br"
    and "tableau_bounded_models T = tableau_bounded_models (store_tableau (branch_store Br))"
    and "r = Feasible \<Longrightarrow> tableau_candidate T \<in> tableau_bounded_models (store_tableau (branch_store Br))"
    and "r = Infeasible \<Longrightarrow> tableau_bounded_models (store_tableau (branch_store Br)) = {}"
proof -
  let ?S = "store_tableau (branch_store Br)"
  have inv: "simplex_invariant ?S bs ns"
    using sound none unfolding branch_sound_def branch_ok_def by blast
  note rs = simplex_run_sound[OF inv run]
  note fr = simplex_run_frame[OF inv run]
  show "tableau_bounded_models T = tableau_bounded_models ?S"
    "r = Feasible \<Longrightarrow> tableau_candidate T \<in> tableau_bounded_models ?S"
    "r = Infeasible \<Longrightarrow> tableau_bounded_models ?S = {}"
    using rs by auto
  show "branch_decisions (with_tableau Br T) = branch_decisions Br"
    by (simp add: with_tableau_def)
  have cs: "conflict_sound (branch_store Br)" "conflict_complete (branch_store Br)"
    using sound unfolding branch_sound_def branch_ok_def by auto
  have cs': "conflict_sound (branch_store (with_tableau Br T))"
      "conflict_complete (branch_store (with_tableau Br T))"
    using conflict_cong[of "branch_store (with_tableau Br T)" "branch_store Br"] fr cs
    by (simp_all add: with_tableau_def)
  have rb: "relu_branch_of S0 R (with_tableau Br T)"
    using sound rs(1) unfolding branch_sound_def relu_branch_of_def by (simp add: with_tableau_def)
  have sp: "same_space S0 T"
    using sound fr unfolding branch_sound_def same_space_def by simp
  show "branch_sound S0 R (with_tableau Br T) bs' ns'"
    using rb cs' sp rs(2) structure_invariant[OF rs(2)]
    unfolding branch_sound_def branch_ok_def by (simp add: with_tableau_def)
qed

section \<open>Restoring a frame\<close>

theorem restore_branch_sound:
  assumes P: "frame_ok S0 R P" and sp: "same_space S0 T" and st: "tableau_structure T bs ns"
  shows "branch_sound S0 R (restore_branch P T ns) bs ns"
    and "branch_decisions (restore_branch P T ns) = branch_decisions P"
    and "tableau_lower (store_tableau (branch_store (restore_branch P T ns))) =
           tableau_lower (store_tableau (branch_store P))"
    and "tableau_upper (store_tableau (branch_store (restore_branch P T ns))) =
           tableau_upper (store_tableau (branch_store P))"
proof -
  let ?Sp = "store_tableau (branch_store P)"
  let ?T1 = "T\<lparr>tableau_lower := tableau_lower ?Sp, tableau_upper := tableau_upper ?Sp\<rparr>"
  let ?T2 = "comply_all ?T1 ns"
  let ?Br = "restore_branch P T ns"
  have Br: "?Br = with_tableau P ?T2" by (simp add: restore_branch_def Let_def)
  show dec: "branch_decisions ?Br = branch_decisions P" by (simp add: Br with_tableau_def)
  show "tableau_lower (store_tableau (branch_store ?Br)) = tableau_lower ?Sp"
    "tableau_upper (store_tableau (branch_store ?Br)) = tableau_upper ?Sp"
    by (simp_all add: Br with_tableau_def)
  have rb: "relu_branch_of S0 R P" and spP: "same_space S0 ?Sp"
    and cs: "conflict_sound (branch_store P)" and cc: "conflict_complete (branch_store P)"
    using P unfolding frame_ok_def by auto
  have models: "tableau_models ?T2 = tableau_models ?Sp"
    using sp spP models_cong[of ?T2 T] unfolding same_space_def by simp
  have carrier: "carrier ?T2 = carrier ?Sp"
    using sp spP unfolding same_space_def by simp
  have bounded: "tableau_bounded_models ?T2 = tableau_bounded_models ?Sp"
    using models carrier by (simp add: bounded_models_space)
  have rb': "relu_branch_of S0 R ?Br"
    using rb bounded dec unfolding relu_branch_of_def by (simp add: Br with_tableau_def)
  have cs': "conflict_sound (branch_store ?Br)" "conflict_complete (branch_store ?Br)"
    using conflict_cong[of "branch_store ?Br" "branch_store P"] carrier cs cc
    by (simp_all add: Br with_tableau_def)
  have sup: "tableau_rows_supported ?T2" and lists: "lists_match ?T2 bs ns"
    using st unfolding tableau_structure_def tableau_rows_supported_def lists_match_def by simp_all
  have ns: "set ns = tableau_nonbasics T"
    using st unfolding tableau_structure_def lists_match_def by blast
  have rows: "tableau_rows_satisfied ?T2"
  proof (rule comply_all_rows_satisfied)
    show "tableau_rows_satisfied ?T1"
      using st unfolding tableau_structure_def tableau_rows_satisfied_def by simp
    show "set ns \<subseteq> carrier ?T1" using ns by simp
  qed
  have sp': "same_space S0 ?T2"
    using sp models_cong[of ?T2 T] unfolding same_space_def by simp
  have inv: "simplex_invariant ?T2 bs ns" if none: "first_conflict (branch_store P) = None"
  proof -
    have ord: "tableau_bounds_ordered ?Sp" using complete_ordered[OF cc none] .
    have ord2: "tableau_bounds_ordered ?T2"
      using ord carrier unfolding tableau_bounds_ordered_def by simp
    have disj: "tableau_basics T \<inter> tableau_nonbasics T = {}"
      using st unfolding tableau_structure_def tableau_rows_supported_def by blast
    have "\<forall>y\<in>set ns. tableau_lower ?T1 y \<le> tableau_upper ?T1 y \<and> y \<notin> tableau_basics ?T1"
      using ord2 ns disj unfolding tableau_bounds_ordered_def by auto
    then have "\<forall>y\<in>set ns. tableau_lower ?T1 y \<le> tableau_nonbasic_value ?T2 y \<and>
                            tableau_nonbasic_value ?T2 y \<le> tableau_upper ?T1 y"
      by (rule comply_all_within)
    then have nb: "tableau_nonbasic_bounds_satisfied ?T2"
      using ns unfolding tableau_nonbasic_bounds_satisfied_def by simp
    show ?thesis
      using sup rows nb ord2 lists unfolding simplex_invariant_def lists_match_def by blast
  qed
  show "branch_sound S0 R ?Br bs ns"
    using rb' cs' inv sp' sup rows lists
    unfolding branch_sound_def branch_ok_def tableau_structure_def
    by (simp add: Br with_tableau_def)
qed

section \<open>Pushing and popping frames\<close>

text \<open>
  performSplit: the first case split is applied, the rest stay on the frame.
  getCaseSplits always returns two.
\<close>

definition perform_split :: "aux_relu \<Rightarrow> branch \<Rightarrow> search_frame list \<Rightarrow> branch \<times> search_frame list" where
  "perform_split r Br stk =
     (case case_splits (store_tableau (branch_store Br)) r of
        [] \<Rightarrow> (Br, stk)
      | c # cs \<Rightarrow> (apply_split c Br, \<lparr>frame_relu = r, frame_parent = Br, frame_alternatives = cs\<rparr> # stk))"

text \<open>
  popSplit: frames without alternatives are dropped; the next frame's
  parent bounds are restored onto the current tableau and its next
  alternative is applied. When that alternative's bounds are inconsistent,
  native popSplit pops again at once; here the next iteration of the main
  loop does, with the same stack.
\<close>

fun pop_split :: "tableau_state \<Rightarrow> var list \<Rightarrow> search_frame list \<Rightarrow> (branch \<times> search_frame list) option" where
  "pop_split T ns [] = None"
| "pop_split T ns (f # fs) =
     (case frame_alternatives f of
        [] \<Rightarrow> pop_split T ns fs
      | c # cs \<Rightarrow> Some (apply_split c (restore_branch (frame_parent f) T ns),
                        f\<lparr>frame_alternatives := cs\<rparr> # fs))"

definition pending_models :: "search_frame list \<Rightarrow> valuation set" where
  "pending_models stk =
     (\<Union>f\<in>set stk. \<Union>c\<in>set (frame_alternatives f). decision_models (branch_decisions (frame_parent f) @ c))"

definition frames_ok :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> search_frame list \<Rightarrow> bool" where
  "frames_ok S0 R stk \<longleftrightarrow>
     (\<forall>f\<in>set stk. frame_ok S0 R (frame_parent f) \<and> (\<forall>c\<in>set (frame_alternatives f). targets_in c S0))"

lemma pending_models_simps [simp]:
  "pending_models [] = {}"
  "pending_models (f # fs) =
     (\<Union>c\<in>set (frame_alternatives f). decision_models (branch_decisions (frame_parent f) @ c)) \<union>
     pending_models fs"
  by (auto simp: pending_models_def)

lemma frames_ok_simps [simp]:
  "frames_ok S0 R []"
  "frames_ok S0 R (f # fs) \<longleftrightarrow>
     frame_ok S0 R (frame_parent f) \<and> (\<forall>c\<in>set (frame_alternatives f). targets_in c S0) \<and>
     frames_ok S0 R fs"
  by (auto simp: frames_ok_def)

lemma targets_in_space:
  "same_space S0 S \<Longrightarrow> targets_in ts S \<longleftrightarrow> targets_in ts S0"
  unfolding same_space_def targets_in_def by simp

lemma pop_split_sound_all:
  assumes sp: "same_space S0 T" and st: "tableau_structure T bs ns"
  shows "frames_ok S0 R stk \<Longrightarrow>
    (case pop_split T ns stk of
       None \<Rightarrow> pending_models stk = {}
     | Some (Br, stk') \<Rightarrow>
         branch_sound S0 R Br bs ns \<and> frames_ok S0 R stk' \<and>
         decision_models (branch_decisions Br) \<union> pending_models stk' = pending_models stk)"
proof (induction stk)
  case Nil
  then show ?case by simp
next
  case (Cons f fs)
  have fok: "frame_ok S0 R (frame_parent f)" and alts: "\<forall>c\<in>set (frame_alternatives f). targets_in c S0"
    and rest: "frames_ok S0 R fs"
    using Cons.prems by auto
  show ?case
  proof (cases "frame_alternatives f")
    case Nil
    show ?thesis
    proof (cases "pop_split T ns fs")
      case None
      then show ?thesis using Cons.IH[OF rest] Nil by simp
    next
      case (Some p)
      then show ?thesis using Cons.IH[OF rest] Nil by (cases p) simp
    qed
  next
    case alt: (Cons c cs)
    let ?P = "restore_branch (frame_parent f) T ns"
    note rs = restore_branch_sound[OF fok sp st]
    have sp': "same_space S0 (store_tableau (branch_store ?P))"
      using rs(1) unfolding branch_sound_def by blast
    have tgt: "targets_in c (store_tableau (branch_store ?P))"
      using alts alt targets_in_space[OF sp'] by simp
    note sound = apply_split_sound[OF rs(1) tgt]
    have dm: "decision_models (branch_decisions (apply_split c ?P)) =
                decision_models (branch_decisions (frame_parent f) @ c)"
      using sound(2) rs(2) by simp
    have "frames_ok S0 R (f\<lparr>frame_alternatives := cs\<rparr> # fs)"
      using fok alts alt rest by simp
    then show ?thesis
      using sound(1) dm alt by auto
  qed
qed

theorem pop_split_sound:
  assumes frames: "frames_ok S0 R stk" and sp: "same_space S0 T" and st: "tableau_structure T bs ns"
  shows "pop_split T ns stk = None \<Longrightarrow> pending_models stk = {}"
    and "pop_split T ns stk = Some (Br, stk') \<Longrightarrow>
           branch_sound S0 R Br bs ns \<and> frames_ok S0 R stk' \<and>
           decision_models (branch_decisions Br) \<union> pending_models stk' = pending_models stk"
proof -
  note pop_all = pop_split_sound_all[OF sp st frames]
  show "pending_models stk = {}" if a: "pop_split T ns stk = None"
    using pop_all by (simp add: a)
  show "branch_sound S0 R Br bs ns \<and> frames_ok S0 R stk' \<and>
          decision_models (branch_decisions Br) \<union> pending_models stk' = pending_models stk"
    if a: "pop_split T ns stk = Some (Br, stk')"
    using pop_all by (simp add: a)
qed

theorem perform_split_sound:
  assumes sound: "branch_sound S0 R Br bs ns" and frames: "frames_ok S0 R stk"
      and aux: "aux_form S0 r" and r: "r \<in> set R"
      and vars: "relu_b r \<in> carrier S0" "relu_f r \<in> carrier S0" "relu_aux r \<in> carrier S0"
      and split: "perform_split r Br stk = (Br', stk')"
  shows "branch_sound S0 R Br' bs ns" and "frames_ok S0 R stk'"
    and "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) \<subseteq>
           decision_models (branch_decisions Br') \<union> pending_models stk'"
    and "pending_models stk \<subseteq> pending_models stk'"
proof -
  let ?S = "store_tableau (branch_store Br)"
  have sp: "same_space S0 ?S" using sound unfolding branch_sound_def by blast
  have tgt: "targets_in ts S0" if "ts \<in> {native_inactive_split r, native_active_split r}" for ts
    using that vars unfolding targets_in_def by (auto simp: native_inactive_split_def native_active_split_def)
  define c1 where "c1 = hd (case_splits ?S r)"
  define c2 where "c2 = hd (tl (case_splits ?S r))"
  have cs: "case_splits ?S r = [c1, c2]"
    unfolding c1_def c2_def case_splits_def by simp
  have set12: "{c1, c2} = {native_inactive_split r, native_active_split r}"
    unfolding c1_def c2_def case_splits_def by (simp add: insert_commute)
  have Br': "Br' = apply_split c1 Br" and stk': "stk' = \<lparr>frame_relu = r, frame_parent = Br, frame_alternatives = [c2]\<rparr> # stk"
    using split cs unfolding perform_split_def by auto
  have c12: "c1 \<in> {native_inactive_split r, native_active_split r}"
      "c2 \<in> {native_inactive_split r, native_active_split r}"
    using set12 by blast+
  have t1: "targets_in c1 ?S" and t2: "targets_in c2 S0"
    using tgt[OF c12(1)] tgt[OF c12(2)] targets_in_space[OF sp] by auto
  note child = apply_split_sound[OF sound t1]
  show "branch_sound S0 R Br' bs ns" using child(1) Br' by simp
  show "frames_ok S0 R stk'" using stk' frames branch_sound_frame_ok[OF sound] t2 by simp
  show "pending_models stk \<subseteq> pending_models stk'" using stk' by auto
  show "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) \<subseteq>
          decision_models (branch_decisions Br') \<union> pending_models stk'"
  proof
    fix w
    assume w: "w \<in> tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br)"
    have "relu_holds r w" using w r unfolding relu_solutions_def by blast
    then have "w \<in> decision_models (native_inactive_split r) \<or> w \<in> decision_models (native_active_split r)"
      using relu_split_covers[of w S0 r] w aux by blast
    then have "\<exists>c\<in>{c1, c2}. w \<in> decision_models c" unfolding set12 by blast
    then have "w \<in> decision_models c1 \<or> w \<in> decision_models c2" by blast
    then show "w \<in> decision_models (branch_decisions Br') \<union> pending_models stk'"
      using w child(2) Br' stk' by (auto simp: decision_models_append)
  qed
qed

section \<open>The main loop\<close>

text \<open>
  The configuration of the relu_split capture: native LP, DeepSoI off,
  ReLUViolation branching and a constraint violation threshold of 1. Then
  chooseViolatedConstraintForFixing (USE_LEAST_FIX is false) picks the first
  active violated ReLU, and the next iteration splits it. A ReLU split on
  the current path is disabled, so it is not picked again.
\<close>

definition pick_split :: "aux_relu list \<Rightarrow> search_frame list \<Rightarrow> valuation \<Rightarrow> aux_relu option" where
  "pick_split R stk v = find (\<lambda>r. r \<notin> set (map frame_relu stk) \<and> \<not> relu_holds r v) R"

lemma pick_split_in: "pick_split R stk v = Some r \<Longrightarrow> r \<in> set R"
  unfolding pick_split_def by (auto simp: find_Some_iff)

datatype step_outcome =
    Step_Sat valuation
  | Step_Unknown
  | Step_Next search_state
  | Step_Refuted tableau_state "var list" "var list"

text \<open>
  One iteration. A branch with a recorded conflict, a conflict found by row
  tightening, or an Infeasible simplex run is refuted, and the loop pops. A
  run that stops for lack of fuel continues with the next iteration, so with
  fuel sf = 1 each iteration makes one simplex step after row tightening, as
  native does. At a point within bounds the query's ReLUs are checked: if all
  hold, the point is a solution; otherwise the first violated unsplit ReLU is
  split.
\<close>

definition search_step :: "nat \<Rightarrow> query \<Rightarrow> aux_relu list \<Rightarrow> search_state \<Rightarrow> step_outcome" where
  "search_step sf Q R st =
     (let Br0 = search_branch st; bs = search_basics st; ns = search_nonbasics st in
      if first_conflict (branch_store Br0) \<noteq> None then Step_Refuted (store_tableau (branch_store Br0)) bs ns
      else let Br = tighten_rows bs Br0 in
      if first_conflict (branch_store Br) \<noteq> None then Step_Refuted (store_tableau (branch_store Br)) bs ns
      else (case simplex_run sf (store_tableau (branch_store Br)) bs ns of
              (Infeasible, T, bs', ns') \<Rightarrow> Step_Refuted T bs' ns'
            | (Out_Of_Fuel, T, bs', ns') \<Rightarrow>
                Step_Next (st\<lparr>search_branch := with_tableau Br T, search_basics := bs',
                              search_nonbasics := ns'\<rparr>)
            | (Feasible, T, bs', ns') \<Rightarrow>
                (let v = tableau_candidate T in
                 if list_all (satisfies_relu_constraint v) (relu_atoms Q) then Step_Sat v
                 else (case pick_split R (search_stack st) v of
                         None \<Rightarrow> Step_Unknown
                       | Some r \<Rightarrow>
                           (case perform_split r (with_tableau Br T) (search_stack st) of
                              (Br', stk') \<Rightarrow>
                                Step_Next \<lparr>search_branch = Br', search_basics = bs',
                                           search_nonbasics = ns', search_stack = stk'\<rparr>)))))"

datatype search_result =
    is_search_sat: Search_Sat valuation
  | is_search_unsat: Search_Unsat
  | is_search_unknown: Search_Unknown

text \<open>A satisfiable result holds a function, so results are tested by discriminator.\<close>

lemma is_search_unsat_iff: "is_search_unsat r \<longleftrightarrow> r = Search_Unsat"
  by (cases r) simp_all

lemma is_search_sat_iff: "is_search_sat r \<longleftrightarrow> (\<exists>v. r = Search_Sat v)"
  by (cases r) simp_all

fun search_loop :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> aux_relu list \<Rightarrow> search_state \<Rightarrow> search_result" where
  "search_loop 0 sf Q R st = Search_Unknown"
| "search_loop (Suc k) sf Q R st =
     (case search_step sf Q R st of
        Step_Sat v \<Rightarrow> Search_Sat v
      | Step_Unknown \<Rightarrow> Search_Unknown
      | Step_Next st' \<Rightarrow> search_loop k sf Q R st'
      | Step_Refuted T bs ns \<Rightarrow>
          (case pop_split T ns (search_stack st) of
             None \<Rightarrow> Search_Unsat
           | Some (Br, stk) \<Rightarrow>
               search_loop k sf Q R \<lparr>search_branch = Br, search_basics = bs,
                                    search_nonbasics = ns, search_stack = stk\<rparr>))"

section \<open>Soundness of the search\<close>

text \<open>
  The search invariant: the current branch and every frame are sound, and
  every ReLU-respecting root solution lies in the current branch or in a
  pending alternative (coverage).
\<close>

definition search_inv :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> search_state \<Rightarrow> bool" where
  "search_inv S0 R st \<longleftrightarrow>
     branch_sound S0 R (search_branch st) (search_basics st) (search_nonbasics st) \<and>
     frames_ok S0 R (search_stack st) \<and>
     tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq>
       decision_models (branch_decisions (search_branch st)) \<union> pending_models (search_stack st)"

definition relus_ok :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> bool" where
  "relus_ok S0 R \<longleftrightarrow>
     (\<forall>r\<in>set R. aux_form S0 r \<and> relu_b r \<in> carrier S0 \<and> relu_f r \<in> carrier S0 \<and> relu_aux r \<in> carrier S0)"

definition initial_search :: "tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> search_state" where
  "initial_search S bs ns =
     \<lparr>search_branch = root_branch S, search_basics = bs, search_nonbasics = ns, search_stack = []\<rparr>"

theorem initial_search_inv:
  assumes "simplex_invariant S bs ns"
  shows "search_inv S R (initial_search S bs ns)"
proof -
  have rb: "relu_branch_of S R (root_branch S)" by (rule branch_of_relu[OF root_branch_of])
  have "branch_sound S R (root_branch S) bs ns"
    using rb root_branch_ok[OF assms] structure_invariant[OF assms]
    unfolding branch_sound_def by (simp add: root_branch_def same_space_def)
  then show ?thesis
    unfolding search_inv_def initial_search_def by (simp add: root_branch_def decision_models_def)
qed

lemma relus_hold:
  assumes "\<forall>r\<in>set R. ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
      and "list_all (satisfies_relu_constraint v) (relu_atoms Q)"
  shows "v \<in> relu_solutions R"
  using assms unfolding relu_solutions_def relu_holds_def list_all_iff by fastforce

theorem search_step_sound:
  assumes inv: "search_inv S0 R st" and relus: "relus_ok S0 R"
      and inQ: "\<forall>r\<in>set R. ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
  shows "search_step sf Q R st = Step_Sat v \<Longrightarrow>
           v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)"
    and "search_step sf Q R st = Step_Next st' \<Longrightarrow> search_inv S0 R st'"
    and "search_step sf Q R st = Step_Refuted T bs ns \<Longrightarrow>
           same_space S0 T \<and> tableau_structure T bs ns \<and>
           tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq> pending_models (search_stack st)"
proof -
  let ?cur = "search_branch st" and ?bs = "search_basics st" and ?ns = "search_nonbasics st"
  let ?stk = "search_stack st"
  let ?tb = "tighten_rows ?bs ?cur"
  let ?S = "store_tableau (branch_store ?tb)"
  have s0: "branch_sound S0 R ?cur ?bs ?ns" and frames: "frames_ok S0 R ?stk"
    and cover: "tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq>
                  decision_models (branch_decisions ?cur) \<union> pending_models ?stk"
    using inv unfolding search_inv_def by auto
  note tr = tighten_rows_sound[OF s0]
  have refuted_cover: "tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq> pending_models ?stk"
    if "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions ?cur) = {}"
    using that cover by blast
  have space_of: "same_space S0 (store_tableau (branch_store B)) \<and>
                  tableau_structure (store_tableau (branch_store B)) bs' ns'"
    if "branch_sound S0 R B bs' ns'" for B bs' ns'
    using that unfolding branch_sound_def by blast
  have main: "case search_step sf Q R st of
       Step_Sat v \<Rightarrow> v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)
     | Step_Unknown \<Rightarrow> True
     | Step_Next st' \<Rightarrow> search_inv S0 R st'
     | Step_Refuted T bs ns \<Rightarrow> same_space S0 T \<and> tableau_structure T bs ns \<and>
         tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq> pending_models ?stk"
  proof (cases "first_conflict (branch_store ?cur) = None")
    case False
    then have step: "search_step sf Q R st = Step_Refuted (store_tableau (branch_store ?cur)) ?bs ?ns"
      by (simp add: search_step_def Let_def)
    show ?thesis
      using step space_of[OF s0] refuted_cover[OF branch_sound_conflict[OF s0 False]] by simp
  next
    case none0: True
    show ?thesis
    proof (cases "first_conflict (branch_store ?tb) = None")
      case False
      then have step: "search_step sf Q R st = Step_Refuted ?S ?bs ?ns"
        using none0 by (simp add: search_step_def Let_def)
      have "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions ?cur) = {}"
        using branch_sound_conflict[OF tr(1) False] tr(2) by simp
      then show ?thesis
        using step space_of[OF tr(1)] refuted_cover by simp
    next
      case none1: True
      obtain r T' bs' ns' where sr: "simplex_run sf ?S ?bs ?ns = (r, T', bs', ns')"
        by (cases "simplex_run sf ?S ?bs ?ns") auto
      note sb = simplex_run_branch_sound[OF tr(1) none1 sr]
      have dec: "branch_decisions (with_tableau ?tb T') = branch_decisions ?cur"
        using sb(2) tr(2) by simp
      show ?thesis
      proof (cases r)
        case Infeasible
        then have step: "search_step sf Q R st = Step_Refuted T' bs' ns'"
          using none0 none1 sr by (simp add: search_step_def Let_def)
        have "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions ?cur) = {}"
          using sb(5)[OF Infeasible] tr(1,2) unfolding branch_sound_def relu_branch_of_def by auto
        then show ?thesis
          using step space_of[OF sb(1)] refuted_cover by (simp add: with_tableau_def)
      next
        case Out_Of_Fuel
        then have step: "search_step sf Q R st =
            Step_Next (st\<lparr>search_branch := with_tableau ?tb T', search_basics := bs',
                          search_nonbasics := ns'\<rparr>)"
          using none0 none1 sr by (simp add: search_step_def Let_def)
        have "search_inv S0 R (st\<lparr>search_branch := with_tableau ?tb T', search_basics := bs',
                                 search_nonbasics := ns'\<rparr>)"
          using sb(1) frames cover dec unfolding search_inv_def by simp
        then show ?thesis using step by simp
      next
        case Feasible
        let ?v = "tableau_candidate T'"
        let ?B1 = "with_tableau ?tb T'"
        have step: "search_step sf Q R st =
            (if list_all (satisfies_relu_constraint ?v) (relu_atoms Q) then Step_Sat ?v
             else (case pick_split R ?stk ?v of
                     None \<Rightarrow> Step_Unknown
                   | Some r \<Rightarrow>
                       (case perform_split r ?B1 ?stk of
                          (Br', stk') \<Rightarrow>
                            Step_Next \<lparr>search_branch = Br', search_basics = bs',
                                       search_nonbasics = ns', search_stack = stk'\<rparr>)))"
          using none0 none1 sr Feasible by (simp add: search_step_def Let_def)
        show ?thesis
        proof (cases "list_all (satisfies_relu_constraint ?v) (relu_atoms Q)")
          case hold: True
          have "?v \<in> relu_solutions R" using relus_hold[OF inQ hold] .
          then have "?v \<in> tableau_bounded_models ?S \<inter> relu_solutions R" using sb(4)[OF Feasible] by blast
          then have "?v \<in> tableau_bounded_models S0"
            using tr(1) unfolding branch_sound_def relu_branch_of_def by blast
          then show ?thesis using step hold by simp
        next
          case violated: False
          show ?thesis
          proof (cases "pick_split R ?stk ?v")
            case None
            then show ?thesis using step violated by simp
          next
            case (Some r')
            obtain Br' stk' where ps: "perform_split r' ?B1 ?stk = (Br', stk')"
              by (cases "perform_split r' ?B1 ?stk")
            have r': "r' \<in> set R" using pick_split_in[OF Some] .
            have aux: "aux_form S0 r'" and vars: "relu_b r' \<in> carrier S0" "relu_f r' \<in> carrier S0"
              "relu_aux r' \<in> carrier S0"
              using relus r' unfolding relus_ok_def by auto
            note ps_sound = perform_split_sound[OF sb(1) frames aux r' vars ps]
            have "tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq>
                    decision_models (branch_decisions Br') \<union> pending_models stk'"
              using cover ps_sound(3,4) unfolding dec by blast
            then have "search_inv S0 R \<lparr>search_branch = Br', search_basics = bs',
                         search_nonbasics = ns', search_stack = stk'\<rparr>"
              using ps_sound(1,2) unfolding search_inv_def by simp
            then show ?thesis using step violated Some ps by simp
          qed
        qed
      qed
    qed
  qed
  show "v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)"
    if a: "search_step sf Q R st = Step_Sat v"
    using main by (simp add: a)
  show "search_inv S0 R st'" if a: "search_step sf Q R st = Step_Next st'"
    using main by (simp add: a)
  show "same_space S0 T \<and> tableau_structure T bs ns \<and>
          tableau_bounded_models S0 \<inter> relu_solutions R \<subseteq> pending_models (search_stack st)"
    if a: "search_step sf Q R st = Step_Refuted T bs ns"
    using main by (simp add: a)
qed

lemma search_loop_sound_all:
  assumes relus: "relus_ok S0 R"
      and inQ: "\<forall>r\<in>set R. ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
  shows "search_inv S0 R st \<Longrightarrow>
    (case search_loop k sf Q R st of
       Search_Sat v \<Rightarrow> v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)
     | Search_Unsat \<Rightarrow> tableau_bounded_models S0 \<inter> relu_solutions R = {}
     | Search_Unknown \<Rightarrow> True)"
proof (induction k arbitrary: st)
  case 0
  then show ?case by simp
next
  case (Suc k)
  note step = search_step_sound[OF Suc.prems relus inQ]
  have frames: "frames_ok S0 R (search_stack st)" using Suc.prems unfolding search_inv_def by blast
  show ?case
  proof (cases "search_step sf Q R st")
    case (Step_Sat v)
    then show ?thesis using step(1)[OF Step_Sat] by simp
  next
    case Step_Unknown
    then show ?thesis by simp
  next
    case (Step_Next st')
    then show ?thesis using Suc.IH[OF step(2)[OF Step_Next]] by simp
  next
    case (Step_Refuted T bs ns)
    note rf = step(3)[OF Step_Refuted]
    show ?thesis
    proof (cases "pop_split T ns (search_stack st)")
      case None
      have "pending_models (search_stack st) = {}"
        using pop_split_sound(1)[OF frames _ _ None] rf by blast
      then show ?thesis using Step_Refuted None rf by auto
    next
      case (Some p)
      obtain Br stk where p: "p = (Br, stk)" by (cases p)
      have ps: "branch_sound S0 R Br bs ns \<and> frames_ok S0 R stk \<and>
                  decision_models (branch_decisions Br) \<union> pending_models stk = pending_models (search_stack st)"
        using pop_split_sound(2)[OF frames _ _ Some[unfolded p]] rf by blast
      have "search_inv S0 R \<lparr>search_branch = Br, search_basics = bs, search_nonbasics = ns, search_stack = stk\<rparr>"
        using ps rf unfolding search_inv_def by auto
      then show ?thesis using Suc.IH Step_Refuted Some p by simp
    qed
  qed
qed

theorem search_loop_sound:
  assumes inv: "search_inv S0 R st" and relus: "relus_ok S0 R"
      and inQ: "\<forall>r\<in>set R. ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
  shows "search_loop k sf Q R st = Search_Sat v \<Longrightarrow>
           v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)"
    and "search_loop k sf Q R st = Search_Unsat \<Longrightarrow> tableau_bounded_models S0 \<inter> relu_solutions R = {}"
proof -
  note loop_all = search_loop_sound_all[OF relus inQ inv, where k = k and sf = sf]
  show "v \<in> tableau_bounded_models S0 \<and> list_all (satisfies_relu_constraint v) (relu_atoms Q)"
    if a: "search_loop k sf Q R st = Search_Sat v"
    using loop_all by (simp add: a)
  show "tableau_bounded_models S0 \<inter> relu_solutions R = {}" if a: "search_loop k sf Q R st = Search_Unsat"
    using loop_all by (simp add: a)
qed

section \<open>Queries\<close>

text \<open>
  The ReLUs of a query in native auxiliary form: for each ReLU atom, the
  first variable of an equation that makes it an auxiliary in the sense of
  relu_in_aux_form. ReLUs without one are not split; if one of them is
  violated at a point within bounds, the search reports Unknown.
\<close>

definition aux_candidates :: "query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> aux_relu list" where
  "aux_candidates Q b f =
     map (\<lambda>x. \<lparr>relu_b = b, relu_f = f, relu_aux = x\<rparr>) (concat (map (\<lambda>c. map snd (aux_terms c)) (linear_atoms Q)))"

definition query_aux_relus :: "nat \<Rightarrow> query \<Rightarrow> aux_relu list" where
  "query_aux_relus n Q =
     List.map_filter (\<lambda>a. case a of ReLU b f \<Rightarrow> find (relu_in_aux_form n Q) (aux_candidates Q b f))
       (relu_atoms Q)"

lemma query_aux_relus_form:
  assumes "r \<in> set (query_aux_relus n Q)"
  shows "relu_in_aux_form n Q r"
proof -
  obtain a where some: "(case a of ReLU b f \<Rightarrow> find (relu_in_aux_form n Q) (aux_candidates Q b f)) = Some r"
    using assms unfolding query_aux_relus_def List.map_filter_def by (auto simp: not_None_eq)
  obtain b f where "a = ReLU b f" by (cases a)
  then have "find (relu_in_aux_form n Q) (aux_candidates Q b f) = Some r" using some by simp
  then show ?thesis by (auto simp: find_Some_iff)
qed

lemma relus_root_empty_unsat:
  assumes ready: "engine_ready n Q" and form: "\<forall>r\<in>set R. relu_in_aux_form n Q r"
      and empty: "tableau_bounded_models (initial_tableau n Q) \<inter> relu_solutions R = {}"
  shows "unsatisfiable Q"
  unfolding unsatisfiable_def satisfiable_def
proof
  assume "\<exists>v. satisfies_query v Q"
  then obtain v where v: "satisfies_query v Q" by blast
  let ?w = "extend_aux n Q v"
  have "?w \<in> tableau_bounded_models (initial_tableau n Q)"
    using query_model_extends[OF ready] v unfolding satisfies_query_def by blast
  moreover have "?w \<in> relu_solutions R"
    unfolding relu_solutions_def
  proof (intro CollectI ballI)
    fix r
    assume r: "r \<in> set R"
    have lt: "relu_b r < n" "relu_f r < n" and atom: "ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
      using form r unfolding relu_in_aux_form_def by auto
    have "satisfies_relu v (relu_b r) (relu_f r)"
      using v atom unfolding satisfies_query_def by fastforce
    then show "relu_holds r ?w" using lt by (simp add: relu_holds_def satisfies_relu_def extend_aux_def)
  qed
  ultimately show False using empty by blast
qed

lemma native_initial_carrier:
  assumes "native_initial_tableau n Q = Some (S, bs, ns)" "x < n + length (linear_atoms Q)"
  shows "x \<in> carrier S"
proof -
  obtain S1 where S: "S = reset_assignment S1" and m: "lists_match S1 bs ns"
    and ns: "ns = filter (\<lambda>x. x \<notin> set bs) [0..<n + length (linear_atoms Q)]"
    using assms(1) by (auto simp: native_initial_tableau_def Let_def split: option.splits if_splits)
  have "x \<in> set bs \<or> x \<in> set ns" using ns assms(2) by auto
  then show ?thesis using m S unfolding lists_match_def by auto
qed

text \<open>
  A start for the search: a tableau with the simplex invariant whose bounded
  solutions are those of the query's starting tableau, and which contains
  the query's variables.
\<close>

definition search_start :: "nat \<Rightarrow> query \<Rightarrow> tableau_state \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "search_start n Q S bs ns \<longleftrightarrow>
     simplex_invariant S bs ns \<and>
     tableau_bounded_models S = tableau_bounded_models (initial_tableau n Q) \<and>
     (\<forall>x<n. x \<in> carrier S)"

lemma search_start_facts:
  assumes ready: "engine_ready n Q" and start: "search_start n Q S bs ns"
  shows "search_inv S R (initial_search S bs ns)"
    and "relus_ok S (query_aux_relus n Q)"
    and "\<forall>r\<in>set (query_aux_relus n Q). ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
proof -
  have inv: "simplex_invariant S bs ns"
    and bm: "tableau_bounded_models S = tableau_bounded_models (initial_tableau n Q)"
    and vars: "\<forall>x<n. x \<in> carrier S"
    using start unfolding search_start_def by auto
  show "search_inv S R (initial_search S bs ns)" using initial_search_inv[OF inv] .
  show "\<forall>r\<in>set (query_aux_relus n Q). ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q)"
    using query_aux_relus_form unfolding relu_in_aux_form_def by blast
  show "relus_ok S (query_aux_relus n Q)"
    unfolding relus_ok_def
  proof
    fix r
    assume r: "r \<in> set (query_aux_relus n Q)"
    have form: "relu_in_aux_form n Q r" using query_aux_relus_form[OF r] .
    have "aux_form S r"
      using relu_in_aux_form_aux[OF ready form] bm unfolding aux_form_def by simp
    moreover have "relu_b r < n" "relu_f r < n" "relu_aux r < n"
      using form unfolding relu_in_aux_form_def by auto
    ultimately show "aux_form S r \<and> relu_b r \<in> carrier S \<and> relu_f r \<in> carrier S \<and> relu_aux r \<in> carrier S"
      using vars by simp
  qed
qed

theorem search_from_start_sound:
  assumes ready: "engine_ready n Q" and start: "search_start n Q S bs ns"
  shows "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Sat v \<Longrightarrow>
           satisfies_query v Q"
    and "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Unsat \<Longrightarrow>
           unsatisfiable Q"
proof -
  note facts = search_start_facts[OF ready start]
  have bm: "tableau_bounded_models S = tableau_bounded_models (initial_tableau n Q)"
    using start unfolding search_start_def by blast
  show "satisfies_query v Q"
    if loop: "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Sat v"
  proof -
    have "v \<in> tableau_bounded_models (initial_tableau n Q)"
      and relus: "list_all (satisfies_relu_constraint v) (relu_atoms Q)"
      using search_loop_sound(1)[OF facts loop] bm by auto
    then show ?thesis
      using bounded_model_satisfies_linear_part[OF ready] unfolding satisfies_query_def list_all_iff by blast
  qed
  show "unsatisfiable Q"
    if loop: "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Unsat"
  proof -
    have "tableau_bounded_models (initial_tableau n Q) \<inter> relu_solutions (query_aux_relus n Q) = {}"
      using search_loop_sound(2)[OF facts loop] bm by simp
    then show ?thesis
      using relus_root_empty_unsat[OF ready] query_aux_relus_form by blast
  qed
qed

lemma native_search_start:
  assumes ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
      and init: "native_initial_tableau n Q = Some (S, bs, ns)"
  shows "search_start n Q S bs ns"
  using native_initial_tableau_sound[OF ready consistent init] native_initial_carrier[OF init]
  unfolding search_start_def by simp

text \<open>
  The auxiliary basis itself is Marabou's start when
  GlobalConfiguration::ONLY_AUX_INITIAL_BASIS holds (Engine.cpp:1135).
\<close>

lemma aux_search_start:
  assumes ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
  shows "search_start n Q (initial_tableau n Q) (initial_basics n Q) [0..<n]"
  using initial_tableau_invariant[OF ready consistent]
  unfolding search_start_def by (simp add: initial_tableau_def)

text \<open>The search from Marabou's default initial basis.\<close>

definition solve_search :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> search_result" where
  "solve_search fuel sf n Q =
     (if \<not> engine_ready n Q then Search_Unknown
      else if \<not> bounds_consistent n Q then Search_Unsat
      else (case native_initial_tableau n Q of
              None \<Rightarrow> Search_Unknown
            | Some (S, bs, ns) \<Rightarrow> search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns)))"

text \<open>The search from the auxiliary basis (ONLY_AUX_INITIAL_BASIS).\<close>

definition solve_search_aux_basis :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> search_result" where
  "solve_search_aux_basis fuel sf n Q =
     (if \<not> engine_ready n Q then Search_Unknown
      else if \<not> bounds_consistent n Q then Search_Unsat
      else search_loop fuel sf Q (query_aux_relus n Q)
             (initial_search (initial_tableau n Q) (initial_basics n Q) [0..<n]))"

theorem solve_search_sat:
  assumes "solve_search fuel sf n Q = Search_Sat v"
  shows "satisfies_query v Q"
proof -
  have ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
    using assms by (auto simp: solve_search_def split: if_splits)
  obtain S bs ns where init: "native_initial_tableau n Q = Some (S, bs, ns)"
    and loop: "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Sat v"
    using assms ready consistent by (auto simp: solve_search_def split: option.splits prod.splits)
  show ?thesis
    using search_from_start_sound(1)[OF ready native_search_start[OF ready consistent init] loop] .
qed

theorem solve_search_unsat:
  assumes "solve_search fuel sf n Q = Search_Unsat"
  shows "unsatisfiable Q"
proof -
  have ready: "engine_ready n Q"
    using assms by (auto simp: solve_search_def split: if_splits)
  show ?thesis
  proof (cases "bounds_consistent n Q")
    case False
    then show ?thesis using inconsistent_bounds_unsatisfiable[OF ready] by blast
  next
    case consistent: True
    obtain S bs ns where init: "native_initial_tableau n Q = Some (S, bs, ns)"
      and loop: "search_loop fuel sf Q (query_aux_relus n Q) (initial_search S bs ns) = Search_Unsat"
      using assms ready consistent by (auto simp: solve_search_def split: option.splits prod.splits)
    show ?thesis
      using search_from_start_sound(2)[OF ready native_search_start[OF ready consistent init] loop] .
  qed
qed

theorem solve_search_aux_basis_sat:
  assumes "solve_search_aux_basis fuel sf n Q = Search_Sat v"
  shows "satisfies_query v Q"
proof -
  have ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
    using assms by (auto simp: solve_search_aux_basis_def split: if_splits)
  then show ?thesis
    using search_from_start_sound(1)[OF ready aux_search_start[OF ready consistent]] assms
    by (simp add: solve_search_aux_basis_def)
qed

theorem solve_search_aux_basis_unsat:
  assumes "solve_search_aux_basis fuel sf n Q = Search_Unsat"
  shows "unsatisfiable Q"
proof -
  have ready: "engine_ready n Q"
    using assms by (auto simp: solve_search_aux_basis_def split: if_splits)
  show ?thesis
  proof (cases "bounds_consistent n Q")
    case False
    then show ?thesis using inconsistent_bounds_unsatisfiable[OF ready] by blast
  next
    case consistent: True
    show ?thesis
      using search_from_start_sound(2)[OF ready aux_search_start[OF ready consistent]] assms ready consistent
      by (simp add: solve_search_aux_basis_def)
  qed
qed

definition solve_query_search :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> search_result" where
  "solve_query_search fuel sf Q = solve_search fuel sf (query_width Q) Q"

corollary solve_query_search_sound:
  "solve_query_search fuel sf Q = Search_Sat v \<Longrightarrow> satisfies_query v Q"
  "solve_query_search fuel sf Q = Search_Unsat \<Longrightarrow> unsatisfiable Q"
  unfolding solve_query_search_def using solve_search_sat solve_search_unsat by blast+

corollary solve_search_verdicts:
  "is_search_sat (solve_search fuel sf n Q) \<Longrightarrow> satisfiable Q"
  "is_search_unsat (solve_search fuel sf n Q) \<Longrightarrow> unsatisfiable Q"
  "is_search_sat (solve_search_aux_basis fuel sf n Q) \<Longrightarrow> satisfiable Q"
  "is_search_unsat (solve_search_aux_basis fuel sf n Q) \<Longrightarrow> unsatisfiable Q"
  using solve_search_sat solve_search_unsat solve_search_aux_basis_sat solve_search_aux_basis_unsat
  unfolding is_search_sat_iff is_search_unsat_iff satisfiable_def by blast+

export_code solve_query_search solve_search solve_search_aux_basis search_loop pop_split perform_split
  checking SML

end
