theory Tableau_Bound_Update
  imports Tableau_Initial_Basis
begin

text \<open>
  Bound application and local conflicts, as in src/engine at the pinned
  revision:
  \<^item> BoundManager::setLowerBound/setUpperBound (BoundManager.cpp:172-199)
    change a bound only when the proposal is strictly stronger, mark it as
    pending (_tightenedLower/_tightenedUpper) and record the first crossing
    (recordInconsistentBound, 161-170);
  \<^item> BoundManager::tightenLowerBound/tightenUpperBound (145-159, 315-378)
    then call Tableau::updateVariableToComplyWithLowerBoundUpdate or
    UpperBoundUpdate (Tableau.cpp:1785-1827): a nonbasic outside the new bound
    is moved onto it through setNonBasicAssignment(\<dots>, true); a basic only has
    its status recomputed;
  \<^item> BoundManager::propagateTightenings (268-284) notifies and clears the
    pending bounds;
  \<^item> Engine::solve throws InfeasibleQueryException when
    Tableau::allBoundsValid fails (Engine.cpp:313-317);
  \<^item> Engine::applySplit (1994-2141) applies a split's bounds with a reset
    explanation, as ground bounds flagged isPhaseFixing: branch restrictions,
    not derived facts;
  \<^item> RowBoundTightener::tightenOnSingleInvertedBasisRow
    (RowBoundTightener.cpp:237-402) derives bounds from one tableau row.
  Comparisons are exact: native consistency uses FloatUtils::gte, and row
  bounds are loosened by EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT;
  both tolerances are zero here. The model recomputes the cost function from
  the statuses, so the native invalidation of a cached cost function is not
  needed.
\<close>

section \<open>The bound store\<close>

datatype bound_side = Lower_Side | Upper_Side

record bound_store =
  store_tableau :: tableau_state
  pending_lower :: "var set"
  pending_upper :: "var set"
  first_conflict :: "(var \<times> bound_side \<times> real) option"

fun bound_holds :: "bound_side \<Rightarrow> real \<Rightarrow> real \<Rightarrow> bool" where
  "bound_holds Lower_Side v w \<longleftrightarrow> v \<le> w"
| "bound_holds Upper_Side v w \<longleftrightarrow> w \<le> v"

fun stronger :: "bound_side \<Rightarrow> tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bool" where
  "stronger Lower_Side S x v \<longleftrightarrow> tableau_lower S x < v"
| "stronger Upper_Side S x v \<longleftrightarrow> v < tableau_upper S x"

fun with_bound :: "bound_side \<Rightarrow> tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> tableau_state" where
  "with_bound Lower_Side S x v = S\<lparr>tableau_lower := (tableau_lower S)(x := v)\<rparr>"
| "with_bound Upper_Side S x v = S\<lparr>tableau_upper := (tableau_upper S)(x := v)\<rparr>"

definition crossed :: "tableau_state \<Rightarrow> var \<Rightarrow> bool" where
  "crossed S x \<longleftrightarrow> tableau_upper S x < tableau_lower S x"

abbreviation carrier :: "tableau_state \<Rightarrow> var set" where
  "carrier S \<equiv> tableau_basics S \<union> tableau_nonbasics S"

fun mark_pending :: "bound_side \<Rightarrow> var \<Rightarrow> bound_store \<Rightarrow> bound_store" where
  "mark_pending Lower_Side x B = B\<lparr>pending_lower := insert x (pending_lower B)\<rparr>"
| "mark_pending Upper_Side x B = B\<lparr>pending_upper := insert x (pending_upper B)\<rparr>"

text \<open>BoundManager::setLowerBound/setUpperBound: the result says whether the bound changed.\<close>

definition set_bound :: "bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bound_store \<Rightarrow> bound_store \<times> bool" where
  "set_bound side x v B =
     (if stronger side (store_tableau B) x v then
        (let S' = with_bound side (store_tableau B) x v;
             B' = mark_pending side x (B\<lparr>store_tableau := S'\<rparr>)
         in (if first_conflict B = None \<and> crossed S' x
             then B'\<lparr>first_conflict := Some (x, side, v)\<rparr> else B', True))
      else (B, False))"

text \<open>Tableau::updateVariableToComplyWithLowerBoundUpdate/UpperBoundUpdate.\<close>

fun comply :: "bound_side \<Rightarrow> tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> tableau_state" where
  "comply Lower_Side S x v =
     (if x \<notin> tableau_basics S \<and> tableau_nonbasic_value S x < v
      then update_nonbasic_assignment S x v else S)"
| "comply Upper_Side S x v =
     (if x \<notin> tableau_basics S \<and> v < tableau_nonbasic_value S x
      then update_nonbasic_assignment S x v else S)"

text \<open>BoundManager::tightenLowerBound/tightenUpperBound.\<close>

definition tighten_bound :: "bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bound_store \<Rightarrow> bound_store \<times> bool" where
  "tighten_bound side x v B =
     (case set_bound side x v B of
        (B', True) \<Rightarrow> (B'\<lparr>store_tableau := comply side (store_tableau B') x v\<rparr>, True)
      | (B', False) \<Rightarrow> (B', False))"

section \<open>Basic facts\<close>

lemma with_bound_simps [simp]:
  "tableau_basics (with_bound side S x v) = tableau_basics S"
  "tableau_nonbasics (with_bound side S x v) = tableau_nonbasics S"
  "tableau_rows (with_bound side S x v) = tableau_rows S"
  "tableau_nonbasic_value (with_bound side S x v) = tableau_nonbasic_value S"
  "tableau_basic_value (with_bound side S x v) = tableau_basic_value S"
  by (cases side; simp)+

lemma comply_simps [simp]:
  "tableau_basics (comply side S x v) = tableau_basics S"
  "tableau_nonbasics (comply side S x v) = tableau_nonbasics S"
  "tableau_rows (comply side S x v) = tableau_rows S"
  "tableau_lower (comply side S x v) = tableau_lower S"
  "tableau_upper (comply side S x v) = tableau_upper S"
  by (cases side; simp)+

lemma bounded_models_cong:
  assumes "tableau_basics T = tableau_basics S" "tableau_nonbasics T = tableau_nonbasics S"
      "tableau_rows T = tableau_rows S" "tableau_lower T = tableau_lower S"
      "tableau_upper T = tableau_upper S"
  shows "tableau_bounded_models T = tableau_bounded_models S"
  using assms by (simp add: tableau_bounded_models_def tableau_models_def)

lemma tighten_weaker:
  "\<not> stronger side (store_tableau B) x v \<Longrightarrow> tighten_bound side x v B = (B, False)"
  by (simp add: tighten_bound_def set_bound_def)

lemma tighten_stronger:
  assumes "stronger side (store_tableau B) x v"
  shows "snd (tighten_bound side x v B)"
    and "store_tableau (fst (tighten_bound side x v B)) =
           comply side (with_bound side (store_tableau B) x v) x v"
  using assms by (cases side; simp add: tighten_bound_def set_bound_def Let_def)+

lemma tighten_store_tableau:
  "store_tableau (fst (tighten_bound side x v B)) =
     (if stronger side (store_tableau B) x v
      then comply side (with_bound side (store_tableau B) x v) x v else store_tableau B)"
  using tighten_weaker tighten_stronger(2) by (cases "stronger side (store_tableau B) x v") simp_all

lemma tighten_structure [simp]:
  "tableau_basics (store_tableau (fst (tighten_bound side x v B))) = tableau_basics (store_tableau B)"
  "tableau_nonbasics (store_tableau (fst (tighten_bound side x v B))) = tableau_nonbasics (store_tableau B)"
  "tableau_rows (store_tableau (fst (tighten_bound side x v B))) = tableau_rows (store_tableau B)"
  by (simp_all add: tighten_store_tableau)

lemma stronger_implies_old:
  "stronger side S x v \<Longrightarrow> bound_holds side v w \<Longrightarrow>
     (case side of Lower_Side \<Rightarrow> tableau_lower S x \<le> w | Upper_Side \<Rightarrow> w \<le> tableau_upper S x)"
  by (cases side) auto

section \<open>A stronger bound is conjunction; the invariant is kept\<close>

theorem tighten_bounded_models:
  assumes x: "x \<in> carrier (store_tableau B)"
  shows "tableau_bounded_models (store_tableau (fst (tighten_bound side x v B))) =
         (if stronger side (store_tableau B) x v
          then tableau_bounded_models (store_tableau B) \<inter> {w. bound_holds side v (w x)}
          else tableau_bounded_models (store_tableau B))"
proof (cases "stronger side (store_tableau B) x v")
  case False
  then show ?thesis by (simp add: tighten_weaker)
next
  case True
  let ?S = "store_tableau B"
  have eq: "tableau_bounded_models (store_tableau (fst (tighten_bound side x v B))) =
      tableau_bounded_models (with_bound side ?S x v)"
    using tighten_stronger(2)[OF True]
      bounded_models_cong[of "comply side (with_bound side ?S x v) x v" "with_bound side ?S x v"]
    by simp
  have "tableau_bounded_models (with_bound side ?S x v) =
      tableau_bounded_models ?S \<inter> {w. bound_holds side v (w x)}"
    using x True
    by (cases side) (auto simp: tableau_bounded_models_def tableau_models_def)
  then show ?thesis using eq True by simp
qed

corollary tighten_weaker_noop:
  "\<not> stronger side (store_tableau B) x v \<Longrightarrow> fst (tighten_bound side x v B) = B"
  by (simp add: tighten_weaker)

theorem tighten_invariant:
  assumes inv: "simplex_invariant (store_tableau B) bs ns"
      and x: "x \<in> carrier (store_tableau B)"
      and ok: "\<not> crossed (with_bound side (store_tableau B) x v) x"
  shows "simplex_invariant (store_tableau (fst (tighten_bound side x v B))) bs ns"
proof (cases "stronger side (store_tableau B) x v")
  case False
  then show ?thesis using inv by (simp add: tighten_weaker)
next
  case True
  let ?S = "store_tableau B"
  let ?S1 = "with_bound side ?S x v"
  let ?S2 = "comply side ?S1 x v"
  have S2: "store_tableau (fst (tighten_bound side x v B)) = ?S2"
    using tighten_stronger(2)[OF True] .
  have sup: "tableau_rows_supported ?S" and rows: "tableau_rows_satisfied ?S"
    and nb: "tableau_nonbasic_bounds_satisfied ?S" and ord: "tableau_bounds_ordered ?S"
    and lists: "distinct bs" "distinct ns" "set bs = tableau_basics ?S" "set ns = tableau_nonbasics ?S"
    using inv unfolding simplex_invariant_def by auto
  have disj: "tableau_basics ?S \<inter> tableau_nonbasics ?S = {}"
    using sup unfolding tableau_rows_supported_def by blast
  have sup2: "tableau_rows_supported ?S2"
    using sup unfolding tableau_rows_supported_def by simp
  have rows1: "tableau_rows_satisfied ?S1"
    using rows unfolding tableau_rows_satisfied_def by simp
  have rows2: "tableau_rows_satisfied ?S2"
  proof (cases side)
    case Lower_Side
    show ?thesis
    proof (cases "x \<notin> tableau_basics ?S1 \<and> tableau_nonbasic_value ?S1 x < v")
      case True
      then have "x \<in> tableau_nonbasics ?S1" using x by auto
      then show ?thesis
        using update_nonbasic_preserves_rows[OF _ rows1] True Lower_Side by auto
    next
      case False
      then show ?thesis using rows1 Lower_Side by auto
    qed
  next
    case Upper_Side
    show ?thesis
    proof (cases "x \<notin> tableau_basics ?S1 \<and> v < tableau_nonbasic_value ?S1 x")
      case True
      then have "x \<in> tableau_nonbasics ?S1" using x by auto
      then show ?thesis
        using update_nonbasic_preserves_rows[OF _ rows1] True Upper_Side by auto
    next
      case False
      then show ?thesis using rows1 Upper_Side by auto
    qed
  qed
  have ok': "tableau_lower ?S1 x \<le> tableau_upper ?S1 x" using ok by (simp add: crossed_def)
  have nb2: "tableau_nonbasic_bounds_satisfied ?S2"
    unfolding tableau_nonbasic_bounds_satisfied_def
  proof
    fix j
    assume j: "j \<in> tableau_nonbasics ?S2"
    have jS: "j \<in> tableau_nonbasics ?S" using j by simp
    have old: "tableau_lower ?S j \<le> tableau_nonbasic_value ?S j"
      "tableau_nonbasic_value ?S j \<le> tableau_upper ?S j"
      using nb jS unfolding tableau_nonbasic_bounds_satisfied_def by auto
    show "tableau_lower ?S2 j \<le> tableau_nonbasic_value ?S2 j \<and>
          tableau_nonbasic_value ?S2 j \<le> tableau_upper ?S2 j"
    proof (cases "j = x")
      case False
      have "tableau_nonbasic_value ?S2 j = tableau_nonbasic_value ?S j"
        using False by (cases side) (auto simp: update_nonbasic_assignment_def)
      moreover have "tableau_lower ?S2 j = tableau_lower ?S j" "tableau_upper ?S2 j = tableau_upper ?S j"
        using False by (cases side; simp)+
      ultimately show ?thesis using old by simp
    next
      case jx: True
      have xN: "x \<notin> tableau_basics ?S" using jS jx disj by blast
      show ?thesis
        using ok' old xN jx True
        by (cases side) (auto simp: update_nonbasic_assignment_def)
    qed
  qed
  have ord2: "tableau_bounds_ordered ?S2"
    using ord ok' unfolding tableau_bounds_ordered_def
    by (cases side) (auto split: if_splits)
  show ?thesis
    unfolding S2 simplex_invariant_def using sup2 rows2 nb2 ord2 lists by simp
qed

text \<open>A tightened basic keeps its value; its status is read against the new bound.\<close>

lemma tighten_basic_value:
  assumes "x \<in> tableau_basics (store_tableau B)"
  shows "tableau_basic_value (store_tableau (fst (tighten_bound side x v B))) =
         tableau_basic_value (store_tableau B)"
    and "tableau_nonbasic_value (store_tableau (fst (tighten_bound side x v B))) =
         tableau_nonbasic_value (store_tableau B)"
  using assms by (cases side; simp add: tighten_store_tableau)+

section \<open>Pending tightenings\<close>

lemma tighten_pending:
  "pending_lower (fst (tighten_bound side x v B)) =
     (if side = Lower_Side \<and> stronger side (store_tableau B) x v
      then insert x (pending_lower B) else pending_lower B)"
  "pending_upper (fst (tighten_bound side x v B)) =
     (if side = Upper_Side \<and> stronger side (store_tableau B) x v
      then insert x (pending_upper B) else pending_upper B)"
  by (cases side; simp add: tighten_bound_def set_bound_def Let_def)+

text \<open>BoundManager::propagateTightenings, in variable order: notify, then clear.\<close>

definition propagate_tightenings ::
  "var list \<Rightarrow> bound_store \<Rightarrow> (var \<times> bound_side \<times> real) list \<times> bound_store" where
  "propagate_tightenings xs B =
     (concat (map (\<lambda>x.
        (if x \<in> pending_lower B then [(x, Lower_Side, tableau_lower (store_tableau B) x)] else []) @
        (if x \<in> pending_upper B then [(x, Upper_Side, tableau_upper (store_tableau B) x)] else [])) xs),
      B\<lparr>pending_lower := pending_lower B - set xs, pending_upper := pending_upper B - set xs\<rparr>)"

theorem propagated_bounds_hold:
  assumes "(x, side, v) \<in> set (fst (propagate_tightenings xs B))"
      and "x \<in> carrier (store_tableau B)" and "w \<in> tableau_bounded_models (store_tableau B)"
  shows "bound_holds side v (w x)"
  using assms
  by (auto simp: propagate_tightenings_def tableau_bounded_models_def split: if_splits)

lemma propagate_tightenings_exact:
  "(x, Lower_Side, v) \<in> set (fst (propagate_tightenings xs B)) \<longleftrightarrow>
     x \<in> set xs \<and> x \<in> pending_lower B \<and> v = tableau_lower (store_tableau B) x"
  "(x, Upper_Side, v) \<in> set (fst (propagate_tightenings xs B)) \<longleftrightarrow>
     x \<in> set xs \<and> x \<in> pending_upper B \<and> v = tableau_upper (store_tableau B) x"
  by (auto simp: propagate_tightenings_def split: if_splits)

section \<open>Local conflicts\<close>

definition conflict_sound :: "bound_store \<Rightarrow> bool" where
  "conflict_sound B \<longleftrightarrow>
     (case first_conflict B of
        None \<Rightarrow> True
      | Some (x, side, v) \<Rightarrow> x \<in> carrier (store_tableau B) \<and> crossed (store_tableau B) x)"

definition conflict_complete :: "bound_store \<Rightarrow> bool" where
  "conflict_complete B \<longleftrightarrow>
     (first_conflict B = None \<longrightarrow> (\<forall>x\<in>carrier (store_tableau B). \<not> crossed (store_tableau B) x))"

lemma tighten_bounds_monotone:
  "tableau_lower (store_tableau B) y \<le> tableau_lower (store_tableau (fst (tighten_bound side x v B))) y"
  "tableau_upper (store_tableau (fst (tighten_bound side x v B))) y \<le> tableau_upper (store_tableau B) y"
  by (cases side; auto simp: tighten_store_tableau)+

lemma crossed_persists:
  "crossed (store_tableau B) y \<Longrightarrow> crossed (store_tableau (fst (tighten_bound side x v B))) y"
  using tighten_bounds_monotone[where B = B and y = y and side = side and x = x and v = v]
  unfolding crossed_def by linarith

lemma tighten_conflict:
  "first_conflict (fst (tighten_bound side x v B)) =
     (if stronger side (store_tableau B) x v \<and> first_conflict B = None \<and>
         crossed (with_bound side (store_tableau B) x v) x
      then Some (x, side, v) else first_conflict B)"
  by (cases side; simp add: tighten_bound_def set_bound_def Let_def)+

theorem tighten_conflict_sound:
  assumes "conflict_sound B" "x \<in> carrier (store_tableau B)"
  shows "conflict_sound (fst (tighten_bound side x v B))"
proof (cases "stronger side (store_tableau B) x v \<and> first_conflict B = None \<and>
              crossed (with_bound side (store_tableau B) x v) x")
  case True
  have "crossed (store_tableau (fst (tighten_bound side x v B))) x"
    using True unfolding crossed_def by (cases side) (auto simp: tighten_store_tableau)
  then show ?thesis
    using True assms(2) unfolding conflict_sound_def by (simp add: tighten_conflict)
next
  case False
  then show ?thesis
    using assms crossed_persists unfolding conflict_sound_def
    by (auto simp: tighten_conflict split: option.splits)
qed

theorem tighten_conflict_complete:
  assumes "conflict_complete B"
  shows "conflict_complete (fst (tighten_bound side x v B))"
proof (cases "stronger side (store_tableau B) x v")
  case False
  then show ?thesis using assms by (simp add: tighten_weaker)
next
  case True
  show ?thesis
    unfolding conflict_complete_def
  proof (intro impI ballI)
    fix y
    assume none: "first_conflict (fst (tighten_bound side x v B)) = None"
      and y: "y \<in> carrier (store_tableau (fst (tighten_bound side x v B)))"
    have old_none: "first_conflict B = None"
      and new_ok: "\<not> crossed (with_bound side (store_tableau B) x v) x"
      using none True by (auto simp: tighten_conflict split: if_splits)
    have old_ok: "\<not> crossed (store_tableau B) y"
      using assms old_none y unfolding conflict_complete_def by simp
    show "\<not> crossed (store_tableau (fst (tighten_bound side x v B))) y"
    proof (cases "y = x")
      case True
      then show ?thesis
        using new_ok \<open>stronger side (store_tableau B) x v\<close>
        unfolding crossed_def by (cases side) (auto simp: tighten_store_tableau)
    next
      case False
      then show ?thesis
        using old_ok \<open>stronger side (store_tableau B) x v\<close>
        unfolding crossed_def by (cases side) (auto simp: tighten_store_tableau)
    qed
  qed
qed

theorem conflict_no_bounded_model:
  assumes "conflict_sound B" "first_conflict B \<noteq> None"
  shows "tableau_bounded_models (store_tableau B) = {}"
proof -
  obtain x side v where c: "first_conflict B = Some (x, side, v)"
    using assms(2) by auto
  have "x \<in> carrier (store_tableau B)" "crossed (store_tableau B) x"
    using assms(1) c unfolding conflict_sound_def by auto
  then show ?thesis
    unfolding tableau_bounded_models_def crossed_def by force
qed

text \<open>Tableau::allBoundsValid is exactly the absence of a recorded conflict.\<close>

lemma all_bounds_valid_iff:
  assumes "conflict_sound B" "conflict_complete B"
  shows "first_conflict B = None \<longleftrightarrow> (\<forall>x\<in>carrier (store_tableau B). \<not> crossed (store_tableau B) x)"
  using assms unfolding conflict_sound_def conflict_complete_def
  by (auto split: option.splits)

section \<open>Branches: derived bounds and decisions\<close>

text \<open>
  A branch is a bound store with the list of decisions (split bounds) applied
  on the way to it. Its invariant says that its bounded solutions are exactly
  those of the root tableau that satisfy the decisions.
\<close>

record branch =
  branch_store :: bound_store
  branch_decisions :: "(bound_side \<times> var \<times> real) list"

definition decision_models :: "(bound_side \<times> var \<times> real) list \<Rightarrow> valuation set" where
  "decision_models D = {w. \<forall>(side, x, v)\<in>set D. bound_holds side v (w x)}"

definition branch_of :: "tableau_state \<Rightarrow> branch \<Rightarrow> bool" where
  "branch_of S0 Br \<longleftrightarrow>
     tableau_bounded_models (store_tableau (branch_store Br)) =
       tableau_bounded_models S0 \<inter> decision_models (branch_decisions Br)"

definition entailed :: "tableau_state \<Rightarrow> bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bool" where
  "entailed S side x v \<longleftrightarrow> (\<forall>w\<in>tableau_bounded_models S. bound_holds side v (w x))"

definition apply_derived :: "bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> branch \<Rightarrow> branch" where
  "apply_derived side x v Br = Br\<lparr>branch_store := fst (tighten_bound side x v (branch_store Br))\<rparr>"

text \<open>
  A decision is recorded whether or not it is stronger; native applySplit
  records a ground bound only when it is, which makes no semantic difference.
\<close>

definition apply_decision :: "bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> branch \<Rightarrow> branch" where
  "apply_decision side x v Br =
     \<lparr>branch_store = fst (tighten_bound side x v (branch_store Br)),
      branch_decisions = branch_decisions Br @ [(side, x, v)]\<rparr>"

definition root_branch :: "tableau_state \<Rightarrow> branch" where
  "root_branch S =
     \<lparr>branch_store = \<lparr>store_tableau = S, pending_lower = {}, pending_upper = {}, first_conflict = None\<rparr>,
      branch_decisions = []\<rparr>"

lemma root_branch_of: "branch_of S (root_branch S)"
  by (simp add: branch_of_def root_branch_def decision_models_def)

lemma root_branch_conflicts:
  assumes "simplex_invariant S bs ns"
  shows "conflict_sound (branch_store (root_branch S))"
    and "conflict_complete (branch_store (root_branch S))"
proof -
  have "\<forall>x\<in>carrier S. tableau_lower S x \<le> tableau_upper S x"
    using assms unfolding simplex_invariant_def tableau_bounds_ordered_def by blast
  then show "conflict_sound (branch_store (root_branch S))"
    "conflict_complete (branch_store (root_branch S))"
    by (auto simp: conflict_sound_def conflict_complete_def root_branch_def crossed_def not_less)
qed

lemma tighten_bounded_models_subset:
  assumes "x \<in> carrier (store_tableau B)"
  shows "tableau_bounded_models (store_tableau (fst (tighten_bound side x v B))) =
         tableau_bounded_models (store_tableau B) \<inter> {w. bound_holds side v (w x)}"
proof -
  have weaker: "tableau_bounded_models (store_tableau B) \<subseteq> {w. bound_holds side v (w x)}"
    if ns: "\<not> stronger side (store_tableau B) x v"
  proof
    fix w
    assume w: "w \<in> tableau_bounded_models (store_tableau B)"
    have "tableau_lower (store_tableau B) x \<le> w x \<and> w x \<le> tableau_upper (store_tableau B) x"
      using w assms unfolding tableau_bounded_models_def by blast
    then show "w \<in> {w. bound_holds side v (w x)}" using ns by (cases side) auto
  qed
  show ?thesis
    using tighten_bounded_models[OF assms, of side v] weaker
    by (auto split: if_splits)
qed

theorem apply_derived_branch:
  assumes br: "branch_of S0 Br" and x: "x \<in> carrier (store_tableau (branch_store Br))"
      and ent: "entailed (store_tableau (branch_store Br)) side x v"
  shows "branch_of S0 (apply_derived side x v Br)"
  using br tighten_bounded_models_subset[OF x, of side v] ent
  unfolding branch_of_def apply_derived_def entailed_def by auto

theorem apply_decision_branch:
  assumes br: "branch_of S0 Br" and x: "x \<in> carrier (store_tableau (branch_store Br))"
  shows "branch_of S0 (apply_decision side x v Br)"
  using br tighten_bounded_models_subset[OF x, of side v]
  unfolding branch_of_def apply_decision_def decision_models_def by auto

text \<open>A split bound applied as if derived falsifies the branch invariant.\<close>

theorem undeclared_decision_breaks_branch:
  assumes br: "branch_of S0 Br" and x: "x \<in> carrier (store_tableau (branch_store Br))"
      and not_ent: "\<not> entailed (store_tableau (branch_store Br)) side x v"
  shows "\<not> branch_of S0 (apply_derived side x v Br)"
proof
  assume br': "branch_of S0 (apply_derived side x v Br)"
  obtain w where w: "w \<in> tableau_bounded_models (store_tableau (branch_store Br))"
    and bad: "\<not> bound_holds side v (w x)"
    using not_ent unfolding entailed_def by blast
  have "w \<in> tableau_bounded_models S0 \<inter> decision_models (branch_decisions Br)"
    using w br unfolding branch_of_def by simp
  then have "w \<in> tableau_bounded_models (store_tableau (branch_store (apply_derived side x v Br)))"
    using br' unfolding branch_of_def apply_derived_def by simp
  then show False
    using tighten_bounded_models_subset[OF x, of side v] bad
    unfolding apply_derived_def by simp
qed

theorem branch_conflict_refutes:
  assumes "branch_of S0 Br" "conflict_sound (branch_store Br)"
      "first_conflict (branch_store Br) \<noteq> None"
  shows "tableau_bounded_models S0 \<inter> decision_models (branch_decisions Br) = {}"
  using assms conflict_no_bounded_model unfolding branch_of_def by metis

corollary root_conflict_unsatisfiable:
  assumes ready: "engine_ready n Q" and br: "branch_of (initial_tableau n Q) Br"
      and nodec: "branch_decisions Br = []"
      and "conflict_sound (branch_store Br)" "first_conflict (branch_store Br) \<noteq> None"
  shows "unsatisfiable Q"
proof -
  have "tableau_bounded_models (initial_tableau n Q) = {}"
    using branch_conflict_refutes[OF br assms(4,5)] nodec by (simp add: decision_models_def)
  then show ?thesis using initial_empty_unsatisfiable[OF ready] by blast
qed

text \<open>The simplex loop run on a branch refutes that branch.\<close>

corollary branch_simplex_infeasible:
  assumes "branch_of S0 Br" "simplex_invariant (store_tableau (branch_store Br)) bs ns"
      "simplex_run fuel (store_tableau (branch_store Br)) bs ns = (Infeasible, S', bs', ns')"
  shows "tableau_bounded_models S0 \<inter> decision_models (branch_decisions Br) = {}"
  using simplex_run_sound(4)[OF assms(2,3)] assms(1) unfolding branch_of_def by simp

section \<open>Bounds derived from a tableau row\<close>

text \<open>
  RowBoundTightener::tightenOnSingleInvertedBasisRow for a row y = c + \<Sum> a x:
  sign-selected bounds give bounds for y, and solving the row for one x with
  a nonzero coefficient gives bounds for x. Each term is bounded separately,
  so repeated variables are handled soundly.
\<close>

fun term_lower :: "tableau_state \<Rightarrow> real \<times> var \<Rightarrow> real" where
  "term_lower S (a, x) = (if 0 \<le> a then a * tableau_lower S x else a * tableau_upper S x)"

fun term_upper :: "tableau_state \<Rightarrow> real \<times> var \<Rightarrow> real" where
  "term_upper S (a, x) = (if 0 \<le> a then a * tableau_upper S x else a * tableau_lower S x)"

definition row_lower_bound :: "tableau_state \<Rightarrow> linexpr \<Rightarrow> real" where
  "row_lower_bound S r = row_const r + sum_list (map (term_lower S) (row_terms r))"

definition row_upper_bound :: "tableau_state \<Rightarrow> linexpr \<Rightarrow> real" where
  "row_upper_bound S r = row_const r + sum_list (map (term_upper S) (row_terms r))"

lemma eval_terms_within:
  assumes "\<forall>x\<in>snd ` set ts. tableau_lower S x \<le> w x \<and> w x \<le> tableau_upper S x"
  shows "sum_list (map (term_lower S) ts) \<le> eval_terms w ts \<and>
         eval_terms w ts \<le> sum_list (map (term_upper S) ts)"
  using assms
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons p ts)
  obtain a x where p: "p = (a, x)" by (cases p)
  have bx: "tableau_lower S x \<le> w x" "w x \<le> tableau_upper S x" using Cons.prems p by auto
  have bnd: "term_lower S (a, x) \<le> a * w x \<and> a * w x \<le> term_upper S (a, x)"
  proof (cases "0 \<le> a")
    case True
    then show ?thesis using bx by (simp add: mult_left_mono)
  next
    case False
    then have "a \<le> 0" by simp
    then show ?thesis using bx False by (simp add: mult_left_mono_neg)
  qed
  have "sum_list (map (term_lower S) ts) \<le> eval_terms w ts \<and>
        eval_terms w ts \<le> sum_list (map (term_upper S) ts)"
    using Cons by simp
  then show ?case using bnd p by simp
qed

lemma row_bounds_within:
  assumes "\<forall>x\<in>linexpr_vars r. tableau_lower S x \<le> w x \<and> w x \<le> tableau_upper S x"
  shows "row_lower_bound S r \<le> eval_linexpr w r \<and> eval_linexpr w r \<le> row_upper_bound S r"
  using eval_terms_within[of "row_terms r" S w] assms
  by (simp add: row_lower_bound_def row_upper_bound_def eval_linexpr_parts linexpr_vars_parts)

text \<open>Solving row y for x: c * x = y - const - rest.\<close>

definition solved_bounds :: "tableau_state \<Rightarrow> var \<Rightarrow> var \<Rightarrow> real \<times> real" where
  "solved_bounds S y x =
     (let r = tableau_rows S y; c = row_coefficient r x;
          rest = Linexpr (row_const r) (drop_var (row_terms r) x);
          lo = tableau_lower S y - row_upper_bound S rest;
          hi = tableau_upper S y - row_lower_bound S rest
      in if 0 < c then (lo / c, hi / c) else (hi / c, lo / c))"

datatype row_rule = Row_Basic bound_side var | Row_Solved bound_side var var

fun rule_valid :: "tableau_state \<Rightarrow> row_rule \<Rightarrow> bool" where
  "rule_valid S (Row_Basic side y) \<longleftrightarrow> y \<in> tableau_basics S"
| "rule_valid S (Row_Solved side y x) \<longleftrightarrow>
     y \<in> tableau_basics S \<and> row_coefficient (tableau_rows S y) x \<noteq> 0"

fun rule_bound :: "tableau_state \<Rightarrow> row_rule \<Rightarrow> bound_side \<times> var \<times> real" where
  "rule_bound S (Row_Basic Lower_Side y) = (Lower_Side, y, row_lower_bound S (tableau_rows S y))"
| "rule_bound S (Row_Basic Upper_Side y) = (Upper_Side, y, row_upper_bound S (tableau_rows S y))"
| "rule_bound S (Row_Solved Lower_Side y x) = (Lower_Side, x, fst (solved_bounds S y x))"
| "rule_bound S (Row_Solved Upper_Side y x) = (Upper_Side, x, snd (solved_bounds S y x))"

lemma bounded_model_facts:
  assumes sup: "tableau_rows_supported S" and w: "w \<in> tableau_bounded_models S"
      and y: "y \<in> tableau_basics S"
  shows "w y = eval_linexpr w (tableau_rows S y)"
    and "\<forall>x\<in>linexpr_vars (tableau_rows S y). tableau_lower S x \<le> w x \<and> w x \<le> tableau_upper S x"
    and "tableau_lower S y \<le> w y \<and> w y \<le> tableau_upper S y"
  using w y sup
  unfolding tableau_bounded_models_def tableau_models_def tableau_rows_supported_def by blast+

theorem row_rule_entailed:
  assumes sup: "tableau_rows_supported S" and valid: "rule_valid S rl"
      and rb: "rule_bound S rl = (side, x, v)"
  shows "entailed S side x v"
  unfolding entailed_def
proof
  fix w
  assume w: "w \<in> tableau_bounded_models S"
  show "bound_holds side v (w x)"
  proof (cases rl)
    case (Row_Basic s y)
    have y: "y \<in> tableau_basics S" using valid Row_Basic by simp
    note f = bounded_model_facts[OF sup w y]
    have "row_lower_bound S (tableau_rows S y) \<le> w y \<and> w y \<le> row_upper_bound S (tableau_rows S y)"
      using row_bounds_within[OF f(2)] f(1) by simp
    then show ?thesis using rb Row_Basic by (cases s) auto
  next
    case (Row_Solved s y z)
    have y: "y \<in> tableau_basics S" and c: "row_coefficient (tableau_rows S y) z \<noteq> 0"
      using valid Row_Solved by auto
    note f = bounded_model_facts[OF sup w y]
    let ?r = "tableau_rows S y" and ?c = "row_coefficient (tableau_rows S y) z"
    let ?rest = "Linexpr (row_const ?r) (drop_var (row_terms ?r) z)"
    have rest_vars: "\<forall>u\<in>linexpr_vars ?rest. tableau_lower S u \<le> w u \<and> w u \<le> tableau_upper S u"
      using f(2) by (auto simp: linexpr_vars_parts)
    have rest: "row_lower_bound S ?rest \<le> eval_linexpr w ?rest \<and>
                eval_linexpr w ?rest \<le> row_upper_bound S ?rest"
      using row_bounds_within[OF rest_vars] .
    have split: "w y = eval_linexpr w ?rest + ?c * w z"
      using f(1) eval_row_split[of w ?r z] by simp
    have lo: "tableau_lower S y - row_upper_bound S ?rest \<le> ?c * w z"
      and hi: "?c * w z \<le> tableau_upper S y - row_lower_bound S ?rest"
      using split rest f(3) by linarith+
    have x: "x = z" using rb Row_Solved by (cases s) auto
    show ?thesis
    proof (cases "0 < ?c")
      case True
      have "(tableau_lower S y - row_upper_bound S ?rest) / ?c \<le> w z"
        "w z \<le> (tableau_upper S y - row_lower_bound S ?rest) / ?c"
        using lo hi True by (simp_all add: pos_divide_le_eq pos_le_divide_eq mult.commute)
      then show ?thesis
        using rb Row_Solved True x by (cases s) (auto simp: solved_bounds_def Let_def)
    next
      case False
      then have neg: "?c < 0" using c by linarith
      have "(tableau_upper S y - row_lower_bound S ?rest) / ?c \<le> w z"
        "w z \<le> (tableau_lower S y - row_upper_bound S ?rest) / ?c"
        using lo hi neg by (simp_all add: neg_divide_le_eq neg_le_divide_eq mult.commute)
      then show ?thesis
        using rb Row_Solved False x by (cases s) (auto simp: solved_bounds_def Let_def)
    qed
  qed
qed

text \<open>
  Rules are evaluated against the current state, as the native tightener
  uses y's freshly tightened bounds for the solved variables. Invalid rules
  are skipped.
\<close>

fun apply_rules :: "row_rule list \<Rightarrow> branch \<Rightarrow> branch" where
  "apply_rules [] Br = Br"
| "apply_rules (rl # rls) Br =
     (let S = store_tableau (branch_store Br) in
      if rule_valid S rl
      then (case rule_bound S rl of (side, x, v) \<Rightarrow> apply_rules rls (apply_derived side x v Br))
      else apply_rules rls Br)"

definition row_rules :: "tableau_state \<Rightarrow> var \<Rightarrow> row_rule list" where
  "row_rules S y =
     [Row_Basic Lower_Side y, Row_Basic Upper_Side y] @
     concat (map (\<lambda>x. [Row_Solved Lower_Side y x, Row_Solved Upper_Side y x])
       (remdups (map snd (row_terms (tableau_rows S y)))))"

lemma rule_target_in_carrier:
  assumes sup: "tableau_rows_supported S" and valid: "rule_valid S rl"
      and rb: "rule_bound S rl = (side, x, v)"
  shows "x \<in> carrier S"
proof (cases rl)
  case (Row_Basic s y)
  then show ?thesis using valid rb by (cases s) auto
next
  case (Row_Solved s y z)
  have y: "y \<in> tableau_basics S" and c: "row_coefficient (tableau_rows S y) z \<noteq> 0"
    using valid Row_Solved by auto
  have "z \<in> linexpr_vars (tableau_rows S y)"
    using c coefficient_absent[of z "row_terms (tableau_rows S y)"]
    by (auto simp: row_coefficient_def linexpr_vars_parts)
  then have "z \<in> tableau_nonbasics S" using sup y unfolding tableau_rows_supported_def by blast
  then show ?thesis using rb Row_Solved by (cases s) auto
qed

theorem apply_rules_sound:
  assumes "branch_of S0 Br" "tableau_rows_supported (store_tableau (branch_store Br))"
      "conflict_sound (branch_store Br)" "conflict_complete (branch_store Br)"
  shows "branch_of S0 (apply_rules rls Br) \<and>
         branch_decisions (apply_rules rls Br) = branch_decisions Br \<and>
         tableau_rows_supported (store_tableau (branch_store (apply_rules rls Br))) \<and>
         conflict_sound (branch_store (apply_rules rls Br)) \<and>
         conflict_complete (branch_store (apply_rules rls Br))"
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
    have x: "x \<in> carrier ?S" using rule_target_in_carrier[OF Cons.prems(2) True rb] .
    have ent: "entailed ?S side x v" using row_rule_entailed[OF Cons.prems(2) True rb] .
    let ?Br = "apply_derived side x v Br"
    have br: "branch_of S0 ?Br" using apply_derived_branch[OF Cons.prems(1) x ent] .
    have sup: "tableau_rows_supported (store_tableau (branch_store ?Br))"
      using Cons.prems(2) unfolding tableau_rows_supported_def apply_derived_def by simp
    have cs: "conflict_sound (branch_store ?Br)"
      using tighten_conflict_sound[OF Cons.prems(3) x] unfolding apply_derived_def by simp
    have cc: "conflict_complete (branch_store ?Br)"
      using tighten_conflict_complete[OF Cons.prems(4)] unfolding apply_derived_def by simp
    have dec: "branch_decisions ?Br = branch_decisions Br" by (simp add: apply_derived_def)
    show ?thesis
      using Cons.IH[OF br sup cs cc] True rb dec by simp
  qed
qed

export_code tighten_bound propagate_tightenings apply_rules row_rules apply_decision
  root_branch checking SML

end
