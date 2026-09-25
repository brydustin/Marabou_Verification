theory Tableau_Relu_Split
  imports Tableau_Bound_Update
begin

text \<open>
  One native ReLU case split on the tableau state, in auxiliary form. Source,
  at the pinned revision (src/engine):
  \<^item> ReluConstraint::transformToUseAuxVariables (ReluConstraint.cpp:936-978)
    adds f - b - aux = 0 with aux \<ge> 0, so the matrix already holds the ReLU's
    linear part and a split needs no new equation;
  \<^item> ReluConstraint::getInactiveSplit (674-681) is b \<le> 0, f \<le> 0, and
    getActiveSplit (683-705) with the auxiliary in use is b \<ge> 0, aux \<le> 0;
  \<^item> ReluConstraint::getCaseSplits (597-641) orders them by the sign of f's
    assignment when no direction is set;
  \<^item> SearchTreeHandler::performSplit (SearchTreeHandler.cpp:133-230)
    disables the constraint, stores the state, applies the first split
    (asserting that it has no equations) and keeps the other as an
    alternative;
  \<^item> Engine::applySplit applies the split's bounds on the bound-only path
    (Tableau_Bound_Update.apply_decision);
  \<^item> ReluConstraint::getEntailedTightenings (827-916) always adds f \<ge> 0 and
    aux \<ge> 0.
  The matrix is fixed; only bounds change. The already proved query-level
  split (ReLU_Splitting) replaces the ReLU by y = 0 or y = x; this theory is
  the native form.
\<close>

section \<open>ReLUs in auxiliary form\<close>

record aux_relu =
  relu_b :: var
  relu_f :: var
  relu_aux :: var

definition relu_holds :: "aux_relu \<Rightarrow> valuation \<Rightarrow> bool" where
  "relu_holds r w \<longleftrightarrow> satisfies_relu w (relu_b r) (relu_f r)"

definition relu_solutions :: "aux_relu list \<Rightarrow> valuation set" where
  "relu_solutions R = {w. \<forall>r\<in>set R. relu_holds r w}"

text \<open>The auxiliary equation f - b - aux = 0 holds in every bounded solution.\<close>

definition aux_form :: "tableau_state \<Rightarrow> aux_relu \<Rightarrow> bool" where
  "aux_form S r \<longleftrightarrow>
     (\<forall>w\<in>tableau_bounded_models S. w (relu_aux r) = w (relu_f r) - w (relu_b r))"

type_synonym split_bounds = "(bound_side \<times> var \<times> real) list"

definition native_inactive_split :: "aux_relu \<Rightarrow> split_bounds" where
  "native_inactive_split r = [(Upper_Side, relu_b r, 0), (Upper_Side, relu_f r, 0)]"

definition native_active_split :: "aux_relu \<Rightarrow> split_bounds" where
  "native_active_split r = [(Lower_Side, relu_b r, 0), (Upper_Side, relu_aux r, 0)]"

text \<open>getCaseSplits with f's assignment known and no direction heuristic.\<close>

definition case_splits :: "tableau_state \<Rightarrow> aux_relu \<Rightarrow> split_bounds list" where
  "case_splits S r =
     (if 0 < tableau_candidate S (relu_f r)
      then [native_active_split r, native_inactive_split r] else [native_inactive_split r, native_active_split r])"

lemma case_splits_set: "set (case_splits S r) = {native_inactive_split r, native_active_split r}"
  by (auto simp: case_splits_def)

lemma decision_models_append:
  "decision_models (D @ E) = decision_models D \<inter> decision_models E"
  unfolding decision_models_def by (auto simp: ball_Un)

lemma decision_models_splits:
  "w \<in> decision_models (native_inactive_split r) \<longleftrightarrow> w (relu_b r) \<le> 0 \<and> w (relu_f r) \<le> 0"
  "w \<in> decision_models (native_active_split r) \<longleftrightarrow> 0 \<le> w (relu_b r) \<and> w (relu_aux r) \<le> 0"
  by (auto simp: decision_models_def native_inactive_split_def native_active_split_def)

section \<open>The children cover the parent\<close>

theorem relu_split_covers:
  assumes w: "w \<in> tableau_bounded_models S0" and aux: "aux_form S0 r"
      and relu: "relu_holds r w"
  shows "w \<in> decision_models (native_inactive_split r) \<or> w \<in> decision_models (native_active_split r)"
proof (cases "w (relu_b r) \<le> 0")
  case True
  then have "w (relu_f r) = 0"
    using relu by (simp add: relu_holds_def satisfies_relu_def relu_def)
  then show ?thesis using True by (simp add: decision_models_splits)
next
  case False
  then have "w (relu_f r) = w (relu_b r)"
    using relu by (simp add: relu_holds_def satisfies_relu_def relu_def)
  moreover have "w (relu_aux r) = w (relu_f r) - w (relu_b r)"
    using aux w unfolding aux_form_def by blast
  ultimately show ?thesis using False by (simp add: decision_models_splits)
qed

theorem zero_boundary_in_both:
  assumes "w \<in> tableau_bounded_models S0" "aux_form S0 r" "relu_holds r w"
      and "w (relu_b r) = 0"
  shows "w \<in> decision_models (native_inactive_split r)" and "w \<in> decision_models (native_active_split r)"
proof -
  have f: "w (relu_f r) = 0"
    using assms(3,4) by (simp add: relu_holds_def satisfies_relu_def)
  have "w (relu_aux r) = w (relu_f r) - w (relu_b r)"
    using assms(1,2) unfolding aux_form_def by blast
  then show "w \<in> decision_models (native_inactive_split r)" "w \<in> decision_models (native_active_split r)"
    using f assms(4) by (simp_all add: decision_models_splits)
qed

theorem relu_split_refutes:
  assumes aux: "aux_form S0 r" and r: "r \<in> set R"
      and inactive: "tableau_bounded_models S0 \<inter> relu_solutions R \<inter>
                       decision_models (D @ native_inactive_split r) = {}"
      and active: "tableau_bounded_models S0 \<inter> relu_solutions R \<inter>
                     decision_models (D @ native_active_split r) = {}"
  shows "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models D = {}"
proof (rule ccontr)
  assume "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models D \<noteq> {}"
  then obtain w where w: "w \<in> tableau_bounded_models S0" "w \<in> relu_solutions R"
    "w \<in> decision_models D" by blast
  have "relu_holds r w" using w(2) r unfolding relu_solutions_def by blast
  then have "w \<in> decision_models (native_inactive_split r) \<or> w \<in> decision_models (native_active_split r)"
    using relu_split_covers[OF w(1) aux] by blast
  then show False
    using inactive active w by (auto simp: decision_models_append)
qed

section \<open>The children are exact\<close>

lemma relu_nonneg:
  assumes "w \<in> tableau_bounded_models S0" "aux_form S0 r" "relu_holds r w"
  shows "0 \<le> w (relu_f r)" and "0 \<le> w (relu_aux r)"
proof -
  show f: "0 \<le> w (relu_f r)"
    using assms(3) by (simp add: relu_holds_def satisfies_relu_def)
  have "w (relu_aux r) = w (relu_f r) - w (relu_b r)"
    using assms(1,2) unfolding aux_form_def by blast
  then show "0 \<le> w (relu_aux r)"
    using assms(3) by (simp add: relu_holds_def satisfies_relu_def relu_def)
qed

theorem children_imply_relu:
  assumes w: "w \<in> tableau_bounded_models S0" and aux: "aux_form S0 r"
      and nonneg: "0 \<le> w (relu_f r)" "0 \<le> w (relu_aux r)"
  shows "w \<in> decision_models (native_inactive_split r) \<Longrightarrow> relu_holds r w"
    and "w \<in> decision_models (native_active_split r) \<Longrightarrow> relu_holds r w"
proof -
  have a: "w (relu_aux r) = w (relu_f r) - w (relu_b r)"
    using w aux unfolding aux_form_def by blast
  show "w \<in> decision_models (native_inactive_split r) \<Longrightarrow> relu_holds r w"
    using nonneg by (simp add: decision_models_splits relu_holds_def satisfies_relu_def relu_def)
  show "w \<in> decision_models (native_active_split r) \<Longrightarrow> relu_holds r w"
    using nonneg a by (simp add: decision_models_splits relu_holds_def satisfies_relu_def relu_def)
qed

section \<open>ReLU-aware branches\<close>

definition relu_branch_of :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> branch \<Rightarrow> bool" where
  "relu_branch_of S0 R Br \<longleftrightarrow>
     tableau_bounded_models (store_tableau (branch_store Br)) \<inter> relu_solutions R =
       tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br)"

lemma branch_of_relu: "branch_of S0 Br \<Longrightarrow> relu_branch_of S0 R Br"
  unfolding branch_of_def relu_branch_of_def by auto

definition relu_entailed :: "tableau_state \<Rightarrow> aux_relu list \<Rightarrow> bound_side \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bool" where
  "relu_entailed S R side x v \<longleftrightarrow>
     (\<forall>w\<in>tableau_bounded_models S \<inter> relu_solutions R. bound_holds side v (w x))"

theorem apply_relu_derived_branch:
  assumes br: "relu_branch_of S0 R Br" and x: "x \<in> carrier (store_tableau (branch_store Br))"
      and ent: "relu_entailed (store_tableau (branch_store Br)) R side x v"
  shows "relu_branch_of S0 R (apply_derived side x v Br)"
  using br tighten_bounded_models_subset[OF x, of side v] ent
  unfolding relu_branch_of_def apply_derived_def relu_entailed_def by auto

theorem apply_decision_relu_branch:
  assumes br: "relu_branch_of S0 R Br" and x: "x \<in> carrier (store_tableau (branch_store Br))"
  shows "relu_branch_of S0 R (apply_decision side x v Br)"
  using br tighten_bounded_models_subset[OF x, of side v]
  unfolding relu_branch_of_def apply_decision_def decision_models_def by auto

text \<open>The bounds f \<ge> 0 and aux \<ge> 0 of getEntailedTightenings are ReLU-entailed.\<close>

theorem relu_nonneg_entailed:
  assumes br: "relu_branch_of S0 R Br" and aux: "aux_form S0 r" and r: "r \<in> set R"
  shows "relu_entailed (store_tableau (branch_store Br)) R Lower_Side (relu_f r) 0"
    and "relu_entailed (store_tableau (branch_store Br)) R Lower_Side (relu_aux r) 0"
proof -
  have root: "\<And>w. w \<in> tableau_bounded_models (store_tableau (branch_store Br)) \<inter> relu_solutions R \<Longrightarrow>
      w \<in> tableau_bounded_models S0 \<and> relu_holds r w"
    using br r unfolding relu_branch_of_def relu_solutions_def by blast
  show "relu_entailed (store_tableau (branch_store Br)) R Lower_Side (relu_f r) 0"
    "relu_entailed (store_tableau (branch_store Br)) R Lower_Side (relu_aux r) 0"
    unfolding relu_entailed_def using root relu_nonneg[OF _ aux] by auto
qed

section \<open>Applying a split\<close>

fun apply_split :: "split_bounds \<Rightarrow> branch \<Rightarrow> branch" where
  "apply_split [] Br = Br"
| "apply_split ((side, x, v) # ts) Br = apply_split ts (apply_decision side x v Br)"

lemma apply_split_decisions:
  "branch_decisions (apply_split ts Br) = branch_decisions Br @ ts"
  by (induction ts Br rule: apply_split.induct) (simp_all add: apply_decision_def)

lemma apply_split_structure [simp]:
  "tableau_basics (store_tableau (branch_store (apply_split ts Br))) =
     tableau_basics (store_tableau (branch_store Br))"
  "tableau_nonbasics (store_tableau (branch_store (apply_split ts Br))) =
     tableau_nonbasics (store_tableau (branch_store Br))"
  "tableau_rows (store_tableau (branch_store (apply_split ts Br))) =
     tableau_rows (store_tableau (branch_store Br))"
  by (induction ts Br rule: apply_split.induct) (simp_all add: apply_decision_def)

definition targets_in :: "split_bounds \<Rightarrow> tableau_state \<Rightarrow> bool" where
  "targets_in ts S \<longleftrightarrow> (\<forall>(side, x, v)\<in>set ts. x \<in> carrier S)"

theorem apply_split_relu_branch:
  assumes "relu_branch_of S0 R Br" "targets_in ts (store_tableau (branch_store Br))"
  shows "relu_branch_of S0 R (apply_split ts Br)"
  using assms
proof (induction ts Br rule: apply_split.induct)
  case (1 Br)
  then show ?case by simp
next
  case (2 side x v ts Br)
  have x: "x \<in> carrier (store_tableau (branch_store Br))"
    using "2.prems"(2) unfolding targets_in_def by auto
  have br: "relu_branch_of S0 R (apply_decision side x v Br)"
    using apply_decision_relu_branch[OF "2.prems"(1) x] .
  have "targets_in ts (store_tableau (branch_store (apply_decision side x v Br)))"
    using "2.prems"(2) unfolding targets_in_def by (auto simp: apply_decision_def)
  then show ?case using "2.IH"[OF br] by simp
qed

theorem apply_split_branch:
  assumes "branch_of S0 Br" "targets_in ts (store_tableau (branch_store Br))"
  shows "branch_of S0 (apply_split ts Br)"
  using assms
proof (induction ts Br rule: apply_split.induct)
  case (1 Br)
  then show ?case by simp
next
  case (2 side x v ts Br)
  have x: "x \<in> carrier (store_tableau (branch_store Br))"
    using "2.prems"(2) unfolding targets_in_def by auto
  have br: "branch_of S0 (apply_decision side x v Br)"
    using apply_decision_branch[OF "2.prems"(1) x] .
  have "targets_in ts (store_tableau (branch_store (apply_decision side x v Br)))"
    using "2.prems"(2) unfolding targets_in_def by (auto simp: apply_decision_def)
  then show ?case using "2.IH"[OF br] by simp
qed

section \<open>Well-formed branches\<close>

text \<open>
  While no conflict is recorded the simplex invariant holds; once one is
  recorded the branch is refuted and no simplex step is taken.
\<close>

definition branch_ok :: "branch \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "branch_ok Br bs ns \<longleftrightarrow>
     conflict_sound (branch_store Br) \<and> conflict_complete (branch_store Br) \<and>
     (first_conflict (branch_store Br) = None \<longrightarrow>
        simplex_invariant (store_tableau (branch_store Br)) bs ns)"

lemma root_branch_ok:
  "simplex_invariant S bs ns \<Longrightarrow> branch_ok (root_branch S) bs ns"
  using root_branch_conflicts[of S bs ns] by (simp add: branch_ok_def root_branch_def)

lemma tighten_ok:
  assumes ok: "branch_ok Br bs ns" and x: "x \<in> carrier (store_tableau (branch_store Br))"
  shows "branch_ok (Br\<lparr>branch_store := fst (tighten_bound side x v (branch_store Br))\<rparr>) bs ns"
proof -
  let ?B = "branch_store Br"
  let ?B' = "fst (tighten_bound side x v ?B)"
  have cs: "conflict_sound ?B" and cc: "conflict_complete ?B"
    and inv: "first_conflict ?B = None \<Longrightarrow> simplex_invariant (store_tableau ?B) bs ns"
    using ok unfolding branch_ok_def by auto
  have cs': "conflict_sound ?B'" using tighten_conflict_sound[OF cs x] .
  have cc': "conflict_complete ?B'" using tighten_conflict_complete[OF cc] .
  have inv': "simplex_invariant (store_tableau ?B') bs ns" if none: "first_conflict ?B' = None"
  proof -
    have old: "first_conflict ?B = None"
      using none by (auto simp: tighten_conflict split: if_splits)
    show ?thesis
    proof (cases "stronger side (store_tableau ?B) x v")
      case False
      then show ?thesis using inv[OF old] by (simp add: tighten_weaker)
    next
      case True
      have xc: "x \<in> carrier (store_tableau ?B')" using x by simp
      have "\<not> crossed (store_tableau ?B') x"
        using cc' none xc unfolding conflict_complete_def by blast
      then have "\<not> crossed (with_bound side (store_tableau ?B) x v) x"
        using tighten_stronger(2)[OF True] unfolding crossed_def by simp
      then show ?thesis using tighten_invariant[OF inv[OF old] x] by blast
    qed
  qed
  show ?thesis
    using cs' cc' inv' unfolding branch_ok_def by simp
qed

lemma apply_split_ok:
  assumes "branch_ok Br bs ns" "targets_in ts (store_tableau (branch_store Br))"
  shows "branch_ok (apply_split ts Br) bs ns"
  using assms
proof (induction ts Br rule: apply_split.induct)
  case (1 Br)
  then show ?case by simp
next
  case (2 side x v ts Br)
  have x: "x \<in> carrier (store_tableau (branch_store Br))"
    using "2.prems"(2) unfolding targets_in_def by auto
  have ok: "branch_ok (apply_decision side x v Br) bs ns"
    using tighten_ok[OF "2.prems"(1) x, of side v]
    by (simp add: apply_decision_def branch_ok_def)
  have "targets_in ts (store_tableau (branch_store (apply_decision side x v Br)))"
    using "2.prems"(2) unfolding targets_in_def by (auto simp: apply_decision_def)
  then show ?case using "2.IH"[OF ok] by simp
qed

section \<open>Row tightening on a branch\<close>

text \<open>
  Each iteration of the native main loop, and so the first one after a split,
  runs Engine::explicitBasisBoundTightening (Engine.cpp:287-296, 2269-2294),
  the row bound tightener over the basic rows. Row rules keep the ReLU-aware branch, its
  decisions, row support and well-formedness.
\<close>

lemma entailed_relu_entailed: "entailed S side x v \<Longrightarrow> relu_entailed S R side x v"
  unfolding entailed_def relu_entailed_def by blast

lemma apply_rules_preserves:
  assumes "relu_branch_of S0 R Br" "branch_ok Br bs ns"
      "tableau_rows_supported (store_tableau (branch_store Br))"
  shows "relu_branch_of S0 R (apply_rules rls Br) \<and> branch_ok (apply_rules rls Br) bs ns \<and>
         branch_decisions (apply_rules rls Br) = branch_decisions Br \<and>
         tableau_rows_supported (store_tableau (branch_store (apply_rules rls Br)))"
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
    have x: "x \<in> carrier ?S" using rule_target_in_carrier[OF Cons.prems(3) True rb] .
    have ent: "relu_entailed ?S R side x v"
      using entailed_relu_entailed[OF row_rule_entailed[OF Cons.prems(3) True rb]] .
    let ?Br = "apply_derived side x v Br"
    have br: "relu_branch_of S0 R ?Br" using apply_relu_derived_branch[OF Cons.prems(1) x ent] .
    have ok: "branch_ok ?Br bs ns"
      using tighten_ok[OF Cons.prems(2) x, of side v] by (simp add: apply_derived_def)
    have sup: "tableau_rows_supported (store_tableau (branch_store ?Br))"
      using Cons.prems(3) unfolding tableau_rows_supported_def apply_derived_def by simp
    have dec: "branch_decisions ?Br = branch_decisions Br" by (simp add: apply_derived_def)
    show ?thesis using Cons.IH[OF br ok sup] True rb dec by simp
  qed
qed

definition all_row_rules :: "tableau_state \<Rightarrow> var list \<Rightarrow> row_rule list" where
  "all_row_rules S bs = concat (map (row_rules S) bs)"

definition tighten_rows :: "var list \<Rightarrow> branch \<Rightarrow> branch" where
  "tighten_rows bs Br = apply_rules (all_row_rules (store_tableau (branch_store Br)) bs) Br"

section \<open>Refuting a branch and one split expansion\<close>

text \<open>
  A branch is refuted by a conflict its own bounds already record, else by a
  conflict that row tightening records, else by an Infeasible run of the
  exact simplex loop. The tests are nested conditionals, so evaluation stops
  at the first that succeeds.
\<close>

definition refuted_after_rows :: "nat \<Rightarrow> branch \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "refuted_after_rows fuel Br bs ns \<longleftrightarrow>
     (if first_conflict (branch_store Br) \<noteq> None then True
      else fst (simplex_run fuel (store_tableau (branch_store Br)) bs ns) = Infeasible)"

definition branch_refuted :: "nat \<Rightarrow> branch \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "branch_refuted fuel Br bs ns \<longleftrightarrow>
     (if first_conflict (branch_store Br) \<noteq> None then True
      else refuted_after_rows fuel (tighten_rows bs Br) bs ns)"

lemma refuted_after_rows_sound:
  assumes br: "relu_branch_of S0 R Br" and ok: "branch_ok Br bs ns"
      and refuted: "refuted_after_rows fuel Br bs ns"
  shows "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) = {}"
proof -
  let ?S = "store_tableau (branch_store Br)"
  have "tableau_bounded_models ?S = {}"
  proof (cases "first_conflict (branch_store Br) = None")
    case False
    then show ?thesis
      using conflict_no_bounded_model ok unfolding branch_ok_def by blast
  next
    case True
    have inv: "simplex_invariant ?S bs ns" using ok True unfolding branch_ok_def by blast
    obtain r' S' bs' ns' where run: "simplex_run fuel ?S bs ns = (r', S', bs', ns')"
      by (cases "simplex_run fuel ?S bs ns") auto
    have "r' = Infeasible" using refuted True run unfolding refuted_after_rows_def by simp
    then show ?thesis using simplex_run_sound(4)[OF inv run] by blast
  qed
  then show ?thesis using br unfolding relu_branch_of_def by auto
qed

theorem branch_refuted_sound:
  assumes br: "relu_branch_of S0 R Br" and ok: "branch_ok Br bs ns"
      and sup: "tableau_rows_supported (store_tableau (branch_store Br))"
      and refuted: "branch_refuted fuel Br bs ns"
  shows "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) = {}"
proof (cases "first_conflict (branch_store Br) = None")
  case False
  then have "tableau_bounded_models (store_tableau (branch_store Br)) = {}"
    using conflict_no_bounded_model ok unfolding branch_ok_def by blast
  then show ?thesis using br unfolding relu_branch_of_def by auto
next
  case True
  let ?Br = "tighten_rows bs Br"
  have pres: "relu_branch_of S0 R ?Br" "branch_ok ?Br bs ns"
    "branch_decisions ?Br = branch_decisions Br"
    using apply_rules_preserves[OF br ok sup] unfolding tighten_rows_def by auto
  have "refuted_after_rows fuel ?Br bs ns"
    using refuted True unfolding branch_refuted_def by simp
  then show ?thesis using refuted_after_rows_sound[OF pres(1,2)] pres(3) by simp
qed

definition split_refutes :: "nat \<Rightarrow> aux_relu \<Rightarrow> branch \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> bool" where
  "split_refutes fuel r Br bs ns \<longleftrightarrow>
     list_all (\<lambda>ts. branch_refuted fuel (apply_split ts Br) bs ns)
       (case_splits (store_tableau (branch_store Br)) r)"

theorem split_refutes_sound:
  assumes br: "relu_branch_of S0 R Br" and ok: "branch_ok Br bs ns"
      and sup: "tableau_rows_supported (store_tableau (branch_store Br))"
      and aux: "aux_form S0 r" and r: "r \<in> set R"
      and vars: "relu_b r \<in> carrier (store_tableau (branch_store Br))"
        "relu_f r \<in> carrier (store_tableau (branch_store Br))"
        "relu_aux r \<in> carrier (store_tableau (branch_store Br))"
      and refutes: "split_refutes fuel r Br bs ns"
  shows "tableau_bounded_models S0 \<inter> relu_solutions R \<inter> decision_models (branch_decisions Br) = {}"
proof (rule relu_split_refutes[OF aux r])
  have child: "tableau_bounded_models S0 \<inter> relu_solutions R \<inter>
      decision_models (branch_decisions Br @ ts) = {}"
    if ts: "ts \<in> {native_inactive_split r, native_active_split r}" for ts
  proof -
    have targets: "targets_in ts (store_tableau (branch_store Br))"
      using ts vars unfolding targets_in_def by (auto simp: native_inactive_split_def native_active_split_def)
    have "branch_refuted fuel (apply_split ts Br) bs ns"
      using refutes ts case_splits_set[of "store_tableau (branch_store Br)" r]
      unfolding split_refutes_def list_all_iff by blast
    then show ?thesis
      using branch_refuted_sound[OF apply_split_relu_branch[OF br targets]
          apply_split_ok[OF ok targets]] sup
      by (simp add: apply_split_decisions tableau_rows_supported_def)
  qed
  show "tableau_bounded_models S0 \<inter> relu_solutions R \<inter>
          decision_models (branch_decisions Br @ native_inactive_split r) = {}"
    "tableau_bounded_models S0 \<inter> relu_solutions R \<inter>
          decision_models (branch_decisions Br @ native_active_split r) = {}"
    using child by auto
qed

text \<open>A feasible leaf whose candidate satisfies the ReLUs is a solution of the root.\<close>

theorem branch_feasible_solution:
  assumes br: "branch_of S0 Br" and inv: "simplex_invariant (store_tableau (branch_store Br)) bs ns"
      and run: "simplex_run fuel (store_tableau (branch_store Br)) bs ns = (Feasible, S', bs', ns')"
      and relus: "tableau_candidate S' \<in> relu_solutions R"
  shows "tableau_candidate S' \<in> tableau_bounded_models S0 \<inter> relu_solutions R"
  using simplex_run_sound(3)[OF inv run] br relus unfolding branch_of_def by blast

section \<open>Queries\<close>

text \<open>
  A query ReLU in native auxiliary form: the ReLU atom and an equation whose
  coefficients are exactly f - b - aux (as transformToUseAuxVariables writes
  it), with scalar 0.
\<close>

definition aux_pattern :: "aux_relu \<Rightarrow> (real \<times> var) list \<Rightarrow> bool" where
  "aux_pattern r ts \<longleftrightarrow>
     list_all (\<lambda>x. linexpr_coefficient ts x =
                    (if x = relu_f r then 1 else if x = relu_b r then -1
                     else if x = relu_aux r then -1 else 0))
       (remdups (map snd ts @ [relu_b r, relu_f r, relu_aux r]))"

definition relu_in_aux_form :: "nat \<Rightarrow> query \<Rightarrow> aux_relu \<Rightarrow> bool" where
  "relu_in_aux_form n Q r \<longleftrightarrow>
     relu_b r < n \<and> relu_f r < n \<and> relu_aux r < n \<and>
     distinct [relu_b r, relu_f r, relu_aux r] \<and>
     ReLU (relu_b r) (relu_f r) \<in> set (relu_atoms Q) \<and>
     list_ex (\<lambda>c. is_equation c \<and> aux_scalar c = 0 \<and> aux_pattern r (aux_terms c))
       (linear_atoms Q)"

lemma eval_aux_pattern:
  assumes pat: "aux_pattern r ts" and d: "distinct [relu_b r, relu_f r, relu_aux r]"
  shows "eval_terms w ts = w (relu_f r) - w (relu_b r) - w (relu_aux r)"
proof -
  let ?V = "set (map snd ts @ [relu_b r, relu_f r, relu_aux r])"
  have coef_all: "\<forall>x\<in>?V. linexpr_coefficient ts x =
      (if x = relu_f r then 1 else if x = relu_b r then -1 else if x = relu_aux r then -1 else 0)"
    using pat by (simp only: aux_pattern_def list_all_iff set_remdups)
  have coef: "\<And>x. x \<in> ?V \<Longrightarrow> linexpr_coefficient ts x =
      (if x = relu_f r then 1 else if x = relu_b r then -1 else if x = relu_aux r then -1 else 0)"
    using coef_all by blast
  have "eval_terms w ts = (\<Sum>j\<in>?V. linexpr_coefficient ts j * w j)"
    by (rule eval_terms_as_sum) auto
  also have "\<dots> = (\<Sum>j\<in>?V. (if relu_f r = j then w j else 0) - (if relu_b r = j then w j else 0) -
                             (if relu_aux r = j then w j else 0))"
    using d by (intro sum.cong) (auto simp: coef)
  also have "\<dots> = w (relu_f r) - w (relu_b r) - w (relu_aux r)"
    by (simp add: sum_subtractf sum.delta)
  finally show ?thesis .
qed

lemma relu_in_aux_form_aux:
  assumes ready: "engine_ready n Q" and form: "relu_in_aux_form n Q r"
  shows "aux_form (initial_tableau n Q) r"
  unfolding aux_form_def
proof
  fix w
  assume w: "w \<in> tableau_bounded_models (initial_tableau n Q)"
  obtain c where c: "c \<in> set (linear_atoms Q)" "is_equation c" "aux_scalar c = 0"
    "aux_pattern r (aux_terms c)"
    using form unfolding relu_in_aux_form_def list_ex_iff by blast
  have "satisfies_linear w c" using bounded_model_satisfies_linear_part(1)[OF ready w] c(1) by blast
  then have "eval_terms w (aux_terms c) = 0" using equation_iff[OF c(2)] c(3) by simp
  moreover have "distinct [relu_b r, relu_f r, relu_aux r]"
    using form unfolding relu_in_aux_form_def by blast
  ultimately show "w (relu_aux r) = w (relu_f r) - w (relu_b r)"
    using eval_aux_pattern[OF c(4)] by simp
qed

text \<open>
  One native split expansion at the root: the starting tableau of the query
  (auxiliary basis), the ReLU's two children in native order, each refuted by
  a recorded conflict or an Infeasible simplex run.
\<close>

definition solve_one_split :: "nat \<Rightarrow> nat \<Rightarrow> query \<Rightarrow> aux_relu \<Rightarrow> bool" where
  "solve_one_split fuel n Q r \<longleftrightarrow>
     engine_ready n Q \<and> bounds_consistent n Q \<and> relu_in_aux_form n Q r \<and>
     split_refutes fuel r (root_branch (initial_tableau n Q)) (initial_basics n Q) [0..<n]"

text \<open>The query-level conclusion of a refuted root split.\<close>

lemma relu_root_empty_unsat:
  assumes ready: "engine_ready n Q" and form: "relu_in_aux_form n Q r"
      and empty: "tableau_bounded_models (initial_tableau n Q) \<inter> relu_solutions [r] = {}"
  shows "unsatisfiable Q"
  unfolding unsatisfiable_def satisfiable_def
proof
  assume "\<exists>v. satisfies_query v Q"
  then obtain v where v: "satisfies_query v Q" by blast
  let ?w = "extend_aux n Q v"
  have lt: "relu_b r < n" "relu_f r < n"
    using form unfolding relu_in_aux_form_def by auto
  have "?w \<in> tableau_bounded_models (initial_tableau n Q)"
    using query_model_extends[OF ready] v unfolding satisfies_query_def by blast
  moreover have "relu_holds r ?w"
  proof -
    have "satisfies_relu v (relu_b r) (relu_f r)"
      using v form unfolding satisfies_query_def relu_in_aux_form_def by fastforce
    then show ?thesis using lt by (simp add: relu_holds_def satisfies_relu_def extend_aux_def)
  qed
  ultimately show False using empty by (auto simp: relu_solutions_def)
qed

text \<open>
  The native split at the root: if both children of a query's ReLU have no
  bounded solution, the query is unsatisfiable.
\<close>

corollary root_split_children_unsat:
  assumes ready: "engine_ready n Q" and form: "relu_in_aux_form n Q r"
      and inactive: "tableau_bounded_models (initial_tableau n Q) \<inter>
                       decision_models (native_inactive_split r) = {}"
      and active: "tableau_bounded_models (initial_tableau n Q) \<inter>
                     decision_models (native_active_split r) = {}"
  shows "unsatisfiable Q"
proof (rule relu_root_empty_unsat[OF ready form])
  have "tableau_bounded_models (initial_tableau n Q) \<inter> relu_solutions [r] \<inter> decision_models [] = {}"
    by (rule relu_split_refutes[OF relu_in_aux_form_aux[OF ready form]])
       (use inactive active in \<open>auto simp: decision_models_append\<close>)
  then show "tableau_bounded_models (initial_tableau n Q) \<inter> relu_solutions [r] = {}"
    by (simp add: decision_models_def)
qed

theorem solve_one_split_unsat:
  assumes "solve_one_split fuel n Q r"
  shows "unsatisfiable Q"
proof -
  let ?S = "initial_tableau n Q"
  have ready: "engine_ready n Q" and consistent: "bounds_consistent n Q"
    and form: "relu_in_aux_form n Q r"
    and refutes: "split_refutes fuel r (root_branch ?S) (initial_basics n Q) [0..<n]"
    using assms unfolding solve_one_split_def by auto
  have inv: "simplex_invariant ?S (initial_basics n Q) [0..<n]"
    using initial_tableau_invariant[OF ready consistent] .
  have lt: "relu_b r < n" "relu_f r < n" "relu_aux r < n"
    using form unfolding relu_in_aux_form_def by auto
  have vars: "relu_b r \<in> carrier (store_tableau (branch_store (root_branch ?S)))"
    "relu_f r \<in> carrier (store_tableau (branch_store (root_branch ?S)))"
    "relu_aux r \<in> carrier (store_tableau (branch_store (root_branch ?S)))"
    using lt by (simp_all add: root_branch_def initial_tableau_def)
  have "tableau_bounded_models ?S \<inter> relu_solutions [r] \<inter> decision_models [] = {}"
    using split_refutes_sound[OF branch_of_relu[OF root_branch_of] root_branch_ok[OF inv] _
        relu_in_aux_form_aux[OF ready form] _ vars refutes] inv
    by (simp add: root_branch_def simplex_invariant_def)
  then show ?thesis
    using relu_root_empty_unsat[OF ready form] by (simp add: decision_models_def)
qed

export_code solve_one_split split_refutes case_splits apply_split tighten_rows checking SML

end
