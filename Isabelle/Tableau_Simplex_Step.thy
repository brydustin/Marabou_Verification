theory Tableau_Simplex_Step
  imports Tableau_Pivot
begin

text \<open>
  One exact simplex step of Engine::performSimplexStep
  (src/engine/Engine.cpp:632-831) over the solved-row state, with every
  tolerance set to zero. Covered: the basic statuses of
  Tableau::computeBasicStatus (Tableau.cpp:425-452); the core
  sum-of-infeasibilities cost of CostFunctionManager::computeCoreCostFunction
  and computeBasicOOBCosts (CostFunctionManager.cpp:170-205, 264-297); entry
  eligibility (Tableau::eligibleForEntry, 617-666); the default Harris ratio
  test (Tableau::harrisRatioTest, 1057-1440, selected by
  USE_HARRIS_RATIO_TEST); the assignment update of
  Tableau::updateAssignmentForPivot (2345-2457); and the basis exchange of
  Tableau_Pivot. Not covered: the entering-variable strategy, incremental
  cost updates, the optimizing mode, tolerances and numerical recovery.
\<close>

section \<open>Statuses, costs and entry eligibility\<close>

datatype basic_status = Below_Lower | Between | Above_Upper

definition status_of :: "tableau_state \<Rightarrow> var \<Rightarrow> basic_status" where
  "status_of S x =
     (if tableau_upper S x < tableau_basic_value S x then Above_Upper
      else if tableau_basic_value S x < tableau_lower S x then Below_Lower
      else Between)"

definition core_cost :: "tableau_state \<Rightarrow> var \<Rightarrow> real" where
  "core_cost S x =
     (case status_of S x of Above_Upper \<Rightarrow> 1 | Below_Lower \<Rightarrow> -1 | Between \<Rightarrow> 0)"

text \<open>
  Native reduced costs are -c_B B\<inverse> A_j. A row coefficient is
  -(B\<inverse> A_j)_i, so the same number is the cost-weighted column of row
  coefficients.
\<close>

definition reduced_cost :: "tableau_state \<Rightarrow> var \<Rightarrow> real" where
  "reduced_cost S j =
     (\<Sum>i\<in>tableau_basics S. core_cost S i * row_coefficient (tableau_rows S i) j)"

datatype direction = Increase | Decrease

fun direction_sign :: "direction \<Rightarrow> real" where
  "direction_sign Increase = 1"
| "direction_sign Decrease = -1"

definition entering_direction :: "tableau_state \<Rightarrow> var \<Rightarrow> direction option" where
  "entering_direction S j =
     (if reduced_cost S j < 0 \<and> tableau_nonbasic_value S j < tableau_upper S j
      then Some Increase
      else if 0 < reduced_cost S j \<and> tableau_lower S j < tableau_nonbasic_value S j
      then Some Decrease
      else None)"

definition entering_range :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> real" where
  "entering_range S e d =
     (case d of
        Increase \<Rightarrow> tableau_upper S e - tableau_nonbasic_value S e
      | Decrease \<Rightarrow> tableau_nonbasic_value S e - tableau_lower S e)"

section \<open>Exact ratios\<close>

text \<open>
  Steps are measured by a nonnegative length \<tau>; the entering variable moves by
  direction_sign d * \<tau> and a basic x by step_rate S e d x * \<tau>. Native
  change ratios are the signed products direction_sign d * \<tau>. A basic in
  bounds is limited by the bound it approaches; a basic out of bounds is
  limited by the violated bound when it moves towards it and is unconstrained
  otherwise (the basicCost cases of harrisRatioTest).
\<close>

definition step_rate :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> var \<Rightarrow> real" where
  "step_rate S e d x = direction_sign d * row_coefficient (tableau_rows S x) e"

definition basic_limit :: "tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> real option" where
  "basic_limit S x rate =
     (case status_of S x of
        Between \<Rightarrow> Some (if 0 < rate then tableau_upper S x else tableau_lower S x)
      | Above_Upper \<Rightarrow> (if rate < 0 then Some (tableau_upper S x) else None)
      | Below_Lower \<Rightarrow> (if 0 < rate then Some (tableau_lower S x) else None))"

definition basic_ratio :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> var \<Rightarrow> real option" where
  "basic_ratio S e d x =
     (if step_rate S e d x = 0 then None
      else map_option (\<lambda>l. (l - tableau_basic_value S x) / step_rate S e d x)
             (basic_limit S x (step_rate S e d x)))"

definition status_kept :: "tableau_state \<Rightarrow> var \<Rightarrow> real \<Rightarrow> bool" where
  "status_kept S x w \<longleftrightarrow>
     (case status_of S x of
        Between \<Rightarrow> tableau_lower S x \<le> w \<and> w \<le> tableau_upper S x
      | Above_Upper \<Rightarrow> tableau_upper S x \<le> w
      | Below_Lower \<Rightarrow> w \<le> tableau_lower S x)"

lemma direction_sign_square [simp]: "direction_sign d * direction_sign d = 1"
  by (cases d) simp_all

lemma direction_sign_nonzero [simp]: "direction_sign d \<noteq> 0"
  by (cases d) simp_all

lemma basic_ratio_rate:
  "basic_ratio S e d x = Some r \<Longrightarrow> step_rate S e d x \<noteq> 0"
  by (auto simp: basic_ratio_def split: if_splits)

lemma basic_ratio_coefficient:
  "basic_ratio S e d x = Some r \<Longrightarrow> row_coefficient (tableau_rows S x) e \<noteq> 0"
  using basic_ratio_rate by (auto simp: step_rate_def)

lemma status_of_iff:
  "status_of S x = Above_Upper \<longleftrightarrow> tableau_upper S x < tableau_basic_value S x"
  "status_of S x = Below_Lower \<longleftrightarrow>
     \<not> tableau_upper S x < tableau_basic_value S x \<and>
     tableau_basic_value S x < tableau_lower S x"
  "status_of S x = Between \<longleftrightarrow>
     tableau_lower S x \<le> tableau_basic_value S x \<and>
     tableau_basic_value S x \<le> tableau_upper S x"
  by (auto simp: status_of_def)

lemma basic_limit_sign:
  assumes "basic_limit S x k = Some l"
  shows "0 \<le> (l - tableau_basic_value S x) * k"
proof (cases "status_of S x")
  case Below_Lower
  then show ?thesis
    using assms status_of_iff(2)[of S x]
    by (auto simp: basic_limit_def split: if_splits)
next
  case Between
  then show ?thesis
    using assms status_of_iff(3)[of S x]
    by (auto simp: basic_limit_def mult_nonpos_nonpos split: if_splits)
next
  case Above_Upper
  then show ?thesis
    using assms status_of_iff(1)[of S x]
    by (auto simp: basic_limit_def mult_nonpos_nonpos split: if_splits)
qed

lemma basic_ratio_nonneg:
  assumes "basic_ratio S e d x = Some r"
  shows "0 \<le> r"
proof -
  obtain l where l: "basic_limit S x (step_rate S e d x) = Some l"
    and r: "r = (l - tableau_basic_value S x) / step_rate S e d x"
    using assms by (auto simp: basic_ratio_def split: if_splits)
  show ?thesis
    using basic_limit_sign[OF l] unfolding r
    by (simp add: zero_le_divide_iff zero_le_mult_iff)
qed

lemma basic_ratio_step:
  assumes ratio: "\<And>r. basic_ratio S e d x = Some r \<Longrightarrow> \<tau> \<le> r" and tau: "0 \<le> \<tau>"
  shows "status_kept S x (tableau_basic_value S x + step_rate S e d x * \<tau>)"
proof -
  let ?v = "tableau_basic_value S x" and ?k = "step_rate S e d x"
  let ?l = "tableau_lower S x" and ?u = "tableau_upper S x"
  show ?thesis
  proof (cases "?k = 0")
    case True
    then show ?thesis
      by (auto simp: status_kept_def status_of_def split: basic_status.splits)
  next
    case nz: False
    consider (pos) "0 < ?k" | (neg) "?k < 0" using nz by linarith
    then show ?thesis
    proof cases
      case pos
      have up: "?v + ?k * \<tau> \<le> ?u" if "\<not> ?u < ?v" "\<not> ?v < ?l"
      proof -
        have "\<tau> \<le> (?u - ?v) / ?k"
          using ratio that pos nz
          by (simp add: basic_ratio_def basic_limit_def status_of_def)
        then show ?thesis using pos by (simp add: field_simps)
      qed
      have low: "?v + ?k * \<tau> \<le> ?l" if "?v < ?l" "\<not> ?u < ?v"
      proof -
        have "\<tau> \<le> (?l - ?v) / ?k"
          using ratio that pos nz
          by (simp add: basic_ratio_def basic_limit_def status_of_def)
        then show ?thesis using pos by (simp add: field_simps)
      qed
      have grows: "?v \<le> ?v + ?k * \<tau>" using pos tau by simp
      show ?thesis
        using up low grows
        by (auto simp: status_kept_def status_of_def split: basic_status.splits)
    next
      case neg
      have down: "?l \<le> ?v + ?k * \<tau>" if "\<not> ?u < ?v" "\<not> ?v < ?l"
      proof -
        have "\<tau> \<le> (?l - ?v) / ?k"
          using ratio that neg nz
          by (simp add: basic_ratio_def basic_limit_def status_of_def)
        then show ?thesis using neg by (simp add: field_simps)
      qed
      have high: "?u \<le> ?v + ?k * \<tau>" if "?u < ?v"
      proof -
        have "\<tau> \<le> (?u - ?v) / ?k"
          using ratio that neg nz
          by (simp add: basic_ratio_def basic_limit_def status_of_def)
        then show ?thesis using neg by (simp add: field_simps)
      qed
      have shrinks: "?v + ?k * \<tau> \<le> ?v" using neg tau by (simp add: mult_nonpos_nonneg)
      show ?thesis
        using down high shrinks
        by (auto simp: status_kept_def status_of_def split: basic_status.splits)
    qed
  qed
qed

lemma basic_ratio_reaches_limit:
  assumes "basic_ratio S e d x = Some r"
  shows "basic_limit S x (step_rate S e d x) =
           Some (tableau_basic_value S x + step_rate S e d x * r)"
proof -
  have k: "step_rate S e d x \<noteq> 0" using basic_ratio_rate[OF assms] .
  obtain l where l: "basic_limit S x (step_rate S e d x) = Some l"
    and r: "r = (l - tableau_basic_value S x) / step_rate S e d x"
    using assms by (auto simp: basic_ratio_def split: if_splits)
  have "l = tableau_basic_value S x + step_rate S e d x * r"
    using k unfolding r by simp
  then show ?thesis using l by simp
qed

lemma status_kept_limit:
  assumes "basic_limit S x k = Some l" "tableau_lower S x \<le> tableau_upper S x"
  shows "tableau_lower S x \<le> l \<and> l \<le> tableau_upper S x"
  using assms by (auto simp: basic_limit_def split: basic_status.splits if_splits)

section \<open>The exact Harris ratio test\<close>

text \<open>
  First pass: the minimal ratio over the basics (order-independent). Second
  pass: in native basic-index order, among the basics attaining it, the first
  with the largest pivot magnitude. The entering variable's own range wins
  ties, giving a bound flip ("fake pivot").
\<close>

fun min_ratio :: "(var \<Rightarrow> real option) \<Rightarrow> var list \<Rightarrow> real option" where
  "min_ratio f [] = None"
| "min_ratio f (x # xs) =
     (case f x of
        None \<Rightarrow> min_ratio f xs
      | Some r \<Rightarrow> (case min_ratio f xs of None \<Rightarrow> Some r | Some q \<Rightarrow> Some (min r q)))"

fun pick_leaving ::
  "(var \<Rightarrow> real option) \<Rightarrow> (var \<Rightarrow> real) \<Rightarrow> real \<Rightarrow> var list \<Rightarrow>
   (var \<times> real \<times> real) option \<Rightarrow> (var \<times> real \<times> real) option" where
  "pick_leaving f p t [] best = best"
| "pick_leaving f p t (x # xs) best =
     pick_leaving f p t xs
       (case f x of
          None \<Rightarrow> best
        | Some r \<Rightarrow>
            if r \<le> t \<and> (case best of None \<Rightarrow> 0 | Some (_, _, l) \<Rightarrow> l) < p x
            then Some (x, r, p x) else best)"

datatype ratio_choice = Bound_Flip real | Leaving var real

definition exact_harris_ratio_test ::
  "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> var list \<Rightarrow> ratio_choice" where
  "exact_harris_ratio_test S e d bs =
     (case min_ratio (basic_ratio S e d) bs of
        None \<Rightarrow> Bound_Flip (entering_range S e d)
      | Some t \<Rightarrow>
          if entering_range S e d \<le> t then Bound_Flip (entering_range S e d)
          else (case pick_leaving (basic_ratio S e d)
                       (\<lambda>x. \<bar>row_coefficient (tableau_rows S x) e\<bar>) t bs None of
                  None \<Rightarrow> Bound_Flip (entering_range S e d)
                | Some (x, r, _) \<Rightarrow> Leaving x r))"

lemma min_ratio_none:
  "min_ratio f xs = None \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x = None"
  by (induction f xs rule: min_ratio.induct) (auto split: option.splits)

lemma min_ratio_le:
  assumes "x \<in> set xs" "f x = Some r" "min_ratio f xs = Some q"
  shows "q \<le> r"
  using assms
proof (induction xs arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  consider (skip) "f y = None"
    | (single) s where "f y = Some s" "min_ratio f ys = None"
    | (both) s p where "f y = Some s" "min_ratio f ys = Some p"
    by (cases "f y"; cases "min_ratio f ys") auto
  then show ?case
  proof cases
    case skip
    then have "x \<noteq> y" "min_ratio f ys = Some q" using Cons.prems by auto
    then show ?thesis using Cons by auto
  next
    case single
    then have "x = y" using Cons.prems min_ratio_none[of f ys x] by auto
    then show ?thesis using Cons.prems single by simp
  next
    case both
    then have q: "q = min s p" using Cons.prems by simp
    show ?thesis
    proof (cases "x = y")
      case True
      then show ?thesis using Cons.prems both q by simp
    next
      case False
      then have "p \<le> r" using Cons both by auto
      then show ?thesis using q by simp
    qed
  qed
qed

lemma min_ratio_attained:
  "min_ratio f xs = Some q \<Longrightarrow> \<exists>x\<in>set xs. f x = Some q"
proof (induction xs arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  consider (skip) "f y = None"
    | (single) s where "f y = Some s" "min_ratio f ys = None"
    | (both) s p where "f y = Some s" "min_ratio f ys = Some p"
    by (cases "f y"; cases "min_ratio f ys") auto
  then show ?case
  proof cases
    case skip
    then show ?thesis using Cons by auto
  next
    case single
    then show ?thesis using Cons.prems by auto
  next
    case both
    then have "q = min s p" using Cons.prems by simp
    then show ?thesis using Cons.IH[OF both(2)] both(1) by (auto simp: min_def)
  qed
qed

lemma pick_leaving_from:
  "pick_leaving f p t xs best = Some (x, r, l) \<Longrightarrow>
     best = Some (x, r, l) \<or> (x \<in> set xs \<and> f x = Some r \<and> r \<le> t)"
  by (induction f p t xs best rule: pick_leaving.induct)
     (auto split: option.splits if_splits)

lemma pick_leaving_keeps:
  "best \<noteq> None \<Longrightarrow> pick_leaving f p t xs best \<noteq> None"
  by (induction f p t xs best rule: pick_leaving.induct)
     (auto split: option.splits)

lemma pick_leaving_finds:
  "x \<in> set xs \<Longrightarrow> f x = Some r \<Longrightarrow> r \<le> t \<Longrightarrow> 0 < p x \<Longrightarrow>
     pick_leaving f p t xs best \<noteq> None"
proof (induction f p t xs best rule: pick_leaving.induct)
  case (1 f p t best)
  then show ?case by simp
next
  case (2 f p t y xs best)
  show ?case
  proof (cases "y = x")
    case True
    have "(case f y of None \<Rightarrow> best
           | Some r \<Rightarrow> if r \<le> t \<and> (case best of None \<Rightarrow> 0 | Some (_, _, l) \<Rightarrow> l) < p y
                      then Some (y, r, p y) else best) \<noteq> None"
      using 2 True by (auto split: option.splits)
    then show ?thesis using pick_leaving_keeps by simp
  next
    case False
    then show ?thesis using 2 by simp
  qed
qed

section \<open>Applying a choice\<close>

definition move_entering :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> real \<Rightarrow> tableau_state" where
  "move_entering S e d \<tau> =
     update_nonbasic_assignment S e (tableau_nonbasic_value S e + direction_sign d * \<tau>)"

fun apply_choice :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> ratio_choice \<Rightarrow> tableau_state" where
  "apply_choice S e d (Bound_Flip \<tau>) = move_entering S e d \<tau>"
| "apply_choice S e d (Leaving b \<tau>) = exchange_basis (move_entering S e d \<tau>) b e"

definition step_within_ratios :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> real \<Rightarrow> bool" where
  "step_within_ratios S e d \<tau> \<longleftrightarrow>
     0 \<le> \<tau> \<and> \<tau> \<le> entering_range S e d \<and>
     (\<forall>x\<in>tableau_basics S. \<forall>r. basic_ratio S e d x = Some r \<longrightarrow> \<tau> \<le> r)"

fun choice_admissible :: "tableau_state \<Rightarrow> var \<Rightarrow> direction \<Rightarrow> ratio_choice \<Rightarrow> bool" where
  "choice_admissible S e d (Bound_Flip \<tau>) \<longleftrightarrow>
     step_within_ratios S e d \<tau> \<and> \<tau> = entering_range S e d"
| "choice_admissible S e d (Leaving b \<tau>) \<longleftrightarrow>
     step_within_ratios S e d \<tau> \<and> b \<in> tableau_basics S \<and> basic_ratio S e d b = Some \<tau>"

theorem exact_harris_admissible:
  assumes bs: "set bs = tableau_basics S"
      and range: "0 \<le> entering_range S e d"
  shows "choice_admissible S e d (exact_harris_ratio_test S e d bs)"
proof (cases "min_ratio (basic_ratio S e d) bs")
  case None
  then have "\<forall>x\<in>tableau_basics S. basic_ratio S e d x = None"
    using min_ratio_none bs by blast
  then show ?thesis
    using None range by (simp add: exact_harris_ratio_test_def step_within_ratios_def)
next
  case (Some t)
  have below: "\<And>x r. x \<in> tableau_basics S \<Longrightarrow> basic_ratio S e d x = Some r \<Longrightarrow> t \<le> r"
    using min_ratio_le Some bs by blast
  obtain y where y: "y \<in> set bs" "basic_ratio S e d y = Some t"
    using min_ratio_attained[OF Some] by blast
  have t0: "0 \<le> t" using basic_ratio_nonneg[OF y(2)] .
  show ?thesis
  proof (cases "entering_range S e d \<le> t")
    case True
    then show ?thesis
      using Some below range
      by (force simp: exact_harris_ratio_test_def step_within_ratios_def)
  next
    case False
    let ?p = "\<lambda>x. \<bar>row_coefficient (tableau_rows S x) e\<bar>"
    have "0 < ?p y" using basic_ratio_coefficient[OF y(2)] by simp
    then have found: "pick_leaving (basic_ratio S e d) ?p t bs None \<noteq> None"
      using pick_leaving_finds[of y bs "basic_ratio S e d" t t ?p None] y by simp
    then obtain z where z: "pick_leaving (basic_ratio S e d) ?p t bs None = Some z"
      by blast
    obtain x r l where "z = (x, r, l)" by (cases z)
    then have pick: "pick_leaving (basic_ratio S e d) ?p t bs None = Some (x, r, l)"
      using z by simp
    have x: "x \<in> set bs" "basic_ratio S e d x = Some r" "r \<le> t"
      using pick_leaving_from[OF pick] by auto
    have rt: "r = t" using below[of x r] x bs by simp
    show ?thesis
      using Some False pick x rt below t0
      by (auto simp: exact_harris_ratio_test_def step_within_ratios_def bs)
  qed
qed

section \<open>Effect of a step\<close>

lemma update_nonbasic_simps [simp]:
  "tableau_basics (update_nonbasic_assignment S x r) = tableau_basics S"
  "tableau_nonbasics (update_nonbasic_assignment S x r) = tableau_nonbasics S"
  "tableau_rows (update_nonbasic_assignment S x r) = tableau_rows S"
  "tableau_lower (update_nonbasic_assignment S x r) = tableau_lower S"
  "tableau_upper (update_nonbasic_assignment S x r) = tableau_upper S"
  by (simp_all add: update_nonbasic_assignment_def)

lemma update_coefficient_is_row_coefficient:
  "linexpr_coefficient (case r of Linexpr c ts \<Rightarrow> ts) x = row_coefficient r x"
  by (cases r) (simp add: row_coefficient_def)

lemma move_entering_values:
  "x \<in> tableau_basics S \<Longrightarrow>
     tableau_basic_value (move_entering S e d \<tau>) x =
       tableau_basic_value S x + step_rate S e d x * \<tau>"
  "tableau_nonbasic_value (move_entering S e d \<tau>) =
     (tableau_nonbasic_value S)(e := tableau_nonbasic_value S e + direction_sign d * \<tau>)"
  by (simp_all add: move_entering_def update_nonbasic_assignment_def
      update_coefficient_is_row_coefficient step_rate_def algebra_simps)

lemma move_entering_simps [simp]:
  "tableau_basics (move_entering S e d \<tau>) = tableau_basics S"
  "tableau_nonbasics (move_entering S e d \<tau>) = tableau_nonbasics S"
  "tableau_rows (move_entering S e d \<tau>) = tableau_rows S"
  "tableau_lower (move_entering S e d \<tau>) = tableau_lower S"
  "tableau_upper (move_entering S e d \<tau>) = tableau_upper S"
  by (simp_all add: move_entering_def)

lemma move_entering_models [simp]:
  "tableau_models (move_entering S e d \<tau>) = tableau_models S"
  "tableau_bounded_models (move_entering S e d \<tau>) = tableau_bounded_models S"
  by (simp_all add: tableau_models_def tableau_bounded_models_def)

lemma move_entering_rows_satisfied:
  "e \<in> tableau_nonbasics S \<Longrightarrow> tableau_rows_satisfied S \<Longrightarrow>
     tableau_rows_satisfied (move_entering S e d \<tau>)"
  unfolding move_entering_def by (rule update_nonbasic_preserves_rows)

lemma entering_within_bounds:
  assumes "0 \<le> \<tau>" "\<tau> \<le> entering_range S e d"
      and "tableau_lower S e \<le> tableau_nonbasic_value S e"
      "tableau_nonbasic_value S e \<le> tableau_upper S e"
  shows "tableau_lower S e \<le> tableau_nonbasic_value S e + direction_sign d * \<tau> \<and>
         tableau_nonbasic_value S e + direction_sign d * \<tau> \<le> tableau_upper S e"
  using assms by (cases d) (auto simp: entering_range_def)

definition tableau_bounds_ordered :: "tableau_state \<Rightarrow> bool" where
  "tableau_bounds_ordered S \<longleftrightarrow>
     (\<forall>x\<in>tableau_basics S \<union> tableau_nonbasics S. tableau_lower S x \<le> tableau_upper S x)"

text \<open>
  The native leaving target (updateAssignmentForPivot, 2413-2433): a leaving
  variable that increases goes to its upper bound unless it is below its lower
  bound; one that decreases goes to its lower bound unless it is above its
  upper bound.
\<close>

definition native_leaving_target :: "tableau_state \<Rightarrow> var \<Rightarrow> bool \<Rightarrow> real" where
  "native_leaving_target S b increases =
     (if increases
      then (if status_of S b = Below_Lower then tableau_lower S b else tableau_upper S b)
      else (if status_of S b = Above_Upper then tableau_upper S b else tableau_lower S b))"

lemma limit_is_native_target:
  assumes "basic_limit S b k = Some l" "k \<noteq> 0"
  shows "l = native_leaving_target S b (0 < k)"
  using assms
  by (auto simp: basic_limit_def native_leaving_target_def split: basic_status.splits if_splits)

theorem leaving_native_formulas:
  assumes ratio: "basic_ratio S e d b = Some \<tau>" and b: "b \<in> tableau_basics S"
  shows "tableau_basic_value (move_entering S e d \<tau>) b =
           native_leaving_target S b (0 < step_rate S e d b)"
    and "direction_sign d * \<tau> =
           (native_leaving_target S b (0 < step_rate S e d b) - tableau_basic_value S b) /
             row_coefficient (tableau_rows S b) e"
proof -
  have k: "step_rate S e d b \<noteq> 0" using basic_ratio_rate[OF ratio] .
  have lim: "basic_limit S b (step_rate S e d b) =
      Some (tableau_basic_value S b + step_rate S e d b * \<tau>)"
    using basic_ratio_reaches_limit[OF ratio] .
  have target: "tableau_basic_value S b + step_rate S e d b * \<tau> =
      native_leaving_target S b (0 < step_rate S e d b)"
    using limit_is_native_target[OF lim k] by simp
  show "tableau_basic_value (move_entering S e d \<tau>) b =
      native_leaving_target S b (0 < step_rate S e d b)"
    using move_entering_values(1)[OF b] target by simp
  have c: "row_coefficient (tableau_rows S b) e \<noteq> 0"
    using basic_ratio_coefficient[OF ratio] .
  define T where "T = native_leaving_target S b (0 < step_rate S e d b)"
  have "T - tableau_basic_value S b =
      row_coefficient (tableau_rows S b) e * (direction_sign d * \<tau>)"
    using target unfolding T_def[symmetric] by (simp add: step_rate_def algebra_simps)
  then show "direction_sign d * \<tau> =
      (native_leaving_target S b (0 < step_rate S e d b) - tableau_basic_value S b) /
        row_coefficient (tableau_rows S b) e"
    using c unfolding T_def[symmetric] by simp
qed

theorem choice_invariants:
  assumes sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
      and nb: "tableau_nonbasic_bounds_satisfied S" and ord: "tableau_bounds_ordered S"
      and e: "e \<in> tableau_nonbasics S" and adm: "choice_admissible S e d c"
  defines "S' \<equiv> apply_choice S e d c"
  shows "tableau_rows_supported S'"
    and "tableau_rows_satisfied S'"
    and "tableau_models S' = tableau_models S"
    and "tableau_bounded_models S' = tableau_bounded_models S"
    and "tableau_nonbasic_bounds_satisfied S'"
    and "tableau_bounds_ordered S'"
    and "\<forall>x\<in>tableau_basics S \<inter> tableau_basics S'.
           status_kept S x (tableau_candidate S' x)"
    and "e \<in> tableau_basics S' \<Longrightarrow>
           tableau_lower S e \<le> tableau_candidate S' e \<and>
           tableau_candidate S' e \<le> tableau_upper S e"
proof -
  obtain \<tau> where tau: "step_within_ratios S e d \<tau>"
    and shape: "c = Bound_Flip \<tau> \<or> (\<exists>b. c = Leaving b \<tau> \<and> b \<in> tableau_basics S \<and>
                  basic_ratio S e d b = Some \<tau>)"
    using adm by (cases c) auto
  let ?M = "move_entering S e d \<tau>"
  have tau0: "0 \<le> \<tau>" and taur: "\<tau> \<le> entering_range S e d"
    and within: "\<And>x r. x \<in> tableau_basics S \<Longrightarrow> basic_ratio S e d x = Some r \<Longrightarrow> \<tau> \<le> r"
    using tau unfolding step_within_ratios_def by auto
  have disj: "e \<notin> tableau_basics S"
    using sup e unfolding tableau_rows_supported_def by blast
  have e_bounds: "tableau_lower S e \<le> tableau_nonbasic_value S e"
    "tableau_nonbasic_value S e \<le> tableau_upper S e"
    using nb e unfolding tableau_nonbasic_bounds_satisfied_def by auto
  have e_new: "tableau_lower S e \<le> tableau_nonbasic_value S e + direction_sign d * \<tau> \<and>
      tableau_nonbasic_value S e + direction_sign d * \<tau> \<le> tableau_upper S e"
    using entering_within_bounds[OF tau0 taur e_bounds] .
  have M_sup: "tableau_rows_supported ?M"
    using sup unfolding tableau_rows_supported_def by simp
  have M_rows: "tableau_rows_satisfied ?M"
    using move_entering_rows_satisfied[OF e rows] .
  have M_nb: "tableau_nonbasic_bounds_satisfied ?M"
    using nb e_new unfolding tableau_nonbasic_bounds_satisfied_def
    by (auto simp: move_entering_values)
  have kept: "\<And>x. x \<in> tableau_basics S \<Longrightarrow>
      status_kept S x (tableau_basic_value ?M x)"
    using basic_ratio_step within tau0 by (simp add: move_entering_values)
  have M_cand: "\<And>x. x \<in> tableau_basics S \<Longrightarrow> tableau_candidate ?M x = tableau_basic_value ?M x"
    by (simp add: tableau_candidate_def)
  show "tableau_rows_supported S'" "tableau_rows_satisfied S'"
    "tableau_models S' = tableau_models S" "tableau_bounded_models S' = tableau_bounded_models S"
    "tableau_nonbasic_bounds_satisfied S'" "tableau_bounds_ordered S'"
    "\<forall>x\<in>tableau_basics S \<inter> tableau_basics S'. status_kept S x (tableau_candidate S' x)"
    "e \<in> tableau_basics S' \<Longrightarrow>
       tableau_lower S e \<le> tableau_candidate S' e \<and> tableau_candidate S' e \<le> tableau_upper S e"
  proof -
    consider (flip) "c = Bound_Flip \<tau>"
      | (pivot) b where "c = Leaving b \<tau>" "b \<in> tableau_basics S" "basic_ratio S e d b = Some \<tau>"
      using shape by blast
    then have "tableau_rows_supported S' \<and> tableau_rows_satisfied S' \<and>
      tableau_models S' = tableau_models S \<and> tableau_bounded_models S' = tableau_bounded_models S \<and>
      tableau_nonbasic_bounds_satisfied S' \<and> tableau_bounds_ordered S' \<and>
      (\<forall>x\<in>tableau_basics S \<inter> tableau_basics S'. status_kept S x (tableau_candidate S' x)) \<and>
      (e \<in> tableau_basics S' \<longrightarrow>
         tableau_lower S e \<le> tableau_candidate S' e \<and> tableau_candidate S' e \<le> tableau_upper S e)"
    proof cases
      case flip
      then have S': "S' = ?M" by (simp add: S'_def)
      show ?thesis
        using M_sup M_rows M_nb kept M_cand disj ord
        unfolding S' by (simp add: tableau_bounds_ordered_def)
    next
      case (pivot b)
      have S': "S' = exchange_basis ?M b e" using pivot by (simp add: S'_def)
      have p: "pivot_admissible ?M b e"
        using pivot e basic_ratio_coefficient[OF pivot(3)]
        by (simp add: pivot_admissible_def)
      have b_target: "tableau_basic_value ?M b =
          native_leaving_target S b (0 < step_rate S e d b)"
        using leaving_native_formulas(1)[OF pivot(3) pivot(2)] .
      have b_limit: "basic_limit S b (step_rate S e d b) = Some (tableau_basic_value ?M b)"
        using basic_ratio_reaches_limit[OF pivot(3)] move_entering_values(1)[OF pivot(2)]
        by simp
      have b_ord: "tableau_lower S b \<le> tableau_upper S b"
        using ord pivot(2) unfolding tableau_bounds_ordered_def by blast
      have b_in: "tableau_lower ?M b \<le> tableau_basic_value ?M b \<and>
          tableau_basic_value ?M b \<le> tableau_upper ?M b"
        using status_kept_limit[OF b_limit b_ord] by simp
      have cand: "tableau_candidate S' = tableau_candidate ?M"
        unfolding S' using exchange_candidate[OF p M_sup] .
      have facts: "b \<noteq> e" using pivot(2) disj by blast
      have carrier: "tableau_basics S' \<union> tableau_nonbasics S' = tableau_basics S \<union> tableau_nonbasics S"
        unfolding S' using exchange_carrier[OF p] by simp
      show ?thesis
      proof (intro conjI)
        show "tableau_rows_supported S'"
          unfolding S' using exchange_rows_supported[OF p M_sup] .
        show "tableau_rows_satisfied S'"
          unfolding S' using exchange_rows_satisfied[OF p M_sup M_rows] .
        show "tableau_models S' = tableau_models S"
          unfolding S' using exchange_models[OF p M_sup] by simp
        show "tableau_bounded_models S' = tableau_bounded_models S"
          unfolding S' using exchange_bounded_models[OF p M_sup] by simp
        show "tableau_nonbasic_bounds_satisfied S'"
          unfolding S' using exchange_nonbasic_bounds[OF M_nb] b_in by simp
        show "tableau_bounds_ordered S'"
          using ord carrier unfolding tableau_bounds_ordered_def
          by (simp add: S')
        show "\<forall>x\<in>tableau_basics S \<inter> tableau_basics S'. status_kept S x (tableau_candidate S' x)"
          using kept M_cand cand by (simp add: S')
        show "e \<in> tableau_basics S' \<longrightarrow>
            tableau_lower S e \<le> tableau_candidate S' e \<and> tableau_candidate S' e \<le> tableau_upper S e"
          using e_new cand disj by (simp add: tableau_candidate_def move_entering_values)
      qed
    qed
    then show "tableau_rows_supported S'" "tableau_rows_satisfied S'"
      "tableau_models S' = tableau_models S" "tableau_bounded_models S' = tableau_bounded_models S"
      "tableau_nonbasic_bounds_satisfied S'" "tableau_bounds_ordered S'"
      "\<forall>x\<in>tableau_basics S \<inter> tableau_basics S'. status_kept S x (tableau_candidate S' x)"
      "e \<in> tableau_basics S' \<Longrightarrow>
         tableau_lower S e \<le> tableau_candidate S' e \<and> tableau_candidate S' e \<le> tableau_upper S e"
      by blast+
  qed
qed

section \<open>Terminal cases\<close>

lemma eval_terms_as_sum:
  assumes "finite V" "snd ` set ts \<subseteq> V"
  shows "eval_terms v ts = (\<Sum>j\<in>V. linexpr_coefficient ts j * v j)"
  using assms(2)
proof (induction ts)
  case Nil
  then show ?case by simp
next
  case (Cons p ts)
  obtain a x where p: "p = (a, x)" by (cases p)
  have x: "x \<in> V" and rest: "snd ` set ts \<subseteq> V" using Cons.prems p by auto
  have delta: "\<And>j. (if x = j then a else 0) * v j = (if x = j then a * v j else 0)"
    by simp
  have "(\<Sum>j\<in>V. linexpr_coefficient (p # ts) j * v j) =
        (\<Sum>j\<in>V. (if x = j then a * v j else 0)) + (\<Sum>j\<in>V. linexpr_coefficient ts j * v j)"
    by (simp add: p sum.distrib[symmetric] distrib_right delta)
  also have "(\<Sum>j\<in>V. (if x = j then a * v j else 0)) = a * v x"
    using x assms(1) by (simp add: sum.delta)
  finally show ?case using Cons.IH[OF rest] p by simp
qed

lemma eval_linexpr_difference:
  assumes "finite V" "linexpr_vars r \<subseteq> V"
  shows "eval_linexpr v r - eval_linexpr w r = (\<Sum>j\<in>V. row_coefficient r j * (v j - w j))"
proof -
  have ts: "snd ` set (row_terms r) \<subseteq> V" using assms(2) by (simp add: linexpr_vars_parts)
  show ?thesis
    using eval_terms_as_sum[OF assms(1) ts, of v] eval_terms_as_sum[OF assms(1) ts, of w]
    by (simp add: eval_linexpr_parts row_coefficient_def sum_subtractf[symmetric]
        right_diff_distrib)
qed

text \<open>
  The branch of performSimplexStep that throws InfeasibleQueryException
  (Engine.cpp:776-786): a basic is out of bounds, the cost function is fresh
  and no nonbasic is eligible. Then the rows and bounds have no real solution.
\<close>

theorem no_entering_candidate_infeasible:
  assumes sup: "tableau_rows_supported S"
      and finB: "finite (tableau_basics S)" and finN: "finite (tableau_nonbasics S)"
      and rows: "tableau_rows_satisfied S"
      and nb: "tableau_nonbasic_bounds_satisfied S"
      and oob: "\<exists>x\<in>tableau_basics S. status_of S x \<noteq> Between"
      and none: "\<forall>j\<in>tableau_nonbasics S. entering_direction S j = None"
  shows "tableau_bounded_models S = {}"
proof (rule ccontr)
  assume "tableau_bounded_models S \<noteq> {}"
  then obtain v where v: "v \<in> tableau_bounded_models S" by blast
  let ?B = "tableau_basics S" and ?N = "tableau_nonbasics S"
  let ?w = "tableau_candidate S"
  let ?c = "core_cost S"
  let ?C = "\<lambda>i j. row_coefficient (tableau_rows S i) j"
  have vm: "v \<in> tableau_models S"
    and vb: "\<And>x. x \<in> ?B \<union> ?N \<Longrightarrow> tableau_lower S x \<le> v x \<and> v x \<le> tableau_upper S x"
    using v unfolding tableau_bounded_models_def by auto
  have wm: "?w \<in> tableau_models S"
    using rows rows_satisfied_iff_candidate[OF sup] by simp
  have support: "\<And>i. i \<in> ?B \<Longrightarrow> linexpr_vars (tableau_rows S i) \<subseteq> ?N"
    using sup unfolding tableau_rows_supported_def by blast
  have disj: "?B \<inter> ?N = {}" using sup unfolding tableau_rows_supported_def by blast
  have diff: "\<And>i. i \<in> ?B \<Longrightarrow> v i - ?w i = (\<Sum>j\<in>?N. ?C i j * (v j - ?w j))"
  proof -
    fix i
    assume i: "i \<in> ?B"
    have "v i = eval_linexpr v (tableau_rows S i)" "?w i = eval_linexpr ?w (tableau_rows S i)"
      using vm wm i unfolding tableau_models_def by blast+
    then show "v i - ?w i = (\<Sum>j\<in>?N. ?C i j * (v j - ?w j))"
      using eval_linexpr_difference[OF finN support[OF i]] by simp
  qed
  have "(\<Sum>i\<in>?B. ?c i * (v i - ?w i)) = (\<Sum>i\<in>?B. \<Sum>j\<in>?N. ?c i * (?C i j * (v j - ?w j)))"
    using diff by (simp add: sum_distrib_left)
  also have "\<dots> = (\<Sum>j\<in>?N. \<Sum>i\<in>?B. ?c i * ?C i j * (v j - ?w j))"
    by (subst sum.swap) (simp add: mult.assoc)
  also have "\<dots> = (\<Sum>j\<in>?N. reduced_cost S j * (v j - ?w j))"
    by (simp add: reduced_cost_def sum_distrib_right)
  finally have swap: "(\<Sum>i\<in>?B. ?c i * (v i - ?w i)) =
      (\<Sum>j\<in>?N. reduced_cost S j * (v j - ?w j))" .
  have "0 \<le> (\<Sum>j\<in>?N. reduced_cost S j * (v j - ?w j))"
  proof (rule sum_nonneg)
    fix j
    assume j: "j \<in> ?N"
    have wj: "?w j = tableau_nonbasic_value S j"
      using j disj by (auto simp: tableau_candidate_def)
    have jb: "tableau_lower S j \<le> tableau_nonbasic_value S j"
      "tableau_nonbasic_value S j \<le> tableau_upper S j"
      using nb j unfolding tableau_nonbasic_bounds_satisfied_def by auto
    have vj: "tableau_lower S j \<le> v j" "v j \<le> tableau_upper S j" using vb j by auto
    have nj: "entering_direction S j = None" using none j by blast
    consider "reduced_cost S j < 0" | "reduced_cost S j = 0" | "0 < reduced_cost S j"
      by linarith
    then show "0 \<le> reduced_cost S j * (v j - ?w j)"
    proof cases
      case 1
      then have "tableau_nonbasic_value S j = tableau_upper S j"
        using nj jb by (auto simp: entering_direction_def split: if_splits)
      then show ?thesis using 1 vj wj by (simp add: mult_nonpos_nonpos)
    next
      case 2
      then show ?thesis by simp
    next
      case 3
      then have "tableau_nonbasic_value S j = tableau_lower S j"
        using nj jb by (auto simp: entering_direction_def split: if_splits)
      then show ?thesis using 3 vj wj by simp
    qed
  qed
  moreover have "(\<Sum>i\<in>?B. ?c i * (v i - ?w i)) < (\<Sum>i\<in>?B. 0)"
  proof (rule sum_strict_mono_ex1[OF finB])
    have strict: "\<And>i. i \<in> ?B \<Longrightarrow> status_of S i \<noteq> Between \<Longrightarrow> ?c i * (v i - ?w i) < 0"
    proof -
      fix i
      assume i: "i \<in> ?B" and st: "status_of S i \<noteq> Between"
      have wi: "?w i = tableau_basic_value S i" using i by (simp add: tableau_candidate_def)
      have vi: "tableau_lower S i \<le> v i" "v i \<le> tableau_upper S i" using vb i by auto
      show "?c i * (v i - ?w i) < 0"
        using st vi wi
        by (auto simp: core_cost_def status_of_def split: if_splits)
    qed
    show "\<forall>i\<in>?B. ?c i * (v i - ?w i) \<le> 0"
    proof
      fix i
      assume i: "i \<in> ?B"
      show "?c i * (v i - ?w i) \<le> 0"
      proof (cases "status_of S i = Between")
        case True
        then show ?thesis by (simp add: core_cost_def)
      next
        case False
        then show ?thesis using strict[OF i] by simp
      qed
    qed
    show "\<exists>i\<in>?B. ?c i * (v i - ?w i) < 0"
      using oob strict by blast
  qed
  ultimately show False using swap by simp
qed

theorem all_between_candidate_feasible:
  assumes sup: "tableau_rows_supported S" and rows: "tableau_rows_satisfied S"
      and nb: "tableau_nonbasic_bounds_satisfied S"
      and inb: "\<forall>x\<in>tableau_basics S. status_of S x = Between"
  shows "tableau_candidate S \<in> tableau_bounded_models S"
proof -
  have "tableau_candidate S \<in> tableau_models S"
    using rows rows_satisfied_iff_candidate[OF sup] by simp
  moreover have "\<forall>x\<in>tableau_basics S \<union> tableau_nonbasics S.
      tableau_lower S x \<le> tableau_candidate S x \<and> tableau_candidate S x \<le> tableau_upper S x"
  proof
    fix x
    assume x: "x \<in> tableau_basics S \<union> tableau_nonbasics S"
    show "tableau_lower S x \<le> tableau_candidate S x \<and> tableau_candidate S x \<le> tableau_upper S x"
    proof (cases "x \<in> tableau_basics S")
      case True
      then show ?thesis
        using inb by (auto simp: tableau_candidate_def status_of_def split: if_splits)
    next
      case False
      then show ?thesis
        using x nb by (auto simp: tableau_candidate_def tableau_nonbasic_bounds_satisfied_def)
    qed
  qed
  ultimately show ?thesis unfolding tableau_bounded_models_def by blast
qed

end
