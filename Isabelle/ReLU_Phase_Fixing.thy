theory ReLU_Phase_Fixing
  imports Rational_Linear_Implication ReLU_Splitting
begin

text \<open>
  Marabou can fix a ReLU phase before search begins. With preprocessing
  disabled, Engine::invokePreprocessor calls
  Preprocessor::informConstraintsOfInitialBounds. It notifies each constraint
  of its initial bounds before any bound manager exists
  (ReluConstraint::checkIfLowerBoundUpdateFixesPhase and
  checkIfUpperBoundUpdateFixesPhase, ReluConstraint.cpp 125-146), so no PLC
  lemma is recorded. Engine::solve then calls applyAllValidConstraintCaseSplits.
  Engine::applySplit adds every strictly tighter bound of the phase's split
  as a new ground bound without an explanation (Engine.cpp 2108-2134).
  The native proof checker never sees those bounds.

  Here the phase is justified exactly instead. A checked linear implication
  derives the phase condition from the query plus the two inequalities that
  every ReLU satisfies, y >= 0 and y >= x. The phase's split query then
  replaces the query. The native epsilon tests (for example b >= -epsilon
  counting as active) are not trusted: the premise bound must hold exactly.
\<close>

definition relu_hull_query :: "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_query" where
  "relu_hull_query Q x y = Q\<lparr>rat_linear_atoms :=
     RatGe (RatExpr 0 [(1, y)]) 0 # RatGe (RatExpr 0 [(1, y), (-1, x)]) 0 #
     rat_linear_atoms Q\<rparr>"

lemma relu_hull_query_models:
  assumes member: "ReLU x y \<in> set (rat_relu_atoms Q)"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_query v (embed_query (relu_hull_query Q x y))"
proof -
  have "satisfies_relu v x y"
    using query_relu[OF model] member by (simp add: embed_query_def)
  then have "0 \<le> v y" "v x \<le> v y"
    by (auto simp: satisfies_relu_def relu_def)
  then show ?thesis
    using model by (simp add: relu_hull_query_def embed_query_def satisfies_query_def)
qed

text \<open>
  The phase condition is a single bound. Active: x >= l with 0 <= l, or
  y >= l with 0 < l. Inactive: x <= u or y <= u, with u <= 0.
\<close>

fun active_phase_bound :: "var \<Rightarrow> var \<Rightarrow> rat_bound \<Rightarrow> bool" where
  "active_phase_bound x y (RatLower z l) \<longleftrightarrow> (z = x \<and> 0 \<le> l) \<or> (z = y \<and> 0 < l)"
| "active_phase_bound x y (RatUpper z u) \<longleftrightarrow> False"

fun inactive_phase_bound :: "var \<Rightarrow> var \<Rightarrow> rat_bound \<Rightarrow> bool" where
  "inactive_phase_bound x y (RatUpper z u) \<longleftrightarrow> (z = x \<or> z = y) \<and> u \<le> 0"
| "inactive_phase_bound x y (RatLower z l) \<longleftrightarrow> False"

definition check_relu_fixed_active ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_bound \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_relu_fixed_active Q x y b ws \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and> active_phase_bound x y b \<and>
     check_linear_bound (relu_hull_query Q x y) b ws"

definition check_relu_fixed_inactive ::
  "rat_query \<Rightarrow> var \<Rightarrow> var \<Rightarrow> rat_bound \<Rightarrow> rat list \<Rightarrow> bool" where
  "check_relu_fixed_inactive Q x y b ws \<longleftrightarrow>
     ReLU x y \<in> set (rat_relu_atoms Q) \<and> inactive_phase_bound x y b \<and>
     check_linear_bound (relu_hull_query Q x y) b ws"

lemma phase_bound_holds:
  assumes member: "ReLU x y \<in> set (rat_relu_atoms Q)"
      and checked: "check_linear_bound (relu_hull_query Q x y) b ws"
      and model: "satisfies_query v (embed_query Q)"
  shows "satisfies_bound v (embed_bound b)" "satisfies_relu v x y"
proof -
  show "satisfies_bound v (embed_bound b)"
    by (rule check_linear_bound_sound[OF checked relu_hull_query_models[OF member model]])
  show "satisfies_relu v x y"
    using query_relu[OF model] member by (simp add: embed_query_def)
qed

theorem check_relu_fixed_active_sound:
  assumes checked: "check_relu_fixed_active Q x y b ws"
      and model: "satisfies_query v (embed_query Q)"
  shows "0 \<le> v x \<and> v y = v x"
proof -
  have member: "ReLU x y \<in> set (rat_relu_atoms Q)"
      and phase: "active_phase_bound x y b"
      and implied: "check_linear_bound (relu_hull_query Q x y) b ws"
    using checked by (simp_all add: check_relu_fixed_active_def)
  note facts = phase_bound_holds[OF member implied model]
  obtain z l where b: "b = RatLower z l"
    using phase by (cases b) auto
  have lower: "of_rat l \<le> v z" using facts(1) by (simp add: b)
  have relu_eq: "v y = max 0 (v x)" using facts(2) by (simp add: satisfies_relu_def relu_def)
  consider "z = x" "0 \<le> l" | "z = y" "0 < l" using phase by (auto simp: b)
  then show ?thesis
  proof cases
    case 1
    then have "0 \<le> v x" using lower by (metis zero_le_of_rat_iff order.trans)
    then show ?thesis using relu_eq by simp
  next
    case 2
    then have "0 < v y" using lower by (metis zero_less_of_rat_iff order_less_le_trans)
    then show ?thesis using relu_eq by (auto simp: max_def split: if_splits)
  qed
qed

theorem check_relu_fixed_inactive_sound:
  assumes checked: "check_relu_fixed_inactive Q x y b ws"
      and model: "satisfies_query v (embed_query Q)"
  shows "v x \<le> 0 \<and> v y = 0"
proof -
  have member: "ReLU x y \<in> set (rat_relu_atoms Q)"
      and phase: "inactive_phase_bound x y b"
      and implied: "check_linear_bound (relu_hull_query Q x y) b ws"
    using checked by (simp_all add: check_relu_fixed_inactive_def)
  note facts = phase_bound_holds[OF member implied model]
  obtain z u where b: "b = RatUpper z u"
    using phase by (cases b) auto
  have upper: "v z \<le> of_rat u" and nonpos: "u \<le> 0" and which: "z = x \<or> z = y"
    using facts(1) phase by (simp_all add: b)
  have "v z \<le> 0" using upper nonpos by (metis of_rat_le_0_iff order.trans)
  moreover have relu_eq: "v y = max 0 (v x)" using facts(2) by (simp add: satisfies_relu_def relu_def)
  ultimately show ?thesis using which by (auto simp: max_def split: if_splits)
qed

theorem relu_fixed_active_models:
  assumes "check_relu_fixed_active Q x y b ws"
  shows "models (active_split (embed_query Q) x y) = models (embed_query Q)"
  using check_relu_fixed_active_sound[OF assms]
  by (auto simp: models_def satisfies_active_split_iff)

theorem relu_fixed_inactive_models:
  assumes "check_relu_fixed_inactive Q x y b ws"
  shows "models (inactive_split (embed_query Q) x y) = models (embed_query Q)"
  using check_relu_fixed_inactive_sound[OF assms]
  by (auto simp: models_def satisfies_inactive_split_iff)

corollary unsatisfiable_relu_fixed_active:
  assumes "check_relu_fixed_active Q x y b ws"
      and "unsatisfiable (active_split (embed_query Q) x y)"
  shows "unsatisfiable (embed_query Q)"
  using relu_fixed_active_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

corollary unsatisfiable_relu_fixed_inactive:
  assumes "check_relu_fixed_inactive Q x y b ws"
      and "unsatisfiable (inactive_split (embed_query Q) x y)"
  shows "unsatisfiable (embed_query Q)"
  using relu_fixed_inactive_models[OF assms(1)] assms(2)
  by (simp add: unsatisfiable_iff_models_empty)

text \<open>
  The exact signs are necessary. The ReLU holds at x = -1/2, y = 0, where
  x >= -1/2 and y >= 0 are true but the active phase y = x fails; so neither
  a negative input bound nor a zero output bound fixes the active phase.
  At x = y = 1/2, x <= 1/2 is true but the inactive phase y = 0 fails.
\<close>

lemma phase_premises_need_exact_signs:
  "relu (-1/2 :: real) = 0 \<and> (0 :: real) \<noteq> -1/2"
  "relu (1/2 :: real) = 1/2 \<and> (1/2 :: real) \<noteq> 0"
  by (simp_all add: relu_def)

end
