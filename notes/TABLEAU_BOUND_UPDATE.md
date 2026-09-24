# Bound application and local conflicts

Completed on 2026-09-24 (milestone 27). This is milestone 3 of the audit's
solver-calculus roadmap ([PROJECT_DIRECTION_AUDIT.md](PROJECT_DIRECTION_AUDIT.md),
section 8). It models how Marabou applies a new bound to its tableau:
* when the bound changes anything;
* what it does to the assignment;
* how a crossing bound is recorded as a conflict;
* why a split bound must be kept apart from a derived one.

All comparisons are exact. This is an abstraction of the native code, not a
proof about it.

## Native code covered

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`, `src/engine/`:

| Native code | Lines | HOL counterpart |
| --- | --- | --- |
| `BoundManager::setLowerBound/setUpperBound`: change only on a strictly stronger value, mark pending, record the first crossing | BoundManager.cpp 161–199 | `set_bound`, `mark_pending`, `first_conflict` |
| `BoundManager::tightenLowerBound/tightenUpperBound` (plain and with a row explanation) | 145–159, 315–378 | `tighten_bound` |
| `Tableau::updateVariableToComplyWithLowerBoundUpdate/UpperBoundUpdate` | Tableau.cpp 1785–1827 | `comply`: a nonbasic outside the new bound moves onto it through the nonbasic update; a basic only changes status |
| `BoundManager::propagateTightenings` | 268–284 | `propagate_tightenings` |
| `Tableau::allBoundsValid` → `InfeasibleQueryException` in `Engine::solve` | Engine.cpp 313–317 | `conflict_no_bounded_model`, `all_bounds_valid_iff` |
| `Engine::applySplit`: split bounds with a reset explanation, as ground bounds flagged `isPhaseFixing` | Engine.cpp 1994–2141 | `apply_decision` with a recorded decision |
| `RowBoundTightener::tightenOnSingleInvertedBasisRow` | RowBoundTightener.cpp 237–402 | `row_rules`, `rule_bound`, `apply_rules` |

## The model ([Tableau_Bound_Update.thy](../Isabelle/Tableau_Bound_Update.thy))

A `bound_store` wraps the tableau state with the pending sets
(`_tightenedLower/_tightenedUpper`) and the first recorded conflict
(`_firstInconsistentTightening`, or `None` while `_consistentBounds` holds).
Both sides are handled by one `bound_side` parameter.

| Theorem | Statement |
| --- | --- |
| `tighten_weaker_noop` | A proposal that is not strictly stronger changes nothing, and `tighten_bound` reports `False`. |
| `tighten_bounded_models` | A stronger proposal's bounded solutions are the old ones intersected with the new bound. |
| `tighten_invariant` | If the new bound does not cross, the simplex invariant survives: rows and their satisfaction, nonbasics within bounds (the moved nonbasic lands on the bound), bound order, index lists. |
| `tighten_basic_value` | Tightening a basic changes no value; its status is read against the new bound. |
| `tighten_pending`, `propagate_tightenings_exact`, `propagated_bounds_hold` | A stronger bound marks its variable pending. Propagation notifies exactly the pending bounds in variable order, and every notified bound holds in every bounded solution. |
| `tighten_conflict`, `tighten_conflict_sound`, `tighten_conflict_complete` | The first crossing is recorded and never replaced. A recorded conflict stays a crossing, since bounds only tighten, and no crossing goes unrecorded. |
| `conflict_no_bounded_model`, `all_bounds_valid_iff` | A recorded conflict means no bounded solution; the absence of one is exactly `allBoundsValid`. |

The model recomputes the cost function from the statuses, so Marabou's
invalidation of a cached cost function after a status change has no
counterpart and needs none.

### Branches: derived bounds versus decisions

A `branch` is a bound store plus the list of decisions (split bounds) applied
so far. `branch_of S0 Br` says that its bounded solutions are exactly those of
the root tableau `S0` that satisfy the decisions.

| Theorem | Statement |
| --- | --- |
| `apply_derived_branch` | A bound entailed by the current solutions keeps the branch invariant without recording anything. |
| `apply_decision_branch` | A split bound keeps the invariant when it is recorded as a decision. |
| `undeclared_decision_breaks_branch` | A bound that is not entailed, applied as if derived, falsifies the invariant. |
| `branch_conflict_refutes` | A conflict proves that no root solution satisfies the decisions. This refutes the branch, not the query. |
| `root_conflict_unsatisfiable` | With no decisions, on the starting tableau of a query, a conflict proves the query unsatisfiable. |
| `branch_simplex_infeasible` | An `Infeasible` simplex run on a branch refutes the branch in the same sense. |

### Row-derived bounds

For a row `y = c + Σ a x`, `row_lower_bound` and `row_upper_bound` bound `y` by
choosing each variable's bound by the sign of its coefficient, as
`tightenOnSingleInvertedBasisRow` does. `solved_bounds` solves the row for
one variable with a nonzero coefficient. Each term is bounded separately, so
repeated variables are handled soundly. Native loosens these bounds by
`EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT` (10⁻⁶) and skips
coefficients below `MINIMAL_COEFFICIENT_FOR_TIGHTENING` (0.01); here both are
exact.

`row_rule_entailed` proves every such bound entailed. `apply_rules` evaluates
rules against the current state, as native uses `y`'s freshly tightened
bounds. `apply_rules_sound` shows that any rule sequence preserves the
branch, its decisions, row support and the conflict invariants.
`row_rules S y` is the native order: `y`'s bounds first, then each variable
of the row.

## Examples ([Tableau_Bound_Update_Examples.thy](../Isabelle/Tableau_Bound_Update_Examples.thy))

All by `code_simp`:

* `linear_unsat_file_unsatisfiable_by_bounds`: the decoded bytes of
  `examples/linear_unsat.mqx`. The auxiliary row `x2 = x0 − x1`, with `x2`
  fixed to 0, `x0 ≤ 1/4` and `x1 ≥ 1/2`, gives `x2 ≤ −1/4`. The conflict
  `(x2, upper, −1/4)` is recorded at the root, so the query is
  unsatisfiable. This is a third independent refutation of that file, after
  the checked Marabou certificate and the HOL simplex. Marabou's own run of
  it also ended in bound tightening: its run report shows 0 simplex steps, 0
  pivots and 1 explicit-basis tightening call, and its certificate's
  contradiction is that single row.
* `split_not_entailed`, `decision_keeps_branch` and
  `split_as_derived_breaks_branch`: on a root with a solution at `x0 = 7/8`,
  the split `x0 ≥ 1` must be recorded as a decision.
* `decision_effects`: applying it moves the nonbasic `x0` from 0 to 1, and
  the basics follow their rows to `x2 = x3 = 1`. `x0` becomes pending, and
  propagation reports `(x0, lower, 1)`.
* `second_decision_conflict` and `branch_refuted_not_root`: a second
  decision `x1 ≥ 1` makes row `x3 = x0 − x1` give `x3 ≤ 0` against
  `x3 ≥ 1/4`. The conflict refutes that branch, while the root still has
  solutions.
* `weaker_proposal_is_noop`, `basic_tightening_status`: a weaker proposal
  changes nothing. Tightening the basic `x3` to `≤ 3/4` keeps its value 1
  and makes its status `Above_Upper`.

## Limits

* Native tolerances (`FloatUtils::gte` for consistency, the rounding
  constant and the minimal coefficient for row bounds) are set to exact
  comparisons. A native bound that holds only up to tolerance has no
  counterpart.
* Bound explanations for proofs (`BoundExplainer`) are not modeled; the
  branch invariant and entailment replace them.
* Variable merging in `applySplit`, split equations, and bounds from ReLU
  rules (`getEntailedTightenings`) are outside this milestone. So are the
  search stack and its restoration; that is the audit's milestone 5.
