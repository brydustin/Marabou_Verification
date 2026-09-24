# Exact tableau pivots and simplex steps

Completed on 2026-09-24 (milestone 25). This is the second step of the
solver-calculus roadmap in [PROJECT_DIRECTION_AUDIT.md](PROJECT_DIRECTION_AUDIT.md)
(section 8, milestone 2). It extends that step to moving pivots, the ratio
test and the simplex failure branch. It builds on the solved-row state of
[TABLEAU_ASSIGNMENT_UPDATE.md](TABLEAU_ASSIGNMENT_UPDATE.md). Everything is
exact real arithmetic with every native tolerance set to zero. This is a
source-grounded abstraction of the native operations, **not** a proof about
the C++ code, its basis factorization or its floating point.

## Native operations covered

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`,
`src/engine/`:

| Native code | Lines | HOL counterpart |
| --- | --- | --- |
| `Tableau::performPivot` | Tableau.cpp 696–801 | `apply_choice … (Leaving b τ)` = `move_entering` then `exchange_basis` |
| `Tableau::performDegeneratePivot` | Tableau.cpp 803–850 | `exchange_basis`; arrays: `native_degenerate_pivot` |
| index-map and array updates | Tableau.cpp 779–782, 828–831, 839–841 | `swap_indices`, `native_degenerate_pivot`, `native_pivot` |
| `Tableau::updateAssignmentForPivot` | Tableau.cpp 2345–2457 | `move_entering`, `native_leaving_target`, `native_pivot`, `native_bound_flip` |
| `Tableau::getTableauRow`, `computeChangeColumn` | Tableau.cpp 1568–1607, 1452–1457 | explicit rows; `row_coefficient`, `change_column` (d = −row coefficient) |
| `Tableau::computeBasicStatus` | Tableau.cpp 425–452 | `status_of` |
| `CostFunctionManager::computeCoreCostFunction`, `computeBasicOOBCosts` | CostFunctionManager.cpp 170–205, 264–297 | `core_cost`, `reduced_cost` |
| `Tableau::eligibleForEntry`, `nonBasicCanIncrease/Decrease` | Tableau.cpp 617–666 | `entering_direction` |
| `Tableau::harrisRatioTest` (the default: `USE_HARRIS_RATIO_TEST = true`) | Tableau.cpp 1057–1440 | `exact_harris_ratio_test` |
| `Engine::performSimplexStep`, its `InfeasibleQueryException` branch | Engine.cpp 632–831, 776–786 | `simplex_run`, `no_entering_candidate_infeasible` |
| `Engine::fixViolatedPlConstraintIfPossible` | Engine.cpp 833–924 | `pivot_and_set` |

## The exchange ([Tableau_Pivot.thy](../Isabelle/Tableau_Pivot.thy))

For a leaving basic `b` and an entering nonbasic `e`, the row `b = c + a·e + rest` with
pivot element `a ≠ 0` (`pivot_admissible`) is solved for `e` (`solve_row`),
and `e` is substituted into every other row (`substitute_row`). The two
variables swap between the basic and nonbasic sets, and their stored values
move between the two value stores. Duplicate terms are allowed throughout, as
in the existing linear expressions.

| Theorem | Statement |
| --- | --- |
| `exchange_models` | The exchanged rows have exactly the same real solutions. |
| `exchange_rows_supported`, `exchange_well_formed` | Partition and row support are preserved. The bound-order conjunct also needs `lower b ≤ upper b`. |
| `exchange_candidate` | The variable-indexed candidate valuation is unchanged. This is the native "values haven't changed" array swap. |
| `exchange_rows_satisfied` | Row consistency of the stored values is preserved. |
| `exchange_nonbasic_bounds` | If the leaving value is within its bounds, all nonbasics stay within bounds. Native asserts this for degenerate pivots. |
| `exchange_pivot_element`, `exchange_back_admissible` | The new pivot element is `1/a`, so the reverse pivot is admissible. |
| `solved_rows_unique`, `basis_determines_rows` | Two supported solved forms with the same basis and the same solutions have rows equal on every valuation. |
| `exchange_back_rows` | Pivoting back restores the original rows up to evaluation. |
| `exchange_represents`, `exchange_bounded_models` | Represented equation systems and bounded solution sets are preserved. |
| `pivot_and_set_sound` | Pivoting a basic out and then setting it keeps row consistency and the solutions, sets the value, and keeps nonbasic bounds when both values are in bounds. |

`solved_rows_unique` is how this model relates to the native factorization.
Native Marabou never stores these rows: it recomputes them from a factorized
basis matrix. In exact arithmetic that computation gives the unique solved
form of the new basis, which by this theorem agrees in value with the rows
built here. The remaining obligation is that the native factorization and
floating point compute that form; it is stated, not proved.

## One simplex step ([Tableau_Simplex_Step.thy](../Isabelle/Tableau_Simplex_Step.thy))

* **Statuses and costs.** A basic is `Below_Lower`, `Between` or
  `Above_Upper` (checked in the native order). Its core cost is −1, 0 or +1.
  `reduced_cost S j` is the cost-weighted sum of the row coefficients of `j`,
  which equals native −c_B B⁻¹A_j.
* **Eligibility.** A negative reduced cost with the value below the upper
  bound means increase; a positive one with the value above the lower bound
  means decrease.
* **Ratios.** A step has nonnegative length τ; native signed change ratios
  are `direction_sign d * τ`. An in-bounds basic is limited by the bound it
  approaches. An out-of-bounds basic is limited by its violated bound when
  moving towards it, and is unconstrained when moving away. These are the
  `basicCost` cases of `harrisRatioTest`.
* **Exact Harris test.** Pass 1 takes the minimal ratio. The entering
  variable's own range wins ties, giving a bound flip ("fake pivot").
  Otherwise pass 2 scans the basics in native index order and takes the
  first with the largest pivot magnitude among those attaining the minimum.
  With zero tolerance, Harris's relaxed bounds equal the true bounds.

| Theorem | Statement |
| --- | --- |
| `exact_harris_admissible` | The chosen step is admissible: 0 ≤ τ ≤ the entering range, τ is at most every basic's ratio, and a leaving variable attains its ratio. |
| `basic_ratio_step` | Within its ratio, a basic keeps its status: in-bounds stays in bounds, and an out-of-bounds basic never crosses past its violated bound. |
| `leaving_native_formulas` | The leaving variable lands exactly on the native target bound, and the step equals native `nonBasicDelta = basicDelta / pivot`. |
| `choice_invariants` | After an admissible bound flip or pivot: rows supported and satisfied; solutions and bounded solutions unchanged; all nonbasics within bounds; bound order kept; every remaining basic keeps its status; the new basic is within its bounds. |
| `no_entering_candidate_infeasible` | If some basic is out of bounds and no nonbasic is eligible, the rows and bounds have **no real solution**. This is the native "Cost function is fresh --- failure is real" branch. |
| `all_between_candidate_feasible` | If every basic is within bounds, the candidate valuation is a bounded solution. |

The infeasibility proof is the standard phase-1 argument. The cost-weighted
sum of the basics differs from its value at the candidate by
Σ_j reduced_cost_j · (v_j − candidate_j). Each term is ≥ 0 because no
nonbasic is eligible and all nonbasics sit at the blocking bound. Yet any
in-bounds `v` makes the weighted sum strictly smaller than at the candidate.

## Native arrays ([Tableau_Index_Layout.thy](../Isabelle/Tableau_Index_Layout.thy))

`tableau_layout` models `_basicIndexToVariable`, `_nonBasicIndexToVariable`,
`_basicAssignment` and `_nonBasicAssignment` as exact lists. `variable_to_index`
models `_variableToIndex`. `layout_abstracts L S` relates the arrays to the
variable-indexed state.

| Theorem | Statement |
| --- | --- |
| `layout_swap_valid`, `variable_to_index_after_swap` | The index swap keeps the maps distinct and disjoint, gives the leaving variable the entering index `k` and the entering variable the leaving index `l`, and leaves all other indices unchanged (Tableau.cpp 781–782). |
| `native_degenerate_pivot_refines` | The native swap of indices and array entries implements `exchange_basis`. |
| `native_pivot_refines` | Writing the new values into the old slots, then swapping indices, implements `move_entering` followed by `exchange_basis`. |
| `native_bound_flip_refines` | The fake-pivot array update implements the nonbasic move. |
| `native_simplex_pivot_refines` | With the native formulas (target bound, `nonBasicDelta`, change column), the arrays implement the exact Harris pivot. |

## A fuelled loop ([Tableau_Simplex_Run.thy](../Isabelle/Tableau_Simplex_Run.thy))

`simplex_run n S bs ns` repeats the step while some basic is out of bounds.
It takes the first eligible nonbasic in index order; the native entry
strategies are heuristics and not modeled. It updates the index lists as
native does. It returns `Feasible`, `Infeasible` or `Out_Of_Fuel`.

* `simplex_run_sound`: the invariant (`simplex_invariant`) and the bounded
  solution set are preserved. `Feasible` returns a bounded solution of the
  original state. `Infeasible` proves that the original state has none.
  `Out_Of_Fuel` means nothing about the query.
* `simplex_run_represented`: for a tableau that represents an equation list,
  these are statements about the equations and bounds directly.
* `export_code … checking SML` compiles the loop, the ratio test and the
  array operations.

Termination and anti-cycling are not proved. Soundness does not depend on
them.

## Examples ([Tableau_Pivot_Examples.thy](../Isabelle/Tableau_Pivot_Examples.thy))

Rows `x2 = x0 + x1` and `x3 = x0 − x1`, with `x0, x1 ∈ [0,1]`,
`x2 ∈ [3/2, 2]` and `x3 ∈ [l, 1]`, starting from `x0 = x1 = 0`. Checked by
`code_simp` (no evaluation oracle):

* One exchange (`x3` out, `x0` in) gives the rows `x0 = x3 + x1` and
  `x2 = x1 + x3 + x1`; the duplicate term is kept. It has the same solution
  set.
* The Harris choice and the native array update give
  `basic_assignment = [1/2, 1/2]` and `nonbasic_assignment = [1/2, 0]`.
  These arrays refine the HOL step.
* For `l = 1/2`, the run takes four steps: a pivot, a bound flip, a
  degenerate pivot and a bound flip. It returns `Feasible` with `x = (1, 1/2, 3/2, 1/2)`, the
  unique solution, and `feasible_run_solution` checks it against the
  equations and bounds.
* For `l = 3/4`, the run returns `Infeasible`. `example_infeasible` then
  proves by `simplex_run_sound` that the equations and bounds have no real
  solution.
* Rejections:
  * `zero_pivot_rejected`: a zero pivot element is not admissible, and
    exchanging on it changes the solution set.
  * `overstep_rejected`: a step past the minimal ratio pushes an in-bounds
    basic out of bounds.

## Limits

* No proof about C++: factorization, memory, `FloatUtils` tolerances and
  numerical recovery (for example `MalformedBasisException`, refactorization)
  are outside the model.
* Positive native tolerances differ from this model. Harris's positive
  tolerance lets basics move slightly past their bounds; with it zero, this
  model forbids that.
* Only the default ratio test is modeled, and only with a fresh core cost
  function:
  * The standard ratio test would break ties in favour of a basic, not a
    bound flip.
  * Native incrementally updated or heuristic costs are not modeled, nor
    the clamping of ratios when costs are stale, nor the optimizing mode.
* The entry strategy, the stability search over several candidates, bound
  tightening, initialization from a query, ReLU handling and search remain
  open. See the roadmap in the audit.
