# Search with backtracking: a sound solver loop

Completed on 2026-09-25 (milestone 29). This is milestone 5 of the audit's
solver-calculus roadmap ([PROJECT_DIRECTION_AUDIT.md](PROJECT_DIRECTION_AUDIT.md),
section 8), extended to the whole search stack and a fuelled main loop.

The previous milestones built the parts: the tableau and pivots, the
starting tableau, bound application with conflicts, and one native ReLU
split. This milestone adds the search stack of `SearchTreeHandler` and a
fuelled main loop in the style of `Engine::solve`. The loop's results are
theorems about the query:

* `Search_Sat v`: `v` satisfies the query, ReLUs included.
* `Search_Unsat`: the query has no real solution.
* `Search_Unknown`: nothing is claimed (fuel exhausted, a violated ReLU that
  cannot be split, or an input the engine would refuse).

This is the audit's section 6 structure: initialization relates the query
to the start state, each transition keeps an invariant, and both terminal
results are sound. It is exact real arithmetic, not a proof about the C++
code. Termination and completeness are not claimed.

## Native code covered

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`, `src/engine/`:

| Native code | Lines | HOL counterpart |
| --- | --- | --- |
| `SearchTreeStackEntry`: active split, alternatives, stored engine state | SearchTreeStackEntry.h | `search_frame`: the split ReLU, the parent branch, the alternatives |
| `SearchTreeHandler::performSplit`: get the case splits, disable the constraint, store the state (bounds only), push the context, apply the first split, keep the rest | SearchTreeHandler.cpp 133–230 | `perform_split` |
| `Engine::preContextPushHook` → `BoundManager::storeLocalBounds` | Engine.cpp 2546–2554, BoundManager.cpp 223–230 | the parent branch kept in the frame |
| `SearchTreeHandler::popSplit`: drop entries without alternatives, pop the context, restore bounds and state, apply the next alternative, repeat while inconsistent | SearchTreeHandler.cpp 267–402 | `pop_split` and the next loop iteration |
| `Engine::postContextPopHook` → `BoundManager::restoreLocalBounds`, `Tableau::postContextPopHook` → `updateVariablesToComplyWithBounds` | Engine.cpp 2556–2570, BoundManager.cpp 232–239, Tableau.cpp 1703–1717 | `restore_branch`, `comply_all` |
| `Engine::restoreState` with `STORE_BOUNDS_ONLY`: the tableau (basis, assignment) is kept | Engine.cpp 1859–1892, Tableau.cpp 1719 ff. | `restore_branch` keeps the current tableau |
| `Engine::solve` main loop: row tightening, split, bound check, ReLU check or one simplex step; `InfeasibleQueryException` → `popSplit`, empty stack → UNSAT | Engine.cpp 196–461 | `search_step`, `search_loop` |
| `performConstraintFixingStep` → `chooseViolatedConstraintForFixing` (first violated active constraint, `USE_LEAST_FIX = false`) → `reportViolatedConstraint` (threshold) | Engine.cpp 612–630, SearchTreeHandler.cpp 75–90, 544–576 | `pick_split` |

The modeled configuration is that of the `relu_split` capture
([SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md)): native LP,
DeepSoI off, symbolic bound tightening off, and a constraint violation
threshold of 1. With proof production on and DeepSoI off,
`Engine::decideBranchingHeuristics` (Engine.cpp 2706–2741) chooses
`ReLUViolation`, for which `pickSplitPLConstraint` picks nothing, so the
reported violated constraint itself is split.

## The model ([Tableau_Search.thy](../Isabelle/Tableau_Search.thy))

A search state is the current branch, the basic and nonbasic index lists,
and a stack of frames. A frame keeps the ReLU it split, the branch before
the split and the alternatives still to explore.

One iteration (`search_step`):

1. A branch with a recorded conflict is refuted.
2. Row tightening runs over the basic rows (`tighten_rows`); a conflict
   refutes the branch.
3. The exact simplex runs for `sf` steps. `Infeasible` refutes the branch.
   Running out of steps continues with the next iteration, so with `sf = 1`
   each iteration makes one simplex step after row tightening, as native
   does.
4. At a point within bounds, the query's ReLUs are checked. If all hold,
   the point is returned. Otherwise the first violated ReLU that is not
   already split on this path is split; if there is none, the result is
   `Search_Unknown`.

On a refutation, `pop_split` drops frames without alternatives. For the next
frame it restores the parent's bounds, pending sets and conflict status onto
the current tableau, moves nonbasics into the restored bounds, and applies
the next alternative. An empty stack gives `Search_Unsat`. If the
alternative's bounds are inconsistent, native `popSplit` pops again at once;
here the next iteration does so from the same stack.

The query's ReLUs in auxiliary form are found by `query_aux_relus`: for each
ReLU atom, the first variable of an equation that satisfies
`relu_in_aux_form`.

Two entry points start the loop from a query:
* `solve_search` starts from Marabou's default initial basis
  (`native_initial_tableau`, [TABLEAU_INITIALIZATION.md](TABLEAU_INITIALIZATION.md));
* `solve_search_aux_basis` starts from the auxiliary basis, which is
  Marabou's start when `GlobalConfiguration::ONLY_AUX_INITIAL_BASIS` holds
  (Engine.cpp 1135). It is cheaper to evaluate in the kernel.

Both satisfy `search_start`: the simplex invariant, the same bounded
solutions as the query's starting tableau, and all query variables present.

## Results

| Theorem | Statement |
| --- | --- |
| `tighten_rows_sound`, `apply_split_sound` | Row tightening and split bounds keep a branch sound: ReLU-aware, conflict records sound and complete, the simplex invariant without a conflict, and the root's equations and variables. |
| `simplex_run_frame`, `simplex_run_branch_sound` | A simplex run keeps the tableau's equations, variables and bounds, so the branch stays sound under the new basis. |
| `restore_branch_sound` | Restoring a frame onto the current tableau gives a sound branch with exactly the parent's bounds and decisions. Nothing learned in the child is kept. |
| `perform_split_sound` | Splitting keeps the branch and frames sound. Every ReLU-respecting solution of the branch lies in the first child or in the pending alternative. |
| `pop_split_sound` | Popping gives a sound branch and frames, and moves the next alternative from the pending set into the branch. An empty stack has no pending alternatives. |
| `search_step_sound` | `Step_Sat v`: `v` is a root solution satisfying the query's ReLUs. `Step_Next`: the invariant holds again. `Step_Refuted`: every ReLU-respecting root solution is pending. |
| `search_loop_sound` | From an invariant state, `Search_Sat v` gives a root solution satisfying the ReLUs, and `Search_Unsat` shows no ReLU-respecting root solution exists. |
| `search_from_start_sound`, `native_search_start`, `aux_search_start` | From any `search_start`, `Search_Sat v` satisfies the query and `Search_Unsat` proves it unsatisfiable. Both starting bases qualify. |
| `solve_search_sat`, `solve_search_unsat`, `solve_search_aux_basis_sat`, `solve_search_aux_basis_unsat`, `solve_query_search_sound`, `solve_search_verdicts` | For a query: `Search_Sat v` implies `satisfies_query v Q`, and `Search_Unsat` implies `unsatisfiable Q`. |

The invariant `search_inv` has three parts:

* the current branch is sound;
* every frame's parent is sound (without the basis, which the child may have
  changed);
* **coverage**: every ReLU-respecting root solution lies in the current
  branch or in a pending alternative.

Coverage is what makes `Search_Unsat` sound. A refuted branch leaves every
solution in the pending alternatives, and an empty stack has none.

## Examples ([Tableau_Search_Examples.thy](../Isabelle/Tableau_Search_Examples.thy))

All by `code_simp`:

* `split_query_search`, `split_query_unsatisfiable_by_search`: the
  split-needing query of [TABLEAU_RELU_SPLIT.md](TABLEAU_RELU_SPLIT.md) is
  refuted by the search from the auxiliary basis in three iterations:
  * a split with the active child first;
  * that child refuted and popped, moving to the inactive child;
  * that child refuted too, and the final pop finds the stack empty.
* `backtrack_sat_search`, `backtrack_sat_query_solution`: a query whose only
  solutions are in the inactive phase. The linear solution violates the
  ReLU, the active child is refuted, and after backtracking the inactive
  child yields the solution `x0 = −1, x1 = 0, x2 = 1`, which is proved to
  satisfy the query.
* `sat_relu_query_search`: from Marabou's default basis, one simplex step
  reaches a solution without a split.
* `unrestored_alternative_breaks_branch`: applying the inactive split over
  the active child's bounds, instead of the restored parent bounds, excludes
  the ReLU-respecting solution `x0 = −1/2, x1 = 0, x2 = 1/2` of the inactive
  child (`missed_point_facts`). So the unrestored branch does not represent
  that child. By `restore_branch_sound`, the restored one does.

Nested splits are covered by the theorems but not by a kernel-checked
example; see the evaluation finding below. Evaluated in ML outside any
proof, the search from the auxiliary basis on a two-ReLU query explores the
whole depth-2 tree, as in the table below. The query has two ReLUs of one
input with outputs summing to 1 and the input at most 1/4.

| Iteration | Event |
| --- | --- |
| 1 | split the first ReLU (active first) |
| 2 | split the second ReLU (active first), depth 2 |
| 3 | refuted; pop to the second ReLU's inactive child |
| 4 | refuted; the exhausted inner frame is dropped, and the first ReLU's inactive child is resumed at depth 1 |
| 5 | split the second ReLU again |
| 6 | refuted; pop to its inactive child |
| 7 | refuted; the final pop finds the stack empty, so the result is UNSAT |

## Finding: evaluation cost

The state keeps rows, bounds and values as functions, and `code_simp`
normalizes under binders. Three proved code equations remove one source of
growth: `exchange_rows_code`, `substitute_row_code` (Tableau_Pivot.thy) and
`update_nonbasic_assignment_code` (Tableau_Assignment_Update.thy). As
defined, these functions mention the previous row or value function several
times, so each pivot or assignment update copied it several times. This
matches the roughly threefold growth per simplex step recorded in
[TABLEAU_RELU_SPLIT.md](TABLEAU_RELU_SPLIT.md). The equations are
equivalent forms that mention it once. Measured on this machine:

| Computation under `code_simp` | Before | After |
| --- | --- | --- |
| `split_query_solved(4)` (`solve_one_split`, milestone 28) | 28 s | 9 s |
| `split_query` search from the auxiliary basis, three iterations | 282 s | 75 s |
| `backtrack_sat_query` search from the auxiliary basis | — | 226 s |
| One iteration from Marabou's default basis on `split_query` | 68 s | 67–91 s |
| The two-ReLU search above, seven iterations | — | not finished after 30 min |

Profiling the default-basis iteration showed row tightening at the root
taking 22 s. Applying 2, 4 and 8 of its rules took 1.9, 2.1 and 6.1 s, so
the cost grows faster than linearly with the number of applied bounds:
every applied bound adds to the bound and value functions that later steps
normalize again. Tabulating the rows once per tightening pass did not
change that and was not kept. A first-order state (finite lists for rows,
bounds and values) remains the way to evaluate real files in the kernel.

## Comparison with the captured native run

Evaluated in ML outside any proof, `solve_query_search 60 1` on the bytes
of `examples/preprocess_split_unsat.mqx` (the `relu_split` capture's query)
returns UNSAT. It makes two simplex steps, one split, refutes both children
and calls `pop_split` twice, the second time on an exhausted stack. The
native run report ([SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md))
also shows one split, two pops and maximum depth 1. There are two
differences:
* the model visits the active child first, while the native proof tree lists
  the inactive child first. In the model, `f` is positive at the split.
  Native computes the order after its repair step, which the model omits.
* The iteration counts differ: native made 12 main-loop iterations and 9
  simplex steps, the model 5 iterations. The model takes the first eligible
  entering variable, not native's entering heuristic, and it has no repair
  steps.

No theorem depends on this comparison.

## Limits

* ReLU repair (`fixViolatedPlConstraintIfPossible`) is not modeled. Native
  tries a repair before the split takes effect, so its candidate at the
  split, and so the order of the two children, can differ. Soundness does
  not depend on the order.
* Valid case splits (`applyAllValidConstraintCaseSplits`: a ReLU whose phase
  is fixed by its bounds is applied and disabled), entailed tightenings from
  ReLUs during search, symbolic and MILP tightening, DeepSoI, precision
  restoration and the other branching heuristics are not modeled.
* Only ReLUs whose auxiliary equation is in the query are split. A violated
  ReLU without one ends the search with `Search_Unknown`.
* Termination and completeness are not claimed. The loop is fuelled, and the
  simplex has no anti-cycling rule. The search depth is bounded by the
  number of ReLUs, since a ReLU is split at most once on a path.
* Kernel-checked evaluation uses the closure-based state of the earlier
  milestones, so examples stay small (see the finding above).
