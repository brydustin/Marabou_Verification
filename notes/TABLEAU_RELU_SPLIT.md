# One native ReLU split on the tableau state

Completed on 2026-09-24 (milestone 28). This is milestone 4 of the audit's
solver-calculus roadmap ([PROJECT_DIRECTION_AUDIT.md](PROJECT_DIRECTION_AUDIT.md),
section 8). It models how Marabou splits a ReLU in auxiliary form, as two
lists of bound decisions on the branch state of
[TABLEAU_BOUND_UPDATE.md](TABLEAU_BOUND_UPDATE.md). It proves that the two
children cover the parent, including the zero boundary, and that they are
exact. So refuting both children refutes the parent.

The query-level split in `ReLU_Splitting` replaces the ReLU by
`y = 0` or `y = x`. This is the native form: the matrix is fixed and only
bounds change. Everything is exact real arithmetic, not a proof about the C++
code.

## Native code covered

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`, `src/engine/`:

| Native code | Lines | HOL counterpart |
| --- | --- | --- |
| `ReluConstraint::transformToUseAuxVariables`: `f − b − aux = 0`, `aux ≥ 0` | ReluConstraint.cpp 936–978 | `aux_relu`, `aux_form`; for queries, `relu_in_aux_form` checks the ReLU atom and an equation with exactly these coefficients |
| `getInactiveSplit`: `b ≤ 0`, `f ≤ 0` | 674–681 | `native_inactive_split` |
| `getActiveSplit` with the auxiliary in use: `b ≥ 0`, `aux ≤ 0` | 683–705 | `native_active_split` |
| `getCaseSplits`: order by the sign of `f`'s assignment when no direction is set | 597–641 | `case_splits` |
| `getEntailedTightenings`: always `f ≥ 0`, `aux ≥ 0` | 827–916 | `relu_nonneg_entailed` |
| `SearchTreeHandler::performSplit`: disable the constraint, store the state, apply the first split (no equations allowed), keep the rest | SearchTreeHandler.cpp 133–230 | `apply_split`, `split_refutes` |
| `Engine::applySplit`, bound-only path | Engine.cpp 1994–2141 | `apply_decision` for each bound |
| `Engine::explicitBasisBoundTightening` at the top of each main-loop iteration: the row tightener over the basic rows | Engine.cpp 287–296, 2269–2294 | `tighten_rows` |

## Results ([Tableau_Relu_Split.thy](../Isabelle/Tableau_Relu_Split.thy))

| Theorem | Statement |
| --- | --- |
| `relu_split_covers` | Every bounded solution that satisfies the ReLU, with `aux = f − b`, lies in the inactive or the active child. |
| `zero_boundary_in_both` | At `b = 0` it lies in both children. |
| `relu_split_refutes` | If both children of a branch have no ReLU-respecting solution, neither does the branch. |
| `children_imply_relu`, `relu_nonneg`, `relu_nonneg_entailed` | With `f ≥ 0` and `aux ≥ 0`, which the ReLU itself entails, each child forces the ReLU relation. So the split is exact, and the ReLU needs no further attention once split, which is why native disables it. |
| `apply_relu_derived_branch`, `apply_decision_relu_branch`, `apply_split_relu_branch` | ReLU-aware branches (`relu_branch_of`): bounds entailed with the ReLUs keep a branch, and split bounds extend its decisions. |
| `branch_ok`, `tighten_ok`, `apply_split_ok`, `apply_rules_preserves` | While no conflict is recorded, the simplex invariant survives bound application and row tightening. Once one is recorded, the branch is refuted. |
| `branch_refuted_sound` | A branch is refuted by its own recorded conflict, a conflict after row tightening, or an `Infeasible` simplex run. |
| `split_refutes_sound` | Refuting both native children, in native order, refutes the parent branch. |
| `branch_feasible_solution` | A feasible leaf whose candidate satisfies the ReLUs is a solution of the root. |
| `relu_root_empty_unsat`, `root_split_children_unsat`, `solve_one_split_unsat` | At the starting tableau of a query, the same statements prove the query unsatisfiable. `solve_one_split` is an executable single split expansion. |

## Examples ([Tableau_Relu_Split_Examples.thy](../Isabelle/Tableau_Relu_Split_Examples.thy))

* `split_query_unsatisfiable`: a query whose linear part is feasible but
  which needs a split. `solve_one_split` refutes it by `code_simp`.
  * `x1` starts at 1/4 > 0, so the active child comes first, as in
    `getCaseSplits`.
  * The inactive child's `x1 ≤ 0` crosses `x1 ≥ 1/4` at once.
  * The active child survives row tightening, and one simplex step refutes
    it.
* `preprocess_split_file_unsatisfiable_by_native_split`: the decoded bytes of
  `examples/preprocess_split_unsat.mqx`, the `relu_split` capture's query,
  which Marabou refuted with one binary split. The file carries the ReLU's
  auxiliary equation `x1 − x0 − x2 = 0` itself. `root_split_children_unsat`
  applies the native split to its starting tableau. Each child's emptiness
  follows by `linarith` from the tableau's bounded solutions:
  * in the inactive child, `x1 = 0` forces both `x3 ≤ −1/4` and
    `x3 ≥ 1/4`;
  * in the active child, `x2 = 0` does the same for `x4`.
* `split_needs_aux_equation`: without `aux = f − b`, the bound-only children
  miss a ReLU-respecting point. `zero_point_in_both_children` shows the
  boundary point lies in both children.
* `split_boundaries`: a satisfiable ReLU query is not refuted, and a query
  without the auxiliary equation is not accepted.

## Finding: kernel-checked evaluation does not scale to this state

The project proves computations only with `code_simp`, which rewrites in the
kernel, and never with an evaluation oracle. On the 9-variable,
14-column tableau of the file above, measured on this machine:

| Computation | Time under `code_simp` |
| --- | --- |
| Decoding the file's 361 bytes | about 24 s per occurrence in a goal |
| Simplex runs of 1, 2 and 3 steps (after subtracting decoding) | about 2 s, 8 s and 23 s |
| The same with an experimental per-exchange row table (not kept) | 1.5 s, 5.4 s, 17.5 s, and 88 s for 4 steps |
| Row tightening over the five rows of one child | not finished after 10 minutes |

The same runs evaluate in seconds in ML (`value`); the ML trace, which was
not used in any proof, needs 5 or 6 steps per run. The cause is structural:
`code_simp` normalizes bottom-up, including under binders, and the tableau
state keeps rows, bounds and values as nested function updates and closures.
Their normal forms grow with every update. Small examples, such as those
above and in [TABLEAU_PIVOT.md](TABLEAU_PIVOT.md), evaluate in seconds.

Running the HOL solver on real files inside the kernel would need a
first-order state: finite association lists for rows, bounds and values,
with refinement lemmas to the present state. Alternatively, a native trace
could be checked instead of recomputed. Either is a separate milestone; no
theorem here depends on it.

[Milestone 29](TABLEAU_SEARCH.md#finding-evaluation-cost) traced the growth
per step to row and value functions that mentioned their predecessor
several times. It added equivalent code equations that mention it once,
which cut the `solve_one_split` example above from 28 s to 9 s.

## Limits

* Only ReLUs whose auxiliary variable is in use (`_auxVarInUse`) are covered.
  The equation form of `getActiveSplit` would add a row, which native
  forbids at split time.
* Direction heuristics (`_direction` from polarity or BaBSR) and the choice of
  which ReLU to split are not modeled. The order of the two children does
  not affect soundness.
* One split expansion is formalized. The search stack, restoration on
  backtracking, and closing nested frames are the audit's milestone 5.
