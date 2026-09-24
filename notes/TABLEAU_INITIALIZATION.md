# The starting tableau of a query

Completed on 2026-09-24 (milestone 26). [Milestone 25](TABLEAU_PIVOT.md)
proved an exact simplex loop sound for a *given* tableau. This milestone
builds that tableau from a query as Marabou does, so the loop's results
become theorems about the query:

* `Simplex_Unsat` proves the query **unsatisfiable**, ReLUs included, since
  its linear part and bounds already have no real solution.
* `Simplex_Feasible v` gives a valuation satisfying every equation and
  bound. It is a **model** of the query when `v` also satisfies the ReLUs,
  and always when there are none.
* `Simplex_Unknown` claims nothing. It covers inputs the engine would
  refuse, a failed basis check, and exhausted fuel.

It also copies Marabou's default initial-basis selection exactly. On all 20
captured native runs, HOL reproduces the basic and nonbasic orders Marabou
chose. All of this is exact real arithmetic, not a proof about the C++ code.

## Native initialization covered

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`, `src/engine/`:

| Native code | Lines | HOL counterpart |
| --- | --- | --- |
| `Engine::invokePreprocessor`: infinite bounds are an error | Engine.cpp 980–1012 | `engine_ready`: every variable below `n` has a lower and an upper bound atom |
| `Engine::createConstraintMatrix`: only `EQ` rows | 1061–1089 | `engine_ready`: all linear atoms are equations over variables below `n` |
| `Engine::addAuxiliaryVariables`: row `i` gets `n + i` with coefficient −1, bounds fixed to the scalar | 1290–1314 | `initial_rows`, `initial_lower`, `initial_upper` |
| `Engine::selectInitialVariablesForBasis` (default, `ONLY_AUX_INITIAL_BASIS = false`) | 1115–1288 | `select_initial_basis` (exact copy), `basis_pivots`, `basis_order` |
| `Engine::augmentInitialBasisIfNeeded` | 1316–1328 | the auxiliaries of the remaining rows in `basis_order` |
| `Tableau::initializeTableau`: nonbasics numbered in increasing order and set to their lower bounds | Tableau.cpp 336–374 | `initial_tableau`, `reset_assignment`, the nonbasic list of `native_initial_tableau` |
| `Tableau::computeAssignment` | Tableau.cpp 376–411 | basics evaluated from their rows |

## The auxiliary-basis tableau ([Tableau_Initialization.thy](../Isabelle/Tableau_Initialization.thy))

For a query with `m` equations `c + terms = b` over variables `0 … n−1`,
`initial_tableau n Q` has the auxiliary variables `n … n+m−1` as basics. Row
`n+i` is `terms_i` and its bounds are both `b_i − c_i`. The original
variables are nonbasic at their lower bounds. This is the basis Marabou uses
when `ONLY_AUX_INITIAL_BASIS` holds or no triangular column is found. Several
bound atoms on one variable are read as their conjunction (maximum lower,
minimum upper).

| Theorem | Statement |
| --- | --- |
| `initial_tableau_invariant` | For an engine-ready query with consistent bounds, the tableau satisfies `simplex_invariant` with the native index lists. |
| `initial_bounded_models` | Its bounded solutions are exactly the valuations satisfying the auxiliary rows, the fixed auxiliary bounds and the query's bounds. |
| `query_model_extends` | Every valuation satisfying the query's equations and bounds extends, by the auxiliary values, to a bounded solution. |
| `bounded_model_satisfies_linear_part` | Every bounded solution satisfies all equations and bound atoms of the query. |
| `initial_empty_unsatisfiable`, `inconsistent_bounds_unsatisfiable` | No bounded solution, or crossed bounds, proves the query unsatisfiable. |
| `solve_linear_part_unsat`, `solve_linear_part_feasible`, `solve_linear_part_model`, `solve_linear_part_sat` | The query-level results of `simplex_run` on this tableau. |

## The native initial basis ([Tableau_Initial_Basis.thy](../Isabelle/Tableau_Initial_Basis.thy))

`select_initial_basis` is the native loop with `FloatUtils::isZero` replaced
by an exact test. The loop:
* counts the nonzeros per row and column;
* repeatedly diagonalizes the first singleton row, swapping counts with
  their positions as native does;
* when no row is a singleton, excludes the densest column (first maximum).

The result is reached from the auxiliary basis by `pivot_sequence`. This is
a list of exchanges `(auxiliary of row r, its diagonal column)`, and each is
checked for a nonzero pivot element. `reset_assignment` then puts the
nonbasics at their lower bounds and solves for the basics, as
`initializeTableau` and `computeAssignment` do. The index lists follow native
order: diagonal columns first, then the remaining auxiliaries, with the
nonbasics increasing.

* `pivot_sequence_sound`: a checked sequence keeps row support, bounds, the
  carrier and the bounded solutions.
* `native_initial_tableau_sound`: the result satisfies the simplex invariant
  and has the same bounded solutions as the auxiliary-basis tableau.
* `solve_linear_part_native_*` and `solve_query_unsat`, `solve_query_model`
  and `solve_query_sat`: the same query-level results from the native basis.
  `solve_query` computes `n` as the file workflow does, one more than the
  largest variable index.

Soundness never depends on the selection. A failed pivot check or a
mismatched index list gives `Simplex_Unknown`.

## Native evidence ([Imported_Marabou_Initial_Bases.thy](../Isabelle/Imported_Marabou_Initial_Bases.thy))

The capture harness now writes `_initial_basis.json`
(`marabou-initial-basis-v1`) for every run that initializes a tableau. The
record holds `Tableau::_basicIndexToVariable` and `_nonBasicIndexToVariable`,
read from `Engine::storeState` before solving. The harness never interprets
it.

`refresh_native_fixtures.py --tag m26_refresh` reran every capture. All
earlier data artifacts were reproduced byte for byte, and 20 distinct records
were saved. The file runs that reproduce a scenario produced exactly that
scenario's record. The preprocessing-refuted run has no tableau.
[import_initial_basis.py](../Isabelle/tools/import_initial_basis.py) parses
each record strictly and renders the run's source query. For each run it
proves by `code_simp`:

```text
map_option (λ(S, bs, ns). (bs, ns)) (native_initial_tableau n (embed_query source))
  = Some (native basic order, native nonbasic order)
```

All 20 hold, covering:
* the ten scenarios;
* the phase-fixing and inequality files;
* three runs with native preprocessing.

Six runs have 5 or 6 rows; every pivot check in all 20 passes.
`relu_split_swapped_basis_rejected` shows the check is not vacuous.
[test_initial_basis.py](../Isabelle/tests/test_initial_basis.py) checks
that the theory is current and registered and covers every record, and
rejects malformed records.

## Examples ([Tableau_Initialization_Examples.thy](../Isabelle/Tableau_Initialization_Examples.thy))

All by `code_simp`, with no Marabou run or certificate involved:

* `linear_unsat_file_unsatisfiable_by_simplex`: `decode_query` of the bytes of
  `examples/linear_unsat.mqx` is refuted by the HOL simplex. Both the
  auxiliary and the native basis are used, and the native selection makes
  `x1` basic.
* `linear_sat_query_satisfiable`: a two-equation linear query, solved at
  `x = (1/2, 1/2, 0)`.
* `relu_linear_unsat_query_unsatisfiable`: a query with a ReLU whose linear
  part is infeasible.
* `relu_sat_file_relaxation_only`: for `examples/relu_sat.mqx` the linear
  part is feasible, but the valuation found violates a ReLU, so no model is
  claimed.
* `solver_boundaries`: an inequality atom or a missing bound gives
  `Simplex_Unknown`, and crossed bounds give `Simplex_Unsat`.

## Findings and limits

* **Repeated variables.** `createConstraintMatrix` *assigns*
  `A[i][var] = coefficient` for each addend, so a repeated variable keeps
  only its last coefficient. The HOL semantics sums them. The file workflow
  already rejects repeated variables in an equation, so no captured run is
  affected.
* **Several bounds on a variable.** Native setters overwrite, keeping the
  last value. HOL takes the conjunction. The workflow requires exactly one
  lower and one upper bound per variable.
* **Other native steps.** `removeRedundantEquations` is not modeled. The
  harness requires that it removes no row, since `snapshot_steps` checks the
  dimensions. Native nonzero tests use a tolerance where HOL tests exactly;
  the two agree on every captured run.
* **Inequalities.** `le`/`ge` atoms must first become equations. The checked
  slack introductions of [INEQUALITY_AUXILIARY.md](INEQUALITY_AUXILIARY.md)
  do this, but they are not composed with the solver here.
* **ReLUs** are only relaxed. Refuting or solving a query that needs a
  ReLU case split requires the search milestones of the audit roadmap. So
  does termination: `Simplex_Unknown` on exhausted fuel is the honest answer.
