# Reluplex and Marabou: historical comparison

Reluplex was inspected after the corresponding Marabou components. It is a
historical reference, not the verification target. Revisions:

* `upstream/ReluplexCav2017`: `60b482eec832c891cb59c0966c9821e40051c082`
  (2020-07-08).
* `upstream/Marabou`: `1c2f4788c32e2f4e407c356b763a8025c5578722`
  (2026-06-18).

Reluplex's `Readme.txt` labels the artifact a proof-of-concept implementation of
the CAV 2017 algorithm and says the repository is no longer maintained. It
points readers to Marabou. The original [Reluplex
paper](https://arxiv.org/abs/1702.01135) describes an SMT approach for networks
with ReLUs. The table below records code observations, not proofs that either
implementation refines the paper's algorithm.

Paths in the two source columns are relative to the respective upstream root.

| Concept | Reluplex source examined | Marabou correspondence / change |
| --- | --- | --- |
| Indexed variables and candidate values | `reluplex/Reluplex.h`: `_numVariables`, `_assignment`, `getAssignment`, `update` | `src/engine/InputQuery.{h,cpp}` separates the query API; `Tableau` holds basic/nonbasic assignments; both implementations use doubles. |
| ReLU input/output pairs | `reluplex/ReluPairs.h`: `ReluPair::_b/_f`, `addPair`, partner maps | `src/engine/ReluConstraint.{h,cpp}` encapsulates a ReLU within the broader `PiecewiseLinearConstraint` interface. The backward/forward pair meaning survives. |
| Linear tableau and pivot | `reluplex/Tableau.h`: linked row/column entries, `addScaledRow`, `eraseRow`; `Reluplex.h::pivot` exchanges basic/nonbasic variables and performs row arithmetic | `src/engine/Tableau.{h,cpp}`, `TableauRow`, sparse constraint matrix, separate basis infrastructure and entry-selection strategies; `Engine::performSimplexStep`, `Tableau::performPivot`. Representation and organization changed substantially. |
| Linear feasibility engine | `reluplex/Reluplex.h::fixOutOfBounds` invokes `reluplex/GlpkWrapper.h::run/solve`; `glpk-patch/glpk.patch` adds callbacks including bound calculations | Marabou has a native simplex engine and an optional Gurobi path. The native path is used for its current proof-producing mode. It is not simply the old patched GLPK wrapper. |
| Bounds and reasons for backtracking | `reluplex/VariableBound.h`: finite flag, numeric bound and stack level; `Reluplex.h::updateLowerBound/updateUpperBound`, `InvariantViolationError` | `src/engine/BoundManager.{h,cpp}` centralizes bounds; `GroundBoundManager`, `src/proofs/BoundExplainer` and PLC lemmas support proof evidence. The old stack-level marker is not an exact arithmetic certificate. |
| Row-based bound tightening | `Reluplex.h::tightenAllBounds`, `tightenBoundsOnRow`, `storeGlpkBoundTightening`, `performGlpkBoundTightening` | `src/engine/RowBoundTightener.{h,cpp}`, `BoundManager`, and activation-specific tightening methods. Sign-dependent use of lower/upper bounds survives mathematically. |
| Repair violated ReLU | `Reluplex.h::fixBrokenRelu`, `fixBrokenReluVariable`, `update`, `pivot` | `ReluConstraint::getPossibleFixes/getSmartFixes` and `Engine` repair routines; the broader modern solver also has other search modes. The old repair heuristic is not the HOL semantics. |
| Active/inactive phase choice | `reluplex/SmtCore.h::dissolveReluOnVar`, `beginWithSplit`; bound updates in `Reluplex.h`, including `unifyReluPair` for active merging | `ReluConstraint::getActiveSplit/getInactiveSplit`, generic `PiecewiseLinearCaseSplit`, and `Engine::applySplit`; optional ReLU auxiliaries express splits as bounds. The same two exact mathematical phases motivate our first inference rule. |
| Branching, backup, restoration | `SmtCore::SplitInformation` copies bounds, assignment, basic variables, dissolved pairs and tableau; `storeCurrentState`, `restorePreviousState`, `pop` | `SearchTreeHandler`, `SearchTreeStackEntry`, `SearchTreeState`, `EngineState`, `TableauState`; also context-dependent `CDSearchTreeHandler`/`TrailEntry` structures. The concrete state model has changed. |
| Solver status | `Reluplex.h::solve`: checks bounds and ReLUs for SAT, invokes `progress`, backtracks through `SmtCore`, and returns UNSAT on exhausted stack/infeasibility | `Engine::processInputQuery/solve`, `IEngine::ExitCode`, and explicit extraction of a solution into `InputQuery`; modern result modes include UNKNOWN. |
| Numerical recovery | `Reluplex.h::restoreTableauFromBackup`, `checkDegradation`, `reluplex/FloatUtils.h` | `src/engine/PrecisionRestorer`, `DegradationChecker`, `src/common/FloatUtils`; exact HOL arithmetic currently abstracts from all these numerical operations. |
| Certificates | No comparable standalone proof-tree/checker component was found in the inspected Reluplex core files | Marabou's `src/proofs/` contains the tree, contradiction vectors, propagation lemmas, native checker and writers. This is the practical evidence source for future work. |

The Reluplex README's implementation guide was checked against `solve`,
`fixOutOfBounds`, `pivot`, `SmtCore` state management, and the pair/bound classes.
Its GLPK patch and wrapper were inspected as integration points; the bundled
GLPK implementation was not audited or built.

The reusable mathematical ideas are assignments satisfying a linear system,
sign-dependent bounds, the two ReLU phases, and case analysis covering all
models. Our current HOL result formalizes that phase coverage. It establishes
no correctness claim about either historical or current pivot, update,
backtracking, or conflict-analysis code.
