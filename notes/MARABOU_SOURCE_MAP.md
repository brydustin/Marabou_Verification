# Marabou source map

Inspected on 2026-09-22. This map describes the local checkout, not an unspecified
latest release. Marabou commit: `1c2f4788c32e2f4e407c356b763a8025c5578722`
(2026-06-18, “Generation of Alethe proofs (#894)”). All paths below are relative
to `upstream/Marabou/`. The upstream checkout was clean at inspection.

The top-level `README.md` describes an SMT-based verifier and the current solver
modes. Implementation observations below come from the named source files;
paper claims and our mathematical choices are recorded separately.

| Mathematical concept | Actual implementation and important entry points |
| --- | --- |
| Variable | An `unsigned` index; `src/engine/Equation.h`, `Equation::Addend::_variable`; `InputQuery::setNumberOfVariables`, `getNewVariable` in `src/engine/InputQuery.{h,cpp}`. |
| Valuation / candidate assignment | `src/engine/Tableau.h`: `_basicAssignment`, `_nonBasicAssignment`, and variable/index maps; `Tableau::getValue`. External solutions use `InputQuery::setSolutionValue/getSolutionValue` and `_solution`; analogous methods exist on `Query`. Values are `double`. |
| Equation or inequality | `src/engine/Equation.{h,cpp}`: `Equation`, `Addend`, `_addends`, `_scalar`, `_type`, `addAddend`, `setScalar`; types `EQ`, `LE`, `GE` mean sum of addends compared to scalar. Repeated variables can be consolidated by `removeRedundantAddends`. |
| Affine linear expression | `src/common/LinearExpression.{h,cpp}`: `LinearExpression::_addends` (`Map<unsigned,double>`), `_constant`, `evaluate`. This differs from Equation's list representation. |
| Lower / upper bounds | `InputQuery` stores context-dependent maps; `Query` stores maps in `src/engine/Query.h`. `src/engine/BoundManager.{h,cpp}` centralizes solver bounds and propagation; `setLowerBound`, `tightenLowerBound`, `tightenUpperBound`, `consistentBounds`. `src/engine/Tightening.h`: `(variable,value,LB/UB)`. |
| Input query | `src/engine/IQuery.h`, `InputQuery.{h,cpp}`, `Query.{h,cpp}`. `InputQuery` supports push/pop; `generateQuery` produces a non-context-dependent `Query` for internal processing. Equations, bounds, PL and nonlinear constraints are distinct collections. |
| ReLU(b,f) | `src/engine/ReluConstraint.{h,cpp}`: `_b`, `_f`, optional `_aux`; `satisfied`, `getCaseSplits`, `getCaseSplit`, `getActiveSplit`, `getInactiveSplit`, `getEntailedTightenings`, `transformToUseAuxVariables`. |
| Other piecewise-linear constraints | `src/engine/PiecewiseLinearConstraint.{h,cpp}`, `PiecewiseLinearFunctionType.h`; derived `AbsoluteValueConstraint`, `SignConstraint`, `MaxConstraint`, `DisjunctionConstraint`, `LeakyReluConstraint` in correspondingly named files. `NonlinearConstraint` is separate (e.g. sigmoid, bilinear, softmax). These are outside our initial fragment. |
| Tableau | `src/engine/ITableau.h`, `Tableau.{h,cpp}`, `TableauRow.{h,cpp}`. `Tableau` stores sparse `_A`, right-hand side `_b`, basis information, and assignments; `initializeTableau`, `computeAssignment`, `getTableauRow`. |
| Simplex / pivot | `src/engine/Engine.cpp`: `performSimplexStep`; `src/engine/Tableau.cpp`: `computeChangeColumn`, `pickLeavingVariable`, `performPivot`, `performDegeneratePivot`; `EntrySelectionStrategy`, `ProjectedSteepestEdge`, `DantzigsRule`, `BlandsRule`, `CostFunctionManager` in `src/engine/`. |
| Bound tightening | `src/engine/RowBoundTightener.{h,cpp}` for linear rows; `BoundManager::propagateTightenings`; activation-specific notification/tightening methods, e.g. `ReluConstraint::notifyLowerBound/notifyUpperBound/getEntailedTightenings`; `Engine::applyAllBoundTightenings`, `explicitBasisBoundTightening`. `Preprocessor` also tightens and rewrites queries. |
| Case split | `src/engine/PiecewiseLinearCaseSplit.{h,cpp}`: a list of `Tightening`s and `Equation`s; `storeBoundTightening`, `addEquation`; `Engine::applySplit` applies these to solver state. |
| SAT result | `src/engine/IEngine.h`: `ExitCode::SAT`; `Engine::solve`, `extractSolution` in `Engine.cpp`; `Marabou::solveQuery` and `displayResults` in `Marabou.cpp`. A floating-point assignment is reported, not an Isabelle theorem. |
| UNSAT / conflict | `InfeasibleQueryException.h`; bound inconsistency or failed native simplex step leads to backtracking in `Engine::solve`; exhaustion sets `IEngine::UNSAT`. `Engine::explainSimplexFailure`, `certifyInfeasibility`, `computeContradiction`, `writeContradictionToCertificate` provide proof evidence when enabled. |
| Branching / search state | `src/engine/SearchTreeHandler.{h,cpp}`: `needToSplit`, `performSplit`, `popSplit`, `pushContext`, `popContext`; `SearchTreeStackEntry.h`, `SearchTreeState.h`, `EngineState.{h,cpp}`, `TableauState.{h,cpp}`. `CDSearchTreeHandler.{h,cpp}` and `TrailEntry.h` also implement context-dependent decision/implication tracking. |
| Proof tree / leaf evidence | `src/proofs/UnsatCertificateNode.{h,cpp}`, `Contradiction.{h,cpp}`, `PlcLemma.{h,cpp}`, `BoundExplainer.{h,cpp}`. A contradiction is a sparse row-combination vector or an inconsistent-bound variable. Node flags include delegation and SAT-solution flags. |
| Existing proof check/export | `src/proofs/Checker.cpp`: `check`, `checkNode`, `checkContradiction`, `checkAllPLCExplanations`; `UnsatCertificateUtils.cpp`: row combinations and sign-selected bounds; `AletheProofWriter.{h,cpp}`, `SmtLibWriter.{h,cpp}`, `JsonWriter.{h,cpp}`. These C++ components are not verified here. |
| Numerical comparisons | `src/common/FloatUtils.{h,cpp}` and `src/configuration/GlobalConfiguration.{h,cpp}`: tolerance-based equality/sign tests. The HOL semantics uses exact real comparisons instead. |

## Main native solver path

1. `src/engine/main.cpp` calls `marabouMain` in `MarabouMain.cpp`, which selects
   the ordinary `Marabou().run()` path or other configured modes.
2. `Marabou.cpp` prepares an `InputQuery` and calls `Marabou::solveQuery`.
   This invokes `Engine::processInputQuery`, then `Engine::solve` on success.
3. `Engine::processInputQuery` invokes preprocessing, obtains an internal
   `Query`, constructs the constraint matrix and auxiliary variables, chooses a
   basis, initializes the tableau and bound managers, and (if enabled) starts
   the certificate tree. Preprocessing itself can find infeasibility.
4. `Engine::solve` alternates linear feasibility work, bound propagation,
   activation repair/search, and splitting. In the native LP path,
   `performSimplexStep` selects entering/leaving variables and pivots. Failure
   after recomputing assignment and cost information throws
   `InfeasibleQueryException` when not optimizing.
5. If the candidate meets the linear and activation checks, `solve` sets SAT.
   On infeasibility it optionally calls `explainSimplexFailure`, then
   `SearchTreeHandler::popSplit`; no remaining branch sets UNSAT. Other exit
   codes include UNKNOWN, TIMEOUT, ERROR and QUIT_REQUESTED; `false` is not
   synonymous with UNSAT.
6. `Marabou::solveQuery` requests certificate checking/writing for proof-enabled
   UNSAT after solving, and extracts a solution for SAT. The certificate path
   starts from an internal processed problem; equivalence to the original
   input still requires justification.

## ReLU split details that affect the model

`ReluConstraint.cpp:674` (`getInactiveSplit`) adds `b <= 0` and `f <= 0`.
The intended equality `f = 0` needs the surrounding `f >= 0` invariant.
`getActiveSplit` at line 683 adds `b >= 0` and either `b - f = 0` or
`aux <= 0`. `transformToUseAuxVariables` at line 936 creates
`f - b - aux = 0` with `aux >= 0`, which explains the latter form.

Our children explicitly contain `y = 0` or `y - x = 0` and the relevant sign
bound, and remove the selected ReLU atom. This is a mathematical replacement
rule, not a proof that `Engine::applySplit` maintains these C++ invariants.
Both branches include the zero input; no exclusive partition is claimed.

## Existing proof evidence is not exact checking

`Checker::checkContradiction` uses `double` row combinations and
`FloatUtils::isNegative`; PLC checks use a certification tolerance.
`Checker::checkNode` returns true for delegated leaves and SAT-solution leaves
in its wider checking protocol. `Engine::certifyUNSATCertificate` explicitly
reports that delegated leaves require separate certification. Its Alethe path
writes a proof and sets a success flag while stating that separate checking is
required. None of these flags alone establishes exact UNSAT of the original
query. The Alethe writer does recompute combinations using GMP rationals
(`linearCombinationMpq`), while the SMT-LIB writer uses finite decimal
formatting. See [LINEAR_CERTIFICATES.md](LINEAR_CERTIFICATES.md) for the exact
arithmetic investigation and export limitations.

The project's [rational leaf checker](RATIONAL_LINEAR_CHECKER.md) and recursive
tree checker have HOL soundness theorems. A [restricted JSON
adapter](CERTIFICATE_IMPORT.md) now reconstructs normalized-inequality weights
from native row/bound evidence and binary auxiliary-form ReLU splits. Three
initial fixtures emitted by the real C++ writer replay in HOL; their evidence
was hand constructed. Four further [propagation fixtures](RELU_BOUND_PROPAGATION.md)
now replay native `PLCLemma` records for input-to-output ReLU upper bounds with
empty explanations. The relevant producing calls are
`ReluConstraint.cpp::notifyUpperBound` and
`BoundManager.cpp::addLemmaExplanationAndTightenBound`; serialization is
`JsonWriter.cpp::writePLCLemmas`. These component fixtures do not establish a
solver execution or preprocessing correctness.

The [exact linear implication checker](RATIONAL_LINEAR_IMPLICATION.md) now
supports nonempty explanations for that same rule. Its source correspondence
is `src/proofs/UnsatCertificateUtils.cpp::getExplanationRowCombination(unsigned var, ...)`:
`c = e_var + wᵀA`, followed by `computeCombinationUpperBound` using sign-selected
ground bounds. The adapter reconstructs a checked bound before applying the
ReLU rule. Two further writer fixtures call
`src/proofs/BoundExplainer.cpp::updateBoundExplanation/getExplanation` and
`UNSATCertificateUtils::computeBound` on hand-supplied rows. Query and tree
assembly remain in the harness; these calls do not execute `Engine::solve`.

The subsequent [solver capture](SOLVER_CAPTURE.md) executes the real
`Engine::processInputQuery(input, false)` and `Engine::solve(10)`. A public-API
harness snapshots `getQuery` and checks it against `storeState/getGroundBound`
before solving, then passes `getUNSATCertificateRoot` directly to the native
writer. This one linear execution's row contradiction now replays in HOL.
No ReLU rule or pivot is exercised, and the C++ capture is not a verified
translator from original inputs.

The [ReLU solver capture](SOLVER_RELU_CAPTURE.md) now exercises native
`RowBoundTightener::examineInvertedBasisMatrix/tightenOnSingleInvertedBasisRow`,
`BoundManager::propagateTightenings`, and the proof-mode negative-input branch
of `ReluConstraint::notifyUpperBound` during `Engine::solve`. Its single PLC
lemma carries a nonempty `BoundExplainer` row vector. That lemma and the final
row contradiction replay unchanged in HOL, and the linear relaxation is
separately proved satisfiable. No pivot or binary proof split occurs.
The notes also record the additional auxiliary-upper-bound lemma emitted by
broader input variants through `notifyLowerBound`. The
[auxiliary extension](RELU_AUX_BOUND_PROPAGATION.md) now supports that rule.
It additionally inspects `ReluConstraint::transformToUseAuxVariables` and
`UNSATCertificateUtils::computeCombinationLowerBound`, reconstructs the input
lower explanation, and checks both directions of the auxiliary equation.
Two new native runs replay: the earlier broader variant, and an active-phase
case where the auxiliary rule is the sole nonlinear inference.
