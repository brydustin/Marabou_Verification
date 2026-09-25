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

## Pivot and simplex-step details that affect the model

Inspected for [TABLEAU_PIVOT.md](TABLEAU_PIVOT.md); all in `src/engine/`.

* `Engine::performSimplexStep` (Engine.cpp 632–831) asks the active entry
  strategy for candidates, computes the change column `d = B⁻¹A_e`, and picks
  a leaving variable. It retries other candidates while the pivot magnitude
  is below `ACCEPTABLE_SIMPLEX_PIVOT_THRESHOLD`. It throws
  `InfeasibleQueryException` only when no candidate exists with a fresh cost
  function and an accurate assignment (776–786).
* `pickLeavingVariable` uses `harrisRatioTest` (Tableau.cpp 1057–1440),
  since `USE_HARRIS_RATIO_TEST` is `true` (GlobalConfiguration.cpp 71).
  Pass 1 finds the minimal ratio against bounds relaxed by a tolerance. Pass
  2 picks the largest pivot among basics within it. The entering variable's
  range wins ties, giving a bound flip. `standardRatioTest` breaks the same
  tie in favour of a basic.
* Basic bounds in the ratio test depend on `basicCost`: an out-of-bounds
  basic is limited by its violated bound or is unconstrained. Negative
  ratios are clamped to zero when costs are stale.
* `performPivot` (696–801) checks the pivot row against the pivot column
  (765–769). `updateAssignmentForPivot` (2345–2457) writes the entering
  variable's new value into the leaving slot. It sets the leaving variable
  to a bound chosen from its status and direction (2413–2433). Only then are
  the index maps swapped (779–782). `performDegeneratePivot` (803–850) swaps
  the maps (828–831) and then the two array entries (839–841); its values
  do not change.
* `Engine::fixViolatedPlConstraintIfPossible` (833–924) uses the degenerate
  pivot to make a basic variable nonbasic before setting its value.

The HOL model sets every tolerance to zero and uses a fresh core cost
function. It covers the Harris test, pivots, bound flips and the index
arrays exactly. It does not model the entry strategies, the retry search,
refactorization or `MalformedBasisException`.

## Initialization details that affect the model

Inspected for [TABLEAU_INITIALIZATION.md](TABLEAU_INITIALIZATION.md); all in
`src/engine/Engine.cpp` unless noted.

* On the native LP path, `processInputQuery` (1414–1598) runs these steps in
  order:
  * `createConstraintMatrix`;
  * `removeRedundantEquations`;
  * `selectInitialVariablesForBasis` on the matrix *before* auxiliaries;
  * `addAuxiliaryVariables`;
  * `augmentInitialBasisIfNeeded`;
  * `initializeTableau`.
* `createConstraintMatrix` (1061–1089) throws on non-`EQ` rows. It assigns
  each addend's coefficient, so a repeated variable keeps the last one.
* `selectInitialVariablesForBasis` (1115–1288) returns only auxiliaries when
  `ONLY_AUX_INITIAL_BASIS` holds, which it does not by default
  (GlobalConfiguration.cpp 98). Otherwise it builds a lower-triangular block
  of original columns: it diagonalizes singleton rows and else excludes the
  densest column. It uses `FloatUtils::isZero` for nonzero tests.
* `Tableau::initializeTableau` (Tableau.cpp 336–374) numbers the basics in
  the given order and the nonbasics in increasing variable order. It sets
  every nonbasic to its lower bound, then `computeAssignment` (376–411)
  solves for the basics.
* `PL_CONSTRAINTS_ADD_AUX_EQUATIONS_AFTER_PREPROCESSING` is true
  (GlobalConfiguration.cpp 80). In every captured run the ReLU auxiliaries
  exist before that call, introduced by the harness or by native
  preprocessing, so it adds no rows; `snapshot_steps` checks the row count.

## Bound application details that affect the model

Inspected for [TABLEAU_BOUND_UPDATE.md](TABLEAU_BOUND_UPDATE.md); all in
`src/engine/`.

* `BoundManager::setLowerBound` (BoundManager.cpp 172–184) changes a bound
  only if the value is strictly greater, by an exact comparison. It marks
  the bound in `_tightenedLower` and, if the variable's bounds now cross,
  calls `recordInconsistentBound` (161–170). That records only the first
  crossing. The crossing test `consistentBounds(variable)` uses
  `FloatUtils::gte`. The upper bound is symmetric.
* `tightenLowerBound` (145–151, and 315–328 with a row explanation) then
  calls `Tableau::updateVariableToComplyWithLowerBoundUpdate` (Tableau.cpp
  1785–1805). A nonbasic below the new bound is moved onto it by
  `setNonBasicAssignment(…, true)`. A basic has its status recomputed, and
  the cost function is invalidated if the status changed.
* `propagateTightenings` (268–284) notifies watchers of every pending bound
  in variable order and clears the flags.
* `Engine::solve` throws `InfeasibleQueryException` when
  `Tableau::allBoundsValid` (the `_consistentBounds` flag) fails
  (Engine.cpp 313–317). `explainSimplexFailure` starts from
  `getInconsistentVariable`.
* `Engine::applySplit` (1994–2141) resets the explanation of each split
  bound. With proofs, it records the bound with
  `GroundBoundManager::addGroundBound(…, isPhaseFixing = true)` (2114, 2128)
  when it is stronger, then tightens it.
* `RowBoundTightener::tightenOnSingleInvertedBasisRow` (RowBoundTightener.cpp
  237–402) bounds a row's basic variable, then each nonbasic with a
  coefficient of at least 0.01. It subtracts or adds 10⁻⁶ and throws on a
  crossing.

## Native ReLU split details that affect the model

Inspected for [TABLEAU_RELU_SPLIT.md](TABLEAU_RELU_SPLIT.md).

* `ReluConstraint::transformToUseAuxVariables` (ReluConstraint.cpp 936–978)
  adds `f − b − aux = 0`, `aux ≥ 0` and `aux ≤ −lb(b)` (0 if `lb(b) > 0`).
  From then on `getActiveSplit` (683–705) is bound-only (`b ≥ 0`,
  `aux ≤ 0`); `getInactiveSplit` (674–681) is `b ≤ 0`, `f ≤ 0`.
* `getCaseSplits` (597–641) puts the active split first when the direction
  heuristic says so, or when `f`'s assignment is positive; otherwise the
  inactive split comes first.
* `getEntailedTightenings` (827–916) always proposes `f ≥ 0` and, with the
  auxiliary in use, `aux ≥ 0`.
* `SearchTreeHandler::performSplit` (SearchTreeHandler.cpp 133–225) obtains
  the splits and disables the constraint. It stores the engine state
  (bounds only) and pushes the context, then applies the first split,
  asserting that it has no equations. The others are kept as alternatives
  on the stack.
* `Engine::solve` calls `explicitBasisBoundTightening` (Engine.cpp 287–296,
  2269–2294) at the top of each native main-loop iteration, so row
  tightening follows every split.

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

The [binary split capture](SOLVER_RELU_SPLIT_CAPTURE.md) now exercises
`src/engine/Engine.cpp::performConstraintFixingStep/reportPlViolation`,
`src/engine/SearchTreeHandler.cpp::reportViolatedConstraint/performSplit/popSplit`,
and `ReluConstraint::getCaseSplits/getActiveSplit/getInactiveSplit` in a native
solve. The harness sets the existing `Options::CONSTRAINT_VIOLATION_THRESHOLD`
to 1. Native search creates the two proof children, applies their phase bounds,
and closes both. `JsonWriter::writeUnsatCertificateNode` emits inactive first;
the importer identifies phases and the HOL certificate stores active first.
The run records one split, two pops, three `NUM_TABLEAU_PIVOTS`
(`src/engine/Tableau.cpp::performPivot/performDegeneratePivot`), and two
explained leaves. Both child contradictions and the parent replay without
kernel or importer changes. This does not verify the search or pivot code.

The [single auxiliary introduction](TABLEAU_AUXILIARY.md) formalizes one
iteration's mathematical transformation in
`src/engine/Engine.cpp::addAuxiliaryVariables` (line 1290): append coefficient
`-1` for a fresh variable, fix both bounds to the old scalar, and set the
scalar to zero. `Query.cpp::setLowerBound/setUpperBound` store those bounds.
`Engine::createConstraintMatrix` rejects non-equalities before this native
initialization path. The new checked rational function verifies global
freshness and selection, constructs the transformed query, and has a
real-semantic equivalence theorem. Its result matches the earlier linear
capture exactly, allowing that certificate to prove an explicit pre-auxiliary
query UNSAT. The native allocation loop, preceding redundant-row removal,
floating-point storage, and decoder remain unverified.

[Finite composition](TABLEAU_AUXILIARY_SEQUENCE.md) now checks a list of
`(equation index, fresh variable)` pairs, using each intermediate query.
For the binary-split input, the five steps `(0,9),…,(4,13)` give exactly
the earlier processed snapshot, after a proved arithmetic reordering of
`f-b-a` to `-b+f-a`. The original order is in the `relu_split` branch of
`Isabelle/tools/solver_capture/capture.cpp::main`; `snapshot` writes the
matrix by increasing column index. The composition and reused native
certificate prove the explicit pre-tableau query UNSAT. The source and step
list in that first example are hand-written HOL data.

[Source capture/import](SOURCE_QUERY_CAPTURE.md) now obtains those inputs
automatically. `src/engine/InputQuery.cpp::generateQuery` (line 349) copies
equations and bounds and duplicates constraints without preprocessing.
The external `capture.cpp::snapshot_source` serializes this copy before
engine construction, using `Query::getEquations/getPiecewiseLinearConstraints`
and the bound getters. After initialization, `snapshot_steps` observes one
new `-1` column per row and proposes its introduction. The HOL sequence
must construct exactly the independent processed snapshot before the native
proof is used. All five native scenarios now have generated source-query
UNSAT theorems. This verifies the explicit mathematical bridge; C++ extraction,
native initialization, and byte decoding remain unverified.

[Fresh ReLU auxiliary introduction](RELU_AUXILIARY.md) now formalizes the
new-variable branch of
`src/engine/ReluConstraint.cpp::transformToUseAuxVariables` (lines 936–978).
It retains the ReLU, adds `f-b-a=0` and `a≥0`, and uses `max(0,-l)` as the
finite auxiliary cap. The native method reads `existsLowerBound/getLowerBound`
from `PiecewiseLinearConstraint.h` (local map or bound manager), whereas the
checked HOL interface requires an explicit input lower-bound atom. With no
finite cap, HOL omits the upper bound rather than storing infinity.
`Preprocessor::informConstraintsOfInitialBounds` notifies the constraints
before `transformConstraintsIfNeeded` invokes their transformation methods.
The C++ `_auxVarInUse` no-op branch and variable-count allocation are not
modeled; HOL checks global syntactic freshness and constructs a new extension.

Model extension assigns `a=f-b=ReLU(-b)`; projection forgets that coordinate.
The rational wrapper composes the step with existing scalar-fixed introductions
and proof replay. Its result for an explicit four-variable HOL query equals
the previously captured `relu_aux` five-variable source, whose native proof
is reused. That earlier native capture supplied its ReLU auxiliary already.

The subsequent [native introduction capture](NATIVE_RELU_INTRO_CAPTURE.md)
uses `capture.cpp::introduce_native_relu_aux` to snapshot a plain four-variable
`Query`, call `Preprocessor::informConstraintsOfInitialBounds` and the real
`ReluConstraint::transformToUseAuxVariables`, record its selected variables
and finite lower bound, and snapshot the independent five-variable result.
The three tableau introductions and full native UNSAT proof are then captured
as before. A separate six-artifact importer emits exact result equality,
before/processed equisatisfiability, and before-query UNSAT theorems.
This executes one native transformation directly, with general preprocessing
disabled; extraction, bound-cache refinement and byte decoding are unverified.

The [inequality introduction extension](INEQUALITY_AUXILIARY.md) models
`Preprocessor.cpp::makeAllEquationsEqualities` (lines 224–244), called near
the start of `Preprocessor::preprocess`. It appends coefficient +1 for a
fresh slack in both directions, with a lower zero bound for LE and an upper
zero bound for GE. The function is private in `Preprocessor.h`.
One-step and finite-sequence soundness are now proved mathematically; these
introductions have not yet been captured from a native preprocessing run.
The current native file pipeline requires finite bounds in both directions,
so the missing opposite slack bound must be justified separately.

[Finite ReLU auxiliary composition](RELU_AUXILIARY_SEQUENCE.md) now corresponds
to multiple such calls. `Preprocessor.cpp::transformConstraintsIfNeeded`
(lines 212–216) iterates the constraint transformation methods. Our harness
`capture.cpp::introduce_native_relu_aux_sequence` snapshots two plain ReLUs,
notifies their initial bounds once, calls both real methods and records the
ordered introductions. HOL checks global freshness against each current
query, constructs each result, and checks the entire final snapshot.
The accepted `relu_sequence` run goes from six to eight to thirteen variables,
with two `ReluConstraint::notifyUpperBound` input-to-output lemmas and a leaf.

A separate exploratory query produced output-lower-to-auxiliary-upper evidence
in `ReluConstraint.cpp::notifyLowerBound`, in the positive
`(variable == _f || variable == _b)` branch (around lines 177–196).
The [output-based case](RELU_OUTPUT_BOUND_PROPAGATION.md) is now checked
separately from the input-lower rule. `Checker.cpp::checkReluLemma` around
lines 674–678 tests the explained output lower bound plus epsilon; HOL
requires strict positivity of the exact rational premise and two checked
implications for the auxiliary equation. The full preserved proof replays
without filtering nodes. A fresh `relu_chain` run reproduces its six data
artifacts and records full provenance. The native epsilon policy and C++
implementation remain unverified.

The dual [positive-auxiliary branch](RELU_AUX_LOWER_BOUND_PROPAGATION.md) is
`ReluConstraint.cpp::notifyLowerBound`, lines 207–226:
`_auxVarInUse && variable == _aux && FloatUtils::isPositive(bound)`.
`checkIfLowerBoundUpdateFixesPhase` (lines 125–133) first marks the phase
inactive. In proof mode the branch calls
`BoundManager::addLemmaExplanationAndTightenBound(_f, 0, UB, {_aux}, LB, ...)`,
which records a `PLCLemma` only if `f`'s upper bound actually tightens
(`BoundManager.cpp`, lines 414–494), then tightens `_b <= -bound` through the
tightening row as an explained linear update, not as a lemma.
`Checker.cpp::checkReluLemma`, lines 685–689, accepts `causingVar == aux`, LB,
`affectedVar == f`, UB when the explained bound plus epsilon is positive.
`BoundManager::propagateTightenings` (lines 268–284) notifies constraints in
ascending variable index, lower before upper; the `relu_aux_inactive` capture
gives the auxiliary index 0 so that its notification precedes the output's.

For SAT results, `Engine::extractSolution` (`Engine.cpp`, lines 1736–1775)
writes `Tableau::getValue(i)` into `IQuery::setSolutionValue` for each variable
of the supplied query; with preprocessing disabled no variable is merged,
fixed or renumbered. The `relu_sat` harness scenario applies it to a copy of
the processed query and serializes each double as a round-trip decimal and an
exact hexadecimal float. Marabou's own SAT acceptance
(`ReluConstraint::satisfied`, `Engine::adjustAssignmentToSatisfyNonLinearConstraints`)
uses tolerances; the [exact assignment checker](SAT_ASSIGNMENTS.md) does not.

ReLU phases fixed before search
([RELU_PHASE_FIXING.md](RELU_PHASE_FIXING.md)): with preprocessing disabled,
`Engine::invokePreprocessor` calls `Preprocessor::informConstraintsOfInitialBounds`
(`Preprocessor.cpp`, lines 1121–1142) on its copy of the query before any
bound manager exists. `ReluConstraint::notifyLowerBound`/`notifyUpperBound`
then take their `_boundManager == nullptr` branch, which only records the
bound and calls `checkIfLowerBoundUpdateFixesPhase` /
`checkIfUpperBoundUpdateFixesPhase` (lines 125–146). The latter uses the
non-proof policy (`!isPositive`), because `proofs` is computed from the
absent bound manager. `Engine::solve` registers the bound manager, then
calls `applyAllValidConstraintCaseSplits` (lines 202–208). Each fixed,
active constraint is disabled, its `getValidCaseSplit()` (= `getImpliedCaseSplit`,
lines 712–725) is recorded with `SearchTreeHandler::recordImpliedValidSplit`,
and it is applied by `Engine::applySplit`. In proof mode, `applySplit` adds
only strictly tighter split bounds, as new ground bounds with
`isPhaseFixing = true` and a reset explanation (lines 2108–2134). No
certificate node records them, so `Checker::checkNode` never sees them.

Native preprocessing ([NATIVE_PREPROCESSING.md](NATIVE_PREPROCESSING.md)):
`Engine::processInputQuery(input, true)` makes `invokePreprocessor`
(`Engine.cpp`, lines 980–1011) call
`Preprocessor::preprocess(input, PREPROCESSOR_ELIMINATE_VARIABLES)`
(`Preprocessor.cpp`, lines 61–180; the elimination flag is `true` in
`GlobalConfiguration.cpp`, line 79). After it, `processInputQuery`
(lines 1414 onward) runs symbolic tightening, simulation and MILP
tightening. With no network-level reasoner and the harness's `none`
tightening option these change nothing here. `InfeasibleQueryException` from
preprocessing is caught at lines 1574–1583: the engine sets `UNSAT` and
returns false, with no certificate. `Engine::extractSolution`
(lines 1736–1784) maps a solution back through `variableIsMerged`,
`variableIsFixed` and `getNewIndex`. The tightening loop accepts an
improvement only above `PREPROCESSOR_BOUND_TOLERANCE`, and snaps intervals
narrower than `PREPROCESSOR_ALMOST_FIXED_THRESHOLD` (`1e-5`, line 82) to a
point (e.g. `processEquations`, lines 470–481). The exact projection check
rejects any result that relies on such a tolerance.
