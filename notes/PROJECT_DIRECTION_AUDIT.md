# Project direction audit — 2026-09-23

**Finding: the present project is primarily Level 1: verified checking of
Marabou outputs. It has a useful semantic foundation and source-grounded
algebraic results for selected operations, but no formalized Marabou solving
procedure. Continued certificate/import expansion alone will not establish
the proposed solver-level correctness theorem.**

This assessment uses the working directory, including uncommitted and
untracked work, rather than just the last commit. Feature work was paused
when this audit was requested. No implementation or theory was changed
during the audit; this report and its inventory are documentation additions.
The preceding integration remains an incomplete engineering checkpoint.

Inspection covered the whole directory inventory, the main session's theory
declarations/dependencies and proof mechanisms, the semantic/checker/
transformation definitions, import/capture tools and tests, project notes and
history, both upstream READMEs, and the relevant native query, tableau,
bound, ReLU, search and historical Reluplex code. This is an architectural
and assurance-boundary audit, not a line-by-line correctness review of every
upstream file, bundled dependency, benchmark or generated build artifact.

## 1. CURRENT STATE

### Files and dependencies

The authoritative current session is [Isabelle/ROOT](../Isabelle/ROOT):
`Marabou_Verification = HOL +`, with `quick_and_dirty = false`.
There are **77 registered top-level theories**: 26 core theories,
18 example theories and 33 imported/file-binding theories; 7,785 lines total.
Every top-level theory is registered. The ignored generated directory also
contains 119 replay/scratch theory files; these are not 119 additional
main-session theories.

The [complete theory inventory](PROJECT_THEORY_INVENTORY.md) lists **every
theory, direct import, declared object and named theorem/lemma/corollary**.
The principal layers are:

| Layer | Principal files and objects | Principal guarantees |
| --- | --- | --- |
| Real query syntax | `Marabou_Syntax.thy`: `var`, `valuation`, `linexpr`, `linear_constraint`, `bound`, `relu_constraint`, `query` | Definitions, not algorithm correctness. |
| Real semantics | `Marabou_Semantics.thy`, `Linear_Constraints.thy`, `ReLU_Constraints.thy`, `Query_Semantics.thy` | Expression algebra, constraint satisfaction, ReLU phases, inconsistent bounds, SAT/UNSAT definitions. |
| Semantic case analysis | `ReLU_Splitting.thy`: `active_split`, `inactive_split` | `models_relu_split`, `satisfiable_relu_split`, `unsatisfiable_relu_split`. |
| Exact arithmetic | `Rational_Linear_Constraints.thy`, `Rational_Linear_Certificates.thy`, `Rational_Linear_Implication.thy` | Rational-to-real embedding, normalization, `check_linear_leaf_sound`, `check_linear_implication_sound`, `check_linear_bound_sound`. |
| Four ReLU propagation rules | `ReLU_Bound_Propagation.thy`, `ReLU_Aux_Bound_Propagation.thy`, `ReLU_Output_Bound_Propagation.thy`, `ReLU_Aux_Lower_Bound_Propagation.thy` | Checked consequences preserve the real model set, under explicit premises. |
| Recursive refutations | `Rational_Proof_Trees.thy`: `certificate`, `check_certificate` | `check_certificate_sound`, by induction on a supplied finite certificate. |
| Scalar-fixed auxiliaries | `Tableau_Auxiliary.thy`, `Rational_Tableau_Auxiliary.thy`, `Tableau_Auxiliary_Sequence.thy` | Model extension/projection and equisatisfiability for checked fresh introductions and their finite composition. These files do not define a tableau state. |
| ReLU auxiliaries | `ReLU_Auxiliary.thy`, `Rational_ReLU_Auxiliary.thy`, `ReLU_Auxiliary_Sequence.thy` | The corresponding extension/projection and composition results for `f-b-a=0` and checked auxiliary bounds. |
| Inequality auxiliaries | `Inequality_Auxiliary.thy`, `Rational_Inequality_Auxiliary.thy`, `Inequality_Auxiliary_Sequence.thy` | LE/GE conversion using fresh signed slacks, preservation and composition. |
| Finite slack caps — latest work | `Bounded_Inequality_Auxiliary.thy` | Exact linear justification for the opposite finite slack bound; finite-sequence preservation; original-byte SAT/UNSAT transfer. |
| SAT witness validation | `Rational_Assignment.thy` | `check_rat_assignment_sound` and `check_rat_assignment_iff` for a supplied finite rational assignment with distinct names. |
| Project-defined input format | `Exact_Query_Format.thy` | `decode_query`, `decode_encode_query`, `same_constraints`, `decodes_like`, checked transfer to the meaning of exact file bytes. |
| Concrete applications | `Imported_Marabou_*.thy` and the 18 example theories | Kernel-checked instances, examples, and rejection/counterexample lemmas. |

The dependency spine is:

```text
real syntax → expression/constraint/query semantics → ReLU splitting
                         ↓
                rational embedding/normalization
                         ↓
             exact linear implications + ReLU rules
                         ↓
                 recursive certificate checker
                         ↓
          checked introductions and imported replay theorems
                         ↓
                  assignment/file-result theorems
```

Some mathematical preprocessing modules currently import the certificate
stack: e.g. `Rational_Tableau_Auxiliary` imports `Rational_Proof_Trees`.
That is harmless logically, but reflects the checker-oriented architecture.
A future solver layer should depend on reusable semantics/transformation
lemmas; it should not need a native certificate to execute its own transitions.
No reorganization was performed in this audit.

`Isabelle/tools/` contains untrusted Python reconstruction/import/driver code,
a local C++ capture harness, and a ReLU reachability probe.
`Isabelle/tests/` contains Python regressions, SML smoke tests, component
fixtures and native-run artifacts. `Isabelle/generated/` holds generated SML,
native build files, logs, replay sessions and exploratory captures.
The 28 pre-audit notes are mostly source maps and cumulative checker/import
milestone records. `CLAUDE_HANDOFF.md` is an explicitly marked historical
checker-oriented handoff. UAT sigmoid reuse is documented in
`notes/ACTIVATION_REUSE.md`; it is not part of this ReLU session.

Git contains one root commit, `60016b0`, dated 2026-09-22:
“Marabou proof certificates verified in Isabelle/HOL”.
Before adding this report/inventory, status showed 31 modified tracked paths
and 182 untracked entries; staging was empty. Many later theories therefore
exist only in the working tree. A checkout of HEAD does not reproduce the
audited development.

### Build and test results

`isabelle version` returned **`Isabelle2025-2`**.

The full build already running when the audit was requested completed:

```text
Command: isabelle build -v -D Isabelle
Finished Marabou_Verification (0:01:38 elapsed time, 0:07:28 cpu time, factor 4.57)
0:01:41 elapsed time, 0:07:28 cpu time, factor 4.40
Exit status: 0
```

The exact requested command was then run:

```text
$ isabelle build -D Isabelle
0:00:03 elapsed time
Exit status: 0 (up to date)
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited 0
with no output.

The engineering suite is **not fully green**:

```text
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
Ran 277 tests in 2.349s
FAILED (failures=3)
Exit status: 1
```

The failures are current-tool provenance hash mismatches:

* `test_bounded_inequality.NativeBindingTests.test_native_provenance_matches_current_inputs`;
* `test_marabou_query_file.ExampleTheoryTests.test_file_runs_reproduced_the_scenario_artifacts`,
  subcases `relu_sat` and `linear_unsat`.

A separate hash audit identifies four stale records: both
`file_inequality_relu_*_provenance.json` files have an older query-file importer
hash; `file_relu_sat_provenance.json` and `file_linear_unsat_provenance.json`
have older driver/importer hashes. The pre-audit refresh reran ten named
scenarios and the chain file, then stopped on a reused output-directory name.
These discrepancies were left visible, not repaired by rewriting hashes.
They are not failed HOL soundness proofs, but the unfinished milestone must
not be reported as a fully validated release.

The four existing standalone SML smoke scripts all exit 0:
8 leaf, 62 tree, 11 assignment and 16 inequality checks — 97 total.
The inequality export emits three nonexhaustive-pattern warnings in generated
`nth`, finite-set `image` and set-union helpers. The guarded index access and
list-derived finite sets explain their intended safe use; the warnings are
already documented. SML smoke success is not a proof of an SML compiler.
The new bounded-inequality functions are compilation-checked by Isabelle's
`export_code ... checking SML`, not covered by those older 97 smoke cases.

### Proof integrity and placeholders

Systematic whole-token searches over all 77 main and 119 generated theory
files found **zero** occurrences of `sorry`, `oops`, `axiomatization`,
`undefined`, `axioms`, `oracle`, `Skip_Proof`, `skip_proof`,
`cheat_tac` or `make_thm`. Searches of project ML/theory code found no
custom theorem-forging or oracle path, and no enabled `quick_and_dirty`.

A broader text search across project sources, notes and both upstream trees
found these words in documentation discussing the rules and 18 occurrences
of `undefined` in upstream text/source (including dependency/C++ usage).
They are not HOL proof placeholders. No matches for the four requested
tokens occurred in the project's theory/ML/Python/C++ source files.

The main ML helper, `Exact_Query_Text.check_file` in
`Exact_Query_Format.thy:154`, reads a file and compares it with the literal
byte list in a definition theorem; it raises an error on mismatch and does
not manufacture a theorem. Imported acceptance proofs use `code_simp`,
which reconstructs logical proofs, not an external solver success flag.

Guarded list indexing (`!`) does occur. The rational auxiliary introduction
functions check the index before selecting a row; real-level lemmas state
the required index/type hypotheses. This is not an admitted-proof shortcut.
HOL's normal logical foundations and libraries remain part of the trusted
foundation; this audit does not mean “no axioms anywhere in Isabelle/HOL.”

## 2. WHAT WE HAVE ACTUALLY VERIFIED

The theory establishes the following conservative claims.

1. **A real-valued query semantics.** Finite conjunctions of real linear
   constraints, bounds and exact ReLUs have a precise meaning.
2. **Complete semantic ReLU phase coverage.** For a selected ReLU belonging
   to a query, the union of the active and inactive child model sets is the
   original model set. The branches overlap harmlessly at zero.
3. **Sound exact refutation checking.** Nonnegative rational combinations
   of normalized linear inequalities can certify a contradiction. Exact
   linear implications and four specified ReLU consequences are sound.
   A finite tree combining these with checked binary splits proves UNSAT.
4. **Sound finite query transformations.** Checked fresh scalar-fixed,
   ReLU and signed inequality auxiliaries preserve satisfiability, with
   proved extension/projection relations. The new finite-cap layer composes
   those steps with already-verified linear implications.
5. **Sound witness checking.** An accepted rational assignment is a model
   over the existing real semantics.
6. **Concrete checked instances.** Supplied native artifacts and explicit
   exact input files yield individual real SAT/UNSAT theorems. The new
   inequality SAT and UNSAT file theories are included in the successful build.

The key current theorem is:

```text
check_certificate Q cert ⟹ unsatisfiable (embed_query Q)
```

Its premise is acceptance by our checker, not `Engine::solve` returning
UNSAT. Likewise `check_rat_assignment_iff` is completeness of checking the
given rational assignment, not completeness or termination of a solver.
No theorem says every UNSAT query has an accepted certificate, or every
real-satisfiable query will have a rational witness found by an algorithm.

No theorem currently verifies native simplex, a tableau pivot, candidate
assignment maintenance, bound-manager mutation, a search stack, native
phase bookkeeping, backtracking, the C++ numerical implementation, or
general preprocessing. Native runs exercising pivots are examples of
execution followed by output checking; their pivot steps were not replayed
as verified solver-state transitions.

## 3. ALIGNMENT WITH THE RESEARCH GOAL

| Requested category | Present status |
| --- | --- |
| A. Query semantics | Substantial, useful, exact and reusable. |
| B. Certificate checking | The central implemented architecture and principal executable artifact. |
| C. Abstract Marabou-like solver | Absent: no solving procedure or operational search state. |
| D. Actual Marabou operations | Partial: mathematical counterparts of selected source operations, with explicit abstraction gaps; no state-machine composition. |
| E. C++ refinement | Absent: no C++ semantics, representation relation or simulation theorem. |

Thus the project is **Level 1 plus reusable pieces for Level 2**.
It has not yet reached a formalization of the solving calculus.
The missing layer is not a few unsupported certificate constructors.

There is a relevant history distinction: the original brief explicitly
preferred a verified certificate semantics/checker and deferred larger
algorithm verification. The implementation followed that direction.
The present request establishes a different primary research target.
It would be inaccurate to say Claude alone silently diverted an existing
solver-verification architecture: the sole root commit and the handoff
already center certificate verification.

The related-work distinction is justified. The
[Imandra paper, revised February 2024](https://arxiv.org/abs/2307.06299)
describes an implemented proof checker and work toward completing its formal
verification. That supports overlap with Level 1; it does not itself prove
that all checker verification is now complete. This is not a comprehensive
novelty survey. The
[Marabou 2.0 paper](https://arxiv.org/html/2401.14461v2)
also distinguishes solver execution from proof production/checking.
Neither theorem-prover integration nor a verified checker establishes solver
algorithm correctness.

## 4. DRIFT OR MISALIGNMENT

The architectural commitment is visible at specific points:

* `Rational_Linear_Certificates.thy` consumes proposed weights; it does not
  search for a feasible assignment or choose a pivot.
* `Rational_Proof_Trees.thy:35` defines a supplied `certificate`;
  `check_certificate` recurses over it. Structural recursion on proof data
  does not implement the solver's search or prove that search terminates.
* `check_after_fixed_aux_sequence`, `check_after_relu_aux_sequence` and
  `check_after_inequality_aux_sequence` extend the trusted checking boundary
  backwards through preprocessing. They still terminate in certificate or
  assignment acceptance.
* `import_marabou_*.py`, `capture_marabou_solver.py`,
  `verify_query_file.py`, native fixtures, exact text decoding and tool-hash
  provenance increasingly package that Level-1 workflow.
* `CLAUDE_HANDOFF.md:27` explicitly states the checker architecture, and its
  roadmap A–E emphasizes rule coverage, source binding, preprocessing evidence,
  SAT witnesses and packaging.

These artifacts should remain. They supply independent regression evidence,
an exact semantic oracle for testing future operations, and a useful secondary
certification product. More parser features or native capture variants would,
however, mainly expand Level 1 while the solver-state gap remains untouched.

Potentially misleading names require careful qualification:

* `Tableau_Auxiliary` proves an equation transformation used in tableau
  initialization; it does **not** formalize a tableau.
* `Solver_ReLU_Examples` and `Imported_Marabou_Solver_*` concern evidence
  from solver runs, not the correctness of their execution traces.
* `certificate` is a project-defined calculus with reconstructed normalized
  row weights; it is not a faithful memory model of `UnsatCertificateNode`.
* `Marabou_Inequality_Preprocessor.ML` is a generated checker for a small
  sequence of transformations, not a verified implementation of the whole
  `Preprocessor`.
* The newest `prepare_inequalities.py` computes a **local** exact proposal.
  It does not call `Preprocessor::makeAllEquationsEqualities`. Its additional
  opposite bound is checked mathematically; a native preprocessing execution
  has not thereby been verified.

The documentation mostly makes these limitations explicit. The main problem
is research prioritization, not a discovered hidden proof bypass.
Some current status statements are stale: the README and mapping note still
describe native inequality-file integration as absent; the new theories now
build, but provenance/regression cleanup is incomplete. Historical “five
scenarios” and “first phase-coverage result” passages also coexist with later
results. The cumulative notes need a single current status index when work
resumes, rather than treating every historical next-target paragraph as live.

## 5. CORRESPONDENCE WITH ACTUAL MARABOU

### Reference revisions and operational scope

The inspected checkouts are clean:

* Marabou: `1c2f4788c32e2f4e407c356b763a8025c5578722`.
* ReluplexCav2017: `60b482eec832c891cb59c0966c9821e40051c082`.

Paths below beginning `src/` are relative to `upstream/Marabou/`.
The local harness builds actual pinned native engine sources, but excludes
the ordinary CLI/network parsers. It selects proof production, disables
general preprocessing and DeepSoI, and uses the native LP path.
This is a particular supported configuration, not the default full product.
The local README identifies DeepPoly and DeepSoI in the default configuration;
the Marabou 2.0 paper describes the same architectural distinction.

### Definition-family correspondence

The [existing formalization map](FORMALIZATION_MAP.md) is largely accurate
as a documented correspondence map; it expressly disclaims refinement.
The following covers the current semantic definitions that have a claimed
native counterpart. Rational versions and finite-sequence wrappers inherit
the indicated correspondence, not stronger implementation guarantees.
Pure proof helpers and concrete data constants are exhaustively named in the
inventory and do not each constitute a new C++ operation.

| HOL definition family | Actual source concept | Assessment |
| --- | --- | --- |
| `var` | `src/engine/Equation.h`, `Equation::Addend::_variable`; `InputQuery::{setNumberOfVariables,getNewVariable}` | Appropriate names; HOL naturals omit the declared count and unsigned range. |
| `valuation` | `Tableau::_basicAssignment/_nonBasicAssignment`, `Tableau::getValue`; `InputQuery::_solution` | Mathematical value assignment only; no storage or candidate-state relation. |
| `linexpr`, `eval_terms`, `eval_linexpr` | `src/common/LinearExpression.{h,cpp}`, `LinearExpression::evaluate`; `Equation::_addends` | Finite affine arithmetic. Lists, duplicate terms, explicit constants, exact reals differ from the C++ map/list and double operations. |
| `const_expr`, `var_expr`, `add_linexpr`, `scale_linexpr` | Generic algebra used with equations/expressions | Useful generic mathematics, no claim that a specific C++ operation is verified. |
| `LinearEq/Le/Ge`, `satisfies_linear` | `src/engine/Equation.{h,cpp}`, `EQ/LE/GE` and `_scalar` | Intended exact relation. The separate affine constant is absorbed into RHS to match Equation's representation. |
| `Lower/Upper`, `satisfies_bound` | `src/engine/Tightening.h`; `InputQuery`, `Query`, `BoundManager` | Conjunctive predicates, not overwrites, queues or context-dependent stores. |
| `relu`, `ReLU`, `satisfies_relu`, `satisfies_relu_constraint` | `src/engine/ReluConstraint.{h,cpp}`, `_b/_f`, `satisfied` at line 396 | Intended graph of max(0,b); native acceptance uses tolerances. |
| `query`, `satisfies_query`, `models`, `satisfiable`, `unsatisfiable` | `IQuery.h`, `InputQuery.{h,cpp}`, `Query.{h,cpp}` | Correct restricted logical specification; no claim that an exit code equals a semantic predicate. |
| `active_split`, `inactive_split`; rational versions | `ReluConstraint.cpp:674` `getInactiveSplit`; `:683` `getActiveSplit` | Complete canonical exact phases. Native inactive phase uses two upper bounds and an existing output lower bound; auxiliary active phase uses `a≤0`, `a≥0` and `f-b-a=0`. State/flag effects are absent. |
| `query_vars` and support helpers | Allocation freshness needed by `Engine::addAuxiliaryVariables` and ReLU/inequality creation | Conservative syntactic support, including zero terms. Not a proof of the native allocation invariant. |
| `introduce_fixed_aux`; `rat_fixed_aux_query`; checked single/sequence versions | `Engine.cpp:1290` `addAuxiliaryVariables` | Source-grounded algebra: `e=b` becomes `e-s=0` with `s=b`. Current code mutates rows/count/maps; those effects are not modeled. |
| `relu_aux_bounds`, `introduce_relu_aux`; rational/checking/sequence variants | `ReluConstraint.cpp:936` `transformToUseAuxVariables`; `Preprocessor.cpp:212` `transformConstraintsIfNeeded` | Source-grounded fresh `f-b-a=0`, `a≥0`, optional cap. Native cache, metadata and already-introduced no-op differ. HOL permits a second fresh auxiliary for the same ReLU. |
| `inequality_direction`, `inequality_atom`, `introduce_inequality_aux`; rational/sequence variants | `Preprocessor.cpp:224` `makeAllEquationsEqualities` | Source-grounded `e+s=b` with +1 coefficient for both directions; LE gives `s≥0`, GE gives `s≤0`. No verification of the surrounding preprocessing loop. |
| `rat_add_bound`; `check_relu_upper_bound` | `ReluConstraint::notifyUpperBound`, input branch; `BoundManager::addLemmaExplanationAndTightenBound` | Proves a consequence; does not model the mutating operation. |
| `relu_aux_expr`, `check_relu_aux_upper_bound` | `ReluConstraint::notifyLowerBound`, input-to-auxiliary branch | Checks the auxiliary equality in both directions and the lower-bound premise. No metadata assumption supplies the equality. |
| `check_relu_output_aux_upper_bound` | `ReluConstraint.cpp:180`, positive output branch; `src/proofs/Checker.cpp` `checkReluLemma` | Exact `f>0` forces auxiliary zero; native epsilon policy is not equated with exact positivity. |
| `check_relu_aux_lower_output_upper_bound` | `ReluConstraint.cpp:207`, positive auxiliary branch; `Checker::checkReluLemma` | Exact positive auxiliary forces output zero. Still no phase-cache or watcher transition theorem. |
| `rat_linexpr`, `rat_query` and embedding functions | Exact executable counterpart of the chosen mathematical query fragment | Project types, not representations of native doubles; `embed_*` has no C++ counterpart. |
| `normalize_linear/bound/query` | Related to linear reasoning, not identical to native preprocessing | Generic normalization into nonpositive expressions, including two rows for equality. No native algorithm correspondence claimed. |
| `weighted_sum`, `collect_terms`, `constant_contradiction`, `check_linear_leaf` | Related evidence in `src/proofs/{Contradiction,BoundExplainer,UnsatCertificateUtils,JsonWriter}.{h,cpp}` | Exact checking mathematics. Our weights index normalized query inequalities, not the native simplex basis or native row vector directly. |
| `constant_nonpositive`, `check_linear_implication`, `check_linear_bound` | `UnsatCertificateUtils::{computeBound,getExplanationRowCombination}`; `BoundExplainer::updateBoundExplanation` | Independent exact check of reconstructed evidence, not a formalization of the producer's floating-point bound computation. |
| `certificate`, `check_certificate`, `check_after_*` | Related to `src/proofs/UnsatCertificateNode.{h,cpp}` | A sound project-defined checker calculus; not `SearchTreeHandler` or `Engine::solve`. |
| `rat_assignment`, `assignment_value/valuation`, `rat_eval_*`, `check_rat_*` | Candidate data extracted by `Engine.cpp:1736` `extractSolution` | Exact witness validation; default zero for unlisted names, no faithful finite-array model yet. |
| `bounded_inequality_step`, `opposite_inequality_bound`, `rat_introduce_bounded_inequality_*` | No single native method counterpart | Local composition of a source-inspired slack transform and exact implication checking. |
| `bytes`, parser/encoder helpers, `decode_query`, `encode_query`, `same_constraints`, `decodes_like`, `bounded_decodes_like` | No native format/calculus counterpart | Project-defined exact file semantics and result binding; useful infrastructure, not solver verification. |
| `imported_*` constants and example queries/witnesses | Captured or hand-written data, as documented per theory | Particular instances; no new universal correspondence theorem. |
| Tableau state, pivot, solver state, search, backtracking, `marabou_solve` | `Tableau`, `Engine`, `SearchTreeHandler` and context structures | **No corresponding HOL definitions currently exist.** |

One wording correction to the existing map is warranted when documentation
work resumes: its “C++ setters overwrite” description must be restricted to
the appropriate query setters. `BoundManager::setLowerBound` (line 172) and
`setUpperBound` (line 187) themselves reject non-tightening updates and set
pending/conflict state. They are not unrestricted overwrites.

### Adequacy of present representations

| Object | Mathematically adequate? | Adequate correspondence basis? |
| --- | --- | --- |
| Variables | Yes. Natural numbers are a simple naming domain. | Add finite carrier/count, index-map bijections, allocation and eventual machine-range obligations. |
| Expressions/linear constraints | Yes for the target fragment, including duplicates and affine constants. | Keep as specification; add finite matrix/basis/row representation and prove its interpretation. Native assembly/merging behavior cannot be assumed. |
| Bounds | Yes as conjunctions; missing bounds can mean unrestricted. | Add a state-level lower/upper store, optional/extended bounds if needed, monotone updates, pending notifications and context restoration. |
| ReLUs | Yes as exact mathematical relations. | Add constraint identity, active/disabled and fixed-phase status, auxiliary association and invariants. Removing all duplicate atoms is semantically sound but loses object identity needed operationally. |
| Queries | Yes for a finite real-linear/ReLU specification. | Add well-formedness and a translation into the chosen solver configuration. Network metadata can remain outside the initial fragment. |
| Solver state | Not present. A query or a certificate is not such a state. | Must be introduced; existing records cannot express basis/candidate/stack invariants. |

A candidate assignment during solving is allowed to violate bounds and ReLUs.
It must not be represented by the invariant `satisfies_query candidate Q`.
Separate the problem's solution set from the algorithm's current assignment.

### Actual native solver path

For the native, non-MILP engine configuration:

1. **Create a query and enter the engine.**
   `src/engine/Marabou.cpp::prepareQuery` and `solveQuery` (line 214) obtain
   an `InputQuery` and invoke `Engine::processInputQuery` then `Engine::solve`.
   Python/C++ clients can also supply an `IQuery` directly.
2. **Preprocess and initialize.**
   `Engine.cpp:1414` `processInputQuery(inputQuery, preprocess)` calls
   `invokePreprocessor` (980). `Preprocessor::preprocess` (61) includes
   inequality conversion, constraint transformation, propagation and possible
   elimination/renaming. The disabled-preprocessing path copies the query and
   informs constraints of initial bounds. This engine currently rejects
   remaining infinite bounds.
3. **Build the linear state.**
   Native initialization creates the matrix, removes redundant equations,
   selects an initial basis, adds scalar-fixed auxiliaries, initializes
   `BoundManager` and `Tableau` and registers constraint watchers.
   `Tableau::initializeTableau` (336) initializes nonbasic values and
   factorization; `computeAssignment` (376) solves for basic values.
4. **Iterate linear feasibility and nonlinear work.**
   `Engine::solve` (196) performs propagation/valid splits, tests bounds,
   and invokes `performSimplexStep` (632) when linear feasibility is not
   reached. The latter uses `CostFunctionManager`, an entry-selection
   strategy, `Tableau::computeChangeColumn`, `pickLeavingVariable` and
   `performPivot` (696), with numerical recovery paths.
   Once linear feasibility holds it attempts nonlinear satisfaction/repair
   through `adjustAssignmentToSatisfyNonLinearConstraints` (502), using the
   configured DeepSoI or older repair route.
5. **Split and remember alternatives.**
   `SearchTreeHandler::performSplit` (133) obtains native case splits,
   disables the selected constraint, stores state, pushes context, applies
   one split with `Engine::applySplit` (1994), and retains alternatives.
   `ReluConstraint` and `PiecewiseLinearCaseSplit` provide the ReLU phases.
6. **Conflict and backtrack.**
   Bound inconsistency or a native linear failure can throw
   `InfeasibleQueryException`. The catch in `Engine::solve` optionally emits
   evidence through `explainSimplexFailure` (3420), then calls
   `SearchTreeHandler::popSplit` (267). Exhaustion sets `UNSAT`.
   `Engine::storeState/restoreState` (1847/1859), context push/pop,
   `BoundManager` and `PiecewiseLinearConstraint` share restoration duties.
   With `STORE_BOUNDS_ONLY`, tableau store/restore does not roll the basis
   back: the matrix/basis and context-managed bounds must be modeled separately.
7. **Return an outcome.**
   `Engine::solve` sets `SAT` only after its native satisfaction checks.
   `Engine::extractSolution` transfers/reconstructs values.
   `IEngine.h:49` also defines `UNKNOWN`, `TIMEOUT`, `ERROR` and
   `QUIT_REQUESTED`. A false Boolean return is not an UNSAT result.
   `Marabou::solveQuery` invokes proof certification separately for proof-mode
   UNSAT; its UNKNOWN path can invoke incremental linearization outside the
   chosen ReLU fragment.

This is based on the current source, not inferred solely from the historical
Reluplex algorithm. In `upstream/ReluplexCav2017/reluplex/Reluplex.h`,
`update` (2035) and `pivot` (2130) operate on a different tableau
representation; `fixOutOfBounds` (989) uses its GLPK integration.
`SmtCore.h::storeCurrentState/restorePreviousState` copies/restores the
older state, including basis/assignment/tableau. The existing lineage note
correctly treats these as historical counterparts, not the main target.

### Plausibility of later C++ refinement

The route is plausible, but no refinement architecture exists yet.
Keeping the current exact semantics is helpful; it is not necessary to encode
C++ containers directly into it. Add a separate operational state and explicit
relations for finite variable maps, sparse matrices versus interpreted rows,
basis invertibility, assignments, bound stores, phases and contexts.

The numeric boundary is substantive. Native `ReluConstraint::satisfied` and
bound-consistency checks use tolerances; arithmetic uses doubles and basis
factorization. A literal relation equating every native array entry with an
exact real assignment will not automatically be preserved by rounding.
Later work needs an explicit numerical model/error invariant, or a specified
exactly checked variant. A theorem for an exact HOL solver is not, by itself,
a theorem for the current C++ return value. This is an unproved obligation,
not a solver defect established by this audit.

## 6. BIGGEST FORMAL GAP

**There is no source-grounded operational state machine linking an input
query to solver results.**

The missing invariant must relate the original query to the current branch
and unexplored alternatives, while separately maintaining the linear tableau
and candidate assignment. It must justify initialization, each transition,
local conflicts, branch coverage, restoration and both terminal cases.

For eventual partial correctness, the structure should be:

```text
init relates Q to S0
each permitted solver transition preserves the required invariants
reachable Sat v states imply satisfies_query v Q
reachable Unsat states have exhausted only soundly refuted branches
```

Existing lemmas can discharge parts of these obligations. They cannot supply
the missing transition system. Defining “solver” to run Marabou and then call
`check_certificate` would give another valid Level-1 wrapper theorem; it
would not meet the stated Level-2 objective.

After operational soundness, an executable strategy requires justified
pivot/repair/split choices and return conditions. Soundness need not wait for
termination: a fuelled solver may return `Unknown` when fuel is exhausted.
Completeness and termination require separate progress/anti-cycling/fairness
arguments. Finite ReLU phase combinations alone do not prove simplex or the
whole search terminates.

## 7. NEXT VERIFIED MARABOU OPERATION

**Recommend one operation: the exact-arithmetic mathematical counterpart of
`Tableau::setNonBasicAssignment(variable, value, true)`
in `src/engine/Tableau.cpp:1484`.**

This is a small native arithmetic state transition, used by bound-compliance
updates (`Tableau.cpp:1783` onward) and ReLU repair
(`Engine.cpp:850` and `:923`). It avoids prematurely tackling pivot selection,
cost optimization, basis factorization implementation or the entire search.
It establishes the first missing candidate/tableau invariant; another
certificate-format extension would not.

The code computes `delta = value - old_nonbasic_value`, writes the nonbasic
value, computes `d = B⁻¹ A_j` in `computeChangeColumn` (1452), and updates
each basic value by `xB[i] := xB[i] - d[i] * delta`. It also recomputes basic
bound status and invalidates the cached cost function when that status changes.
The `updateBasics=false` initialization branch is a separate operation and
must not inherit this invariant-preservation claim.

A small HOL state should have a finite variable carrier, disjoint basic and
nonbasic names, exact solved rows, lower/upper stores and a candidate
assignment. Interpret the rows as

```text
xB = beta + C xN,  where beta = B⁻¹ b and C = -B⁻¹ AN.
```

For `j` nonbasic, `delta = t - v(j)`, define:

```text
v'(j) = t
v'(k) = v(k)                    for other nonbasic k
v'(i) = v(i) + C(i,j) * delta   for basic i
```

This is precisely the native minus-change-column update under the stated
row interpretation. First prove the row update with finite sums; retain the
explicit matrix/basis interpretation obligation rather than presenting an
unrelated generic row calculus as already refining the factored tableau.

The proposed main theorem, not yet present, is:

```text
wf_tableau S
∧ j ∈ nonbasic_vars S
∧ assignment_satisfies_rows S
⟹ assignment_satisfies_rows (set_nonbasic_assignment S j t)
```

Also prove:

* structural well-formedness and the represented branch solution set are
  unchanged;
* all other nonbasic values are unchanged;
* if nonbasic values initially satisfy their bounds and `t` satisfies
  `j`'s bounds, the updated nonbasic values satisfy their bounds;
* basic statuses reflect the updated assignment, and a changed status
  invalidates the cost cache in the operational model.

Do **not** claim that this update preserves all bounds or ReLUs of the
candidate assignment. Basic variables can become out of bounds; that is a
normal intermediate solver state. The operation preserves linear consistency,
and changes the candidate, not the problem's solution set.

This would be a source-grounded exact abstraction of a native operation,
with its arithmetic and metadata abstractions explicitly stated. It would
still not verify the C++ memory operations or floating-point calculation.

## 8. NEXT 3–5 MILESTONES

These are proposed implementation milestones, not changes made by this audit.
They deliberately prioritize solver states and transitions over new import
formats. Each must build completely with no admitted proofs and document
which source behavior it covers.

1. **Finite tableau state and the nonbasic update above.**
   Add `Tableau_State.thy` and `Tableau_Assignment_Update.thy`.
   Prove well-formedness, row satisfaction preservation, the nonbasic-bound
   lemma, status/cache behavior and tiny active/inactive candidate examples.
   Additional assurance: a first native-style candidate transition is
   justified over an explicit linear state.

2. **One algebraic basis exchange, without assignment movement.**
   Use the basis-exchange portion of
   `Tableau::performDegeneratePivot` (`Tableau.cpp:803`) as reference.
   With a nonzero pivot and valid basic/nonbasic partition, prove solved-row
   transformation, partition/index-map validity, equality of represented
   solution sets and preservation of the variable-indexed assignment.
   Distinguish array swapping from unchanged semantic variable values.
   Additional assurance: one native basis-change operation is justified;
   pivot selection and full ratio-step correctness remain open.

3. **One native bound application and its local conflict result.**
   Model the lower-bound branch of
   `BoundManager::{setLowerBound,tightenLowerBound}` and
   `Tableau::updateVariableToComplyWithLowerBoundUpdate`.
   Prove that a weaker proposal is a no-op, a stronger one represents
   conjunction with the new bound, pending/status effects are correct, and
   a derived bound preserves branch models when its derivation is sound.
   Prove an exact crossing-bounds conflict has no branch model.
   A decision bound must be marked as branch restriction, not misrepresented
   as an entailed fact. Additional assurance: stateful tightening/conflict
   handling, rather than just a checker for the resulting predicate.

4. **Native auxiliary-form ReLU splitting in that state.**
   Reference `ReluConstraint::{getActiveSplit,getInactiveSplit}` and the
   bound-only path of `Engine::applySplit`.
   Keep the matrix fixed; use the existing auxiliary equation and bounds,
   constraint identity and active/disabled status.
   Prove both child solution sets cover the parent, matching the actual
   auxiliary-bound phases, including the zero boundary.
   Additional assurance: the native form of one search expansion, beyond
   the already-proved canonical query split.

5. **One search-frame push/backtrack/pop with coverage invariant.**
   Reference `SearchTreeHandler::{performSplit,popSplit}`,
   context hooks and bounds/phase restoration.
   Start with one binary ReLU frame and the local conflict rule from
   milestone 3; preserve the current basis as the native bound-only mode does.
   Prove that soundly refuting both children permits closing the frame,
   and restoration does not retain a child-only assumption.
   Additional assurance: the first operational branch-exhaustion theorem.
   General stack induction can follow as a separate small extension.

These five do not honestly finish `Engine::solve`. Further milestones must
cover full moving pivots/ratio guards, the cost-function/no-entering-candidate
infeasibility argument in `Engine::performSimplexStep`, initialization into
the invariant, ReLU repair/phase fixing and the configured search controller.
Then prove finite-run soundness and implement a fuelled strategy with
`Unknown` distinct from `Unsat`. Termination/completeness and Level-3
refinement remain separate later results.

The existing checker should stay as a secondary artifact and regression aid.
The outstanding provenance refresh is housekeeping to close the interrupted
checkpoint, not a new research milestone. Do not change the numeric semantics
or silently import all optimizations to obtain a stronger-sounding theorem.

## 9. CLAIM WE CAN CURRENTLY MAKE

“We have formalized a real-linear/ReLU query fragment in Isabelle/HOL and
proved soundness of exact rational certificate and assignment checking,
together with selected source-grounded auxiliary transformations, obtaining
checked SAT/UNSAT theorems for specific captured Marabou examples without
verifying Marabou's solving procedure.”

## 10. CLAIM WE WANT EVENTUALLY TO MAKE

“We aim to prove SAT and UNSAT soundness of an explicit, source-corresponding
exact-arithmetic formalization of a specified Marabou solving configuration
in Isabelle/HOL, with termination/completeness and refinement to the C++
implementation established separately where proved.”
