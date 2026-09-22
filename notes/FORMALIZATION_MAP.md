# Formalization map

Revision scope and source paths are as in [MARABOU_SOURCE_MAP.md](MARABOU_SOURCE_MAP.md).
Paths in the table are relative to `upstream/Marabou/`. These are documented
correspondences, **not refinement theorems about the C++ program**.

| HOL concept | Source counterpart | Chosen abstraction / mismatch |
| --- | --- | --- |
| `var = nat` | `Equation::Addend::_variable`, `InputQuery::getNumberOfVariables/getNewVariable`; `src/engine/Equation.h`, `InputQuery.{h,cpp}` | Unbounded natural-number names. C++ uses finite-width `unsigned` and a declared variable count. An importer must check indices. |
| `valuation = var ⇒ real` | `Tableau::_basicAssignment/_nonBasicAssignment`, `getValue`; `InputQuery::_solution`, `getSolutionValue`; `src/engine/Tableau.{h,cpp}`, `InputQuery.{h,cpp}` | Total exact real function. C++ holds finite `double` arrays/maps and may lack an assignment. |
| `Linexpr c ts` | `src/common/LinearExpression.{h,cpp}` (`_constant`, `_addends`, `evaluate`); `Equation::Addend` | Finite list of real coefficients with duplicates allowed. `LinearExpression` has a map; `Equation` has a list. No C++ container invariant is assumed. |
| `eval_linexpr` | `LinearExpression::evaluate` | Exact sum of **all** terms. C++ skips coefficients considered zero by `FloatUtils`, uses floating-point addition/multiplication, and can return NaN for missing assignments. No equality with that implementation is claimed. |
| `LinearEq`, `LinearLe`, `LinearGe` | `src/engine/Equation.{h,cpp}`, `Equation::EQ/LE/GE` | Direct exact comparison with the right-hand scalar. Marabou's Equation has no separate left constant; `c + sum ts op b` corresponds algebraically to `sum ts op (b-c)`. That arithmetic translation is not an implemented importer. |
| `Lower x l`, `Upper x u` | `src/engine/Tightening.h`, `Tightening::LB/UB`; `InputQuery`, `Query`, `BoundManager` | Declarative propositions in a conjunction. C++ setters overwrite, tightening methods select stronger bounds, and propagation mutates state. These operations are not modeled. |
| No bound atom | `InputQuery::getLowerBound/getUpperBound`, `Preprocessor::setMissingBoundsToInfinity` | Unrestricted direction, instead of a floating-point infinity. NaN and infinity are never HOL real values. |
| `ReLU x y` / `satisfies_relu` | `src/engine/ReluConstraint.{h,cpp}` (`_b`, `_f`, `satisfied`) | `x` is backward/input `b`; `y` is forward/output `f`. Exact `v y = max 0 (v x)` is the intended relation, while `satisfied()` uses tolerances. |
| `query` | `src/engine/IQuery.h`, `InputQuery.{h,cpp}`, `Query.{h,cpp}` | Three finite conjunctions: linear atoms, bounds, ReLUs. Omits variable count, input/output markers, ownership, contexts, non-ReLU constraints, network metadata and solver state. |
| `satisfies_query`, `satisfiable`, `unsatisfiable`, `models` | Intended query meaning; `Engine::solve`/`IEngine::ExitCode` report operational outcomes | These define a mathematical property. No theorem equates an `ExitCode` or C++ Boolean with these predicates. |
| `active_split Q x y` | `ReluConstraint::getActiveSplit` and `Engine::applySplit` | Adds `0 ≤ x` and `y - x = 0`; removes the selected ReLU. C++ uses `b - f = 0` or an auxiliary bound and manages activation state. Both equation orientations express the same exact equality, but no C++ state-preservation theorem exists. |
| `inactive_split Q x y` | `ReluConstraint::getInactiveSplit` | Adds `x ≤ 0` and explicit `y = 0`; removes the selected ReLU. C++ adds upper bounds on `b` and `f`, relying on an existing nonnegative `f` bound. |
| `unsatisfiable_relu_split` | Branch coverage intended by `getCaseSplits`, `SearchTreeHandler::performSplit/popSplit` | A logical inference with explicit membership and two UNSAT premises. Does not verify branch selection, bookkeeping, restoration, or exhaustiveness of the running search. |
| `query_inconsistent_bounds` | `BoundManager::consistentBounds`, `Checker::checkContradiction` for an empty contradiction vector | Exact strict inconsistency `u < l`. Does not trust tolerance tests or the provenance of any propagated bound. |
| `linear_le_add`, `linear_le_scale_nonnegative` | Mathematical ingredients of `BoundExplainer` / `UNSATCertificateUtils` | Sound real arithmetic rules. The rational leaf checker now proves analogous weighted-sum reasoning, without a reconstruction proof for C++ evidence. |
| `rat_linexpr`, `rat_linear_constraint`, `rat_bound`, `rat_query` | Rational mathematical counterparts of the same expression/query concepts | Separate executable data types. The C++ types still use doubles; no conversion from them has been verified. |
| `embed_linexpr`, `embed_linear`, `embed_bound`, `embed_query` | No asserted C++ implementation counterpart | Exact `of_rat` interpretation into the original real syntax. ReLU atoms are preserved. Valuations remain real-valued. |
| `normalize_linear`, `normalize_bound`, `normalize_query` | A mathematical alternative to the transformations in `Preprocessor.cpp` | Proved normalization to expressions constrained to be nonpositive, including two rows per equality. This does not verify Marabou's preprocessing. |
| `weighted_sum`, `collect_terms`, `check_linear_leaf` | Related evidence in `src/proofs/Contradiction`, `BoundExplainer`, `UnsatCertificateUtils`, `AletheProofWriter` | Our weights refer to normalized query inequalities, not tableau rows. Exact length/sign/cancellation checks imply `unsatisfiable (embed_query Q)`. The separate JSON adapter reconstructs candidate weights from a restricted native format. |
| `rat_active_split`, `rat_inactive_split` | `ReluConstraint::getActiveSplit/getInactiveSplit` | Their embeddings are proved equal to the existing mathematical real splits. Native auxiliary bounds must be reconstructed from these canonical phase constraints and root rows. |
| `certificate`, `check_certificate` | `src/proofs/UnsatCertificateNode.{h,cpp}` | Finite tree with linear leaves, binary ReLU splits, and unary checked linear-bound/ReLU propagation. Splits check membership and both children; propagation checks its premises and continuation. Omits C++ visited/SAT/delegation flags. No unchecked success path exists. |
| `check_relu_upper_bound`, `rat_add_bound`, `Relu_Upper` | `src/engine/ReluConstraint.cpp::notifyUpperBound`, input-variable branch; `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound`; `src/proofs/PlcLemma.{h,cpp}` | Requires a present ReLU and explicit input upper bound `u`, then adds an output upper bound `b ≥ max(0,u)`. Exact rational guards replace tolerance-based acceptance. Existing constraints are retained. Imported premises may now come from a checked linear implication. |
| `check_linear_implication`, `check_linear_bound`, `Linear_Bound` | `src/proofs/UnsatCertificateUtils.cpp::computeBound/getExplanationRowCombination`; `BoundExplainer::updateBoundExplanation` | Checks that a target minus a nonnegative normalized-row combination is a nonpositive constant. Proves both upper and lower bounds over real models. The adapter reconstructs upper and lower premises from `e_x + wᵀA`; it does not verify the native floating-point computation. |
| `rat_linear_bound_preserves_models` | Semantic justification for adding a linearly explained bound | Proves equality of real model sets before/after the checked addition. The adapter keeps this HOL premise separate from native ground state; only PLC conclusions update native ground bounds. |
| `rat_relu_upper_preserves_models` | Intended semantic justification for that propagation | Proves equality of real model sets before/after the checked addition. Allows redundant additions; does not verify C++ state updates, phase fixing, or the explanation manager. |
| `relu_aux_expr`, `check_relu_aux_upper_bound`, `Relu_Aux_Upper` | `ReluConstraint::notifyLowerBound`, input-to-auxiliary branch; `transformToUseAuxVariables` supplies the equation in native preprocessing | Checks ReLU membership, an input lower bound, two exact linear witnesses for `f-b-aux=0`, and `max(0,-l)≤u`. Metadata alone never supplies the equation. This does not verify auxiliary introduction. |
| `rat_relu_aux_upper_preserves_models` | Semantic justification for that auxiliary propagation | Adding an accepted upper bound on the proved auxiliary preserves the entire real model set. |
| `check_certificate_sound` | Logical composition intended by the search proof tree | Proved by induction from exact leaf soundness, ReLU coverage, and checked propagation; no premise concerning solver correctness or its UNSAT flag. |
| `Imported_Marabou_*.imported_query` | `src/proofs/JsonWriter.cpp::writeProofToJson` top-level tableau, bounds, constraints | The untrusted adapter decodes exact serialized decimal rationals and matches a separately supplied processed-query manifest. No theorem relates the decoded query to source bytes, binary-double values, or an original preprocessed input. |
| `Imported_Marabou_*.imported_query_unsatisfiable` | JSON-writer test fixtures produced from actual C++ `UnsatCertificateNode` / `Contradiction` objects | Kernel-checked real UNSAT for the explicit query data. Nine fixtures use hand assembly or native component calls on supplied rows. The four `Imported_Marabou_Solver_*` theories replay actual `Engine::solve` certificates, including output and auxiliary propagation. |
| Four `solver_*_query.json` snapshots and their capture harness | `Engine::getQuery/storeState/getGroundBound`, before `Engine::solve` | Independently captures initialized equations/bounds and compares them with the native tableau at runtime. This observation is unverified C++ extraction, not a refinement theorem or a preprocessing proof. |
| `Solver_ReLU_Examples.captured_query_requires_nonlinear_evidence` | A mathematical check on the captured ReLU query | Its linear relaxation has an explicit real model. No rational linear-leaf certificate alone can certify the root; the replayed nonlinear rule is necessary. |
| `ReLU_Aux_Bound_Examples.active_aux_capture_has_no_linear_certificate` | A mathematical check on the active auxiliary capture | Its linear relaxation has an explicit real model; the sole native nonlinear lemma is essential to the replayed contradiction. |

## Deliberate choices

The model permits repeated linear terms, bounds, and ReLU atoms because
conjunction and finite sums give them unambiguous meanings. Splitting filters
out all occurrences of the selected ReLU; each child explicitly implies that
ReLU, so deletion cannot introduce extra parent models. The exact theorem is
`models_relu_split`, with premise `ReLU x y ∈ set (relu_atoms Q)`.

The child-to-parent inclusion holds even without membership
(`satisfies_active_split_iff`, `satisfies_inactive_split_iff`). Membership is
needed for parent-to-children coverage: an unconstrained pair need not satisfy
either ReLU phase.

The original semantic model still permits arbitrary real coefficients. The
executable layer now has separate rational data and a proved normalization into
this semantics. `check_linear_leaf_sound` excludes every real valuation of an
accepted embedded query. We have not silently treated floating-point values as
decimal rationals or replaced HOL real equality with a tolerance test. The
[leaf contract](RATIONAL_LINEAR_CHECKER.md) specifies the representation and
certificate order; the [import contract](CERTIFICATE_IMPORT.md) explicitly
chooses serialized decimal rationals for its processed-query semantics.

## Unresolved semantic questions

1. What is the exact input contract: original decimal/rational network data,
   exact values of finite binary doubles, or a particular serialized query?
   These can denote different real queries.
2. How will preprocessing steps be justified? `Preprocessor::preprocess`
   normalizes inequalities, introduces auxiliaries, tightens bounds, can merge
   weighted layers, and can eliminate variables. The existing proof tree is
   initialized later. A processed-query theorem alone is insufficient.
3. Which auxiliary-variable transformations will be replayed as checked
   definitional extensions? `ReluConstraint::transformToUseAuxVariables` and
   `Engine::addAuxiliaryVariables` are the first relevant cases.
4. How will the running solver emit the supported evidence? The restricted JSON
   writer format is now imported and replayed. An external public-API harness
   has captured actual native linear and ReLU-propagation executions; the normal
   CLI still has no found writer call site. Solver-produced binary splitting
   remains untested. The configurable Alethe format is not imported.
5. How should support expand beyond the two ReLU upper rules and their exact
   tableau explanations to other propagation rules, missing bounds, and larger trees?
   The current importer explicitly rejects unsupported/missing evidence and
   failed exact reconstruction. It never inherits a C++ success flag as a
   premise; serialized decimal values may still differ from original doubles.
6. What exact witness reconstruction will suffice for SAT? An approximate
   floating-point assignment is not by itself an exact solution of equalities.

These questions do not affect the abstract splitting rule or the leaf/tree
soundness theorems. They affect whether the checked rational query and evidence
faithfully represent a concrete Marabou run and its original input.
