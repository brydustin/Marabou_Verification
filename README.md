# Marabou verification in Isabelle/HOL

The development proves exact rational linear-leaf and recursive ReLU proof-tree
checkers sound over real query semantics. A strict adapter imports a subset of
Marabou's JSON certificate format and emits theories for Isabelle to replay.
The checker also verifies linear implications and four ReLU propagation rules:
input upper to output upper, input lower to auxiliary upper, strictly
positive output lower to auxiliary upper zero, and its dual, strictly positive
auxiliary lower to output upper zero. All support tableau explanations;
the three auxiliary rules also check the defining equation.
Eighteen saved certificates serialized by the actual C++ writer have been checked in HOL.
Nine come from real proof-enabled `Engine::solve` executions: one linear query,
one output-propagation query, two auxiliary-propagation variants, and a binary
ReLU split with both children replayed, plus a query starting with a plain ReLU
whose auxiliary is introduced by the native transformation method, and a
two-ReLU query with both native introductions captured and replayed, a
chained two-ReLU query exercising the positive-output rule, and a query whose
native proof uses the positive-auxiliary rule.
The other nine are hand-assembled/component fixtures.
All nine accepted native captures include pre-initialization source queries and
proposed scalar-fixed auxiliary introductions. A second strict importer emits
proofs that the checked introductions produce the independent processed
queries and that the captured source queries are UNSAT over real valuations.
The binary split includes five introductions and both proof children.
A checked fresh ReLU auxiliary introduction is proved sound, including
its optional upper bound. The new capture records the query before and after
the actual native introduction. Importing that step, three tableau steps, and
the native proof establishes UNSAT of the captured four-variable starting query.
Finite checked ReLU introductions are now proved sound too. A two-ReLU capture
replays both introductions, five tableau steps and two native propagation
lemmas to prove its six-variable starting query UNSAT. Removing either ReLU
makes that query satisfiable, also proved in HOL.
The previously rejected chained proof now replays in full. A fresh native run
reproduced its six data artifacts byte-for-byte and supplies build/run provenance.
An exact rational SAT-assignment checker is proved sound and complete for
rational assignments. A tenth native run returns SAT; its reported doubles,
reconstructed exactly, are proved to be a real model of the processed query,
its source and the query before both native ReLU introductions.
A narrow exact text format now has its meaning defined by a HOL decoder with a
proved round trip. The starting queries of all ten native scenarios are saved
as such files, and their UNSAT/SAT results are restated about the decoded bytes.
One command now takes a supported `.mqx` file, runs the unmodified native
engine on the query it reads, and ends with an Isabelle theorem about the
file's decoded bytes, or a stated rejection; see the quick start below.
A checked inequality-to-equality transformation now covers both directions
with fresh signed slacks. Finite sequences preserve real SAT/UNSAT and compose
with the existing introduction and proof checkers. `le`/`ge` files now work in
the `.mqx` workflow. An untrusted local translation adds each slack and a
finite opposite bound, and HOL checks both. The theorems still concern the
original file's bytes. ReLU phases that the initial bounds fix before search
are now justified exactly. Native Marabou adds such a phase's bounds without
any explanation, so these proofs could not be replayed before. Two new
certificate steps prove the phase from the query and the ReLU's valid
inequalities. A `--preprocess` mode now runs Marabou's own preprocessing,
and HOL checks its result independently:
* the native slack and ReLU auxiliary introductions are checked;
* the tightened bounds are re-derived exactly as checked facts;
* a checked projection, under the recorded variable renaming, reaches the
  captured preprocessed query;
* when preprocessing itself reports infeasibility, which Marabou gives no
  proof for, the projection reaches a pair of crossing bounds instead.
**The theorems concern explicit HOL queries and, for `.mqx` files, their decoded bytes. Marabou's implementation,
including its preprocessing procedure (only results are checked), C++/JSON
decoding, and correspondence to network files are not verified.**

## Quick start: prove a result about a query file

```sh
python3 Isabelle/tools/verify_query_file.py Isabelle/examples/relu_chain_unsat.mqx /tmp/mqx-chain
```

This pre-checks the file, builds the native harness, solves the query it
reads, imports the evidence and builds the generated Isabelle session. It
prints the checked theorem, e.g.
`decode_query query_file = Some Q ==> unsatisfiable (embed_query Q)` with
`query_file` the exact bytes of the file, or the rejection reason. See
[the workflow note](notes/QUERY_FILE_WORKFLOW.md) for supported inputs,
rejection messages and the trust boundary. Add `--preprocess` to run
Marabou's own preprocessing; that mode also accepts missing bounds and
converts `le`/`ge` natively ([details](notes/NATIVE_PREPROCESSING.md)).

## Build

Tested with `Isabelle2025-2`. From this project directory:

```sh
isabelle version
isabelle build -D Isabelle
```

The session is `Marabou_Verification`, based on `HOL`, with
`quick_and_dirty = false`. No additional packages or upstream C++ builds are
needed. See [the build record](notes/BUILD_RESULT.md) for the final result and
[the environment audit](notes/ENVIRONMENT_AUDIT.md) for installation details.

The session also checks that the checkers compile to Standard ML. To extract
`Marabou_Linear_Leaf.ML`, `Marabou_Proof_Checker.ML` and
`Marabou_Assignment_Checker.ML`, plus the new
`Marabou_Inequality_Preprocessor.ML` under `Isabelle/generated/`, run:

```sh
isabelle build -e -D Isabelle
```

The generated directory is ignored by Git and can be regenerated from the
theories. See [the leaf checker interface](notes/RATIONAL_LINEAR_CHECKER.md) and
[certificate import and tree checking](notes/CERTIFICATE_IMPORT.md) for the
interfaces, execution instructions, and assurance boundary.

## Files and definitions

| File | Contents |
| --- | --- |
| [Isabelle/ROOT](Isabelle/ROOT) | HOL session and theory order. |
| [Marabou_Syntax.thy](Isabelle/Marabou_Syntax.thy) | `var = nat`, `valuation = var ⇒ real`; finite affine expressions, linear atoms, bounds, ReLU atoms, and the `query` record. |
| [Marabou_Semantics.thy](Isabelle/Marabou_Semantics.thy) | `eval_terms`, `eval_linexpr`, constant/variable expressions, expression addition and scaling. |
| [Linear_Constraints.thy](Isabelle/Linear_Constraints.thy) | Exact semantics of equality, both inequality directions, and lower/upper bounds; elementary inference rules. |
| [ReLU_Constraints.thy](Isabelle/ReLU_Constraints.thy) | `relu x = max 0 x`, ReLU satisfaction and phase decomposition. |
| [Query_Semantics.thy](Isabelle/Query_Semantics.thy) | `satisfies_query`, `models`, `satisfiable`, `unsatisfiable`, and a contradictory-bounds rule. |
| [Tableau_Auxiliary.thy](Isabelle/Tableau_Auxiliary.thy) | Query variable support, one scalar-fixed auxiliary step, model extension/projection, and SAT/UNSAT equivalence under freshness. |
| [Tableau_State.thy](Isabelle/Tableau_State.thy), [Tableau_Assignment_Update.thy](Isabelle/Tableau_Assignment_Update.thy) | Exact solved-row tableau state; a nonbasic assignment update preserves row consistency, state well-formedness, and the selected nonbasic's bounds when its target is in bounds. This abstracts `Tableau::setNonBasicAssignment(..., true)`; it does not verify C++ factorization, floating point, status updates, or cache invalidation. |
| [Tableau_Pivot.thy](Isabelle/Tableau_Pivot.thy) | Exact basis exchange (`performPivot`/`performDegeneratePivot`): the same real solutions, candidate valuation and row consistency; the reverse pivot; uniqueness of the solved form of a basis; pivot-then-set for the ReLU repair path. |
| [Tableau_Simplex_Step.thy](Isabelle/Tableau_Simplex_Step.thy) | Zero-tolerance statuses, core costs, reduced costs, entry eligibility and the default Harris ratio test; admissible steps keep all nonbasics in bounds and every basic's status; no eligible entering variable with an out-of-bounds basic proves the rows and bounds unsatisfiable. |
| [Tableau_Index_Layout.thy](Isabelle/Tableau_Index_Layout.thy) | Native index maps and value arrays; the array updates of degenerate pivots, real pivots and bound flips refine the exact state transitions. |
| [Tableau_Simplex_Run.thy](Isabelle/Tableau_Simplex_Run.thy), [Tableau_Pivot_Examples.thy](Isabelle/Tableau_Pivot_Examples.thy) | A fuelled exact simplex loop whose `Feasible` and `Infeasible` results are proved sound (`Out_Of_Fuel` claims nothing); a four-step feasible run, an infeasibility theorem from a run, native array steps and rejections. |
| [Tableau_Initialization.thy](Isabelle/Tableau_Initialization.thy) | The starting tableau of a query (`addAuxiliaryVariables`, nonbasics at lower bounds); its bounded solutions are exactly the query's linear-and-bound solutions. `Simplex_Unsat` proves the query unsatisfiable, ReLUs included; `Simplex_Feasible` satisfies every equation and bound, and is a model once the ReLUs check. |
| [Tableau_Initial_Basis.thy](Isabelle/Tableau_Initial_Basis.thy), [Imported_Marabou_Initial_Bases.thy](Isabelle/Imported_Marabou_Initial_Bases.thy) | An exact copy of `selectInitialVariablesForBasis`, reached by checked pivots; `solve_query`. The generated theory proves that it reproduces the native basic and nonbasic orders of all 20 captured runs. |
| [Tableau_Initialization_Examples.thy](Isabelle/Tableau_Initialization_Examples.thy) | `examples/linear_unsat.mqx` refuted by the HOL simplex alone, a SAT query, a ReLU query refuted by its linear part, a relaxation that is not a model, and refused inputs. |
| [Rational_Tableau_Auxiliary.thy](Isabelle/Rational_Tableau_Auxiliary.thy) | Executable index/equality/freshness checks, a proved embedding into the real transformation, and `check_after_fixed_aux_sound`. |
| [Tableau_Auxiliary_Examples.thy](Isabelle/Tableau_Auxiliary_Examples.thy) | Exact connection to the earlier linear solver snapshot, a source-query UNSAT theorem, affine examples, and rejection of unsound variable reuse. |
| [Tableau_Auxiliary_Sequence.thy](Isabelle/Tableau_Auxiliary_Sequence.thy) | Finite checked introductions, concatenation/failure laws, SAT/UNSAT preservation, and `check_after_fixed_aux_sequence_sound`. |
| [Tableau_Auxiliary_Sequence_Examples.thy](Isabelle/Tableau_Auxiliary_Sequence_Examples.thy) | Five steps producing the binary-split snapshot exactly, a proved term-order equivalence, source-query UNSAT, and sequence rejection examples. |
| [ReLU_Auxiliary.thy](Isabelle/ReLU_Auxiliary.thy) | One fresh ReLU auxiliary, its equality and nonnegative/optional upper bounds, model extension/projection, and SAT/UNSAT equivalence. |
| [Rational_ReLU_Auxiliary.thy](Isabelle/Rational_ReLU_Auxiliary.thy) | Checked ReLU membership, freshness and finite-bound premise; exact embedding and composition with tableau steps and certificate checking. |
| [ReLU_Auxiliary_Examples.thy](Isabelle/ReLU_Auxiliary_Examples.thy) | Exact connection to the existing auxiliary-propagation capture, an earlier source UNSAT theorem, SAT witnesses, boundary cases, and guard counterexamples. |
| [ReLU_Splitting.thy](Isabelle/ReLU_Splitting.thy) | `active_split`, `inactive_split`, model coverage and the UNSAT inference rule. |
| [Marabou_Examples.thy](Isabelle/Marabou_Examples.thy) | Exact SAT witness, an UNSAT proof using two linear children, and the overlapping zero-input case. |
| [Rational_Linear_Constraints.thy](Isabelle/Rational_Linear_Constraints.thy) | Rational query data, exact embedding into real queries, and proved normalization of equalities, inequalities and bounds. |
| [Rational_Linear_Certificates.thy](Isabelle/Rational_Linear_Certificates.thy) | Exact coefficient collection, checked weighted sums, `check_linear_leaf`, its soundness theorem, and SML code generation. |
| [Rational_Linear_Examples.thy](Isabelle/Rational_Linear_Examples.thy) | Proved acceptance/rejection computations and a ReLU example closed with checked linear leaves. |
| [Rational_Linear_Implication.thy](Isabelle/Rational_Linear_Implication.thy) | `check_linear_implication`, `check_linear_bound`, real-semantic soundness, and preservation of models when adding a checked bound. |
| [Rational_Linear_Implication_Examples.thy](Isabelle/Rational_Linear_Implication_Examples.thy) | Upper/lower bounds, weaker conclusions, malformed evidence, SAT witnesses, and a linear-premise/ReLU/UNSAT chain. |
| [ReLU_Bound_Propagation.thy](Isabelle/ReLU_Bound_Propagation.thy) | Exact input-to-output upper-bound propagation, its checked premises, and a real-model-preservation theorem. |
| [ReLU_Aux_Bound_Propagation.thy](Isabelle/ReLU_Aux_Bound_Propagation.thy) | Input-lower to auxiliary-upper propagation, with two exact linear witnesses for the auxiliary equation, soundness, and model preservation. |
| [ReLU_Aux_Bound_Examples.thy](Isabelle/ReLU_Aux_Bound_Examples.thy) | Negative/zero/positive cases, premise/equation rejection checks, real counterexamples, and the active capture's satisfiable linear relaxation. |
| [ReLU_Output_Bound_Propagation.thy](Isabelle/ReLU_Output_Bound_Propagation.thy) | Strictly positive output lower bound implies auxiliary upper bound zero, with exact premise/equation checks and real-model preservation. |
| [ReLU_Output_Bound_Examples.thy](Isabelle/ReLU_Output_Bound_Examples.thy) | Positive and zero-boundary models, guarded acceptance/rejection, exact tiny-positive premises, and a satisfiable relaxation of the native chain. |
| [ReLU_Aux_Lower_Bound_Propagation.thy](Isabelle/ReLU_Aux_Lower_Bound_Propagation.thy) | The dual rule: a strictly positive auxiliary lower bound implies output upper bound zero, with exact premise/equation checks and real-model preservation. |
| [ReLU_Aux_Lower_Bound_Examples.thy](Isabelle/ReLU_Aux_Lower_Bound_Examples.thy) | Acceptance, zero-boundary countermodel `x=y=1,a=0`, guard rejections, and satisfiable relaxations of the new native capture. |
| [Rational_Proof_Trees.thy](Isabelle/Rational_Proof_Trees.thy) | Rational splits, their real embedding theorems, recursive certificates, `check_certificate_sound`, and SML export. |
| [Rational_Proof_Tree_Examples.thy](Isabelle/Rational_Proof_Tree_Examples.thy) | Nested-tree acceptance, absent/repeated ReLU and bad-child rejection, and the earlier UNSAT example checked recursively. |
| [ReLU_Bound_Examples.thy](Isabelle/ReLU_Bound_Examples.thy) | Negative/zero/positive propagation, ordered chains, real witnesses, and rejection of forged premises or conclusions. |
| [Imported_Marabou_Linear.thy](Isabelle/Imported_Marabou_Linear.thy), [Imported_Marabou_Relu.thy](Isabelle/Imported_Marabou_Relu.thy), [Imported_Marabou_Nested.thy](Isabelle/Imported_Marabou_Nested.thy) | Generated data, kernel-checked acceptance, and real-semantic UNSAT theorems for three writer fixtures. |
| [Imported_Marabou_Propagation.thy](Isabelle/Imported_Marabou_Propagation.thy), [positive](Isabelle/Imported_Marabou_Propagation_Positive.thy), [chain](Isabelle/Imported_Marabou_Propagation_Chain.thy), [tree](Isabelle/Imported_Marabou_Propagation_Tree.thy) | Four imported `PLCLemma` examples, each replayed through the extended soundness theorem. |
| [Imported_Marabou_Explained_Negative.thy](Isabelle/Imported_Marabou_Explained_Negative.thy), [positive](Isabelle/Imported_Marabou_Explained_Positive.thy) | Nonempty tableau explanations become checked linear-bound premises, followed by ReLU propagation and exact contradiction. |
| [Imported_Marabou_Solver_Linear.thy](Isabelle/Imported_Marabou_Solver_Linear.thy) | Kernel-checked UNSAT for an actual solver execution's captured processed query. |
| [Imported_Marabou_Solver_Relu.thy](Isabelle/Imported_Marabou_Solver_Relu.thy) | Actual solver-produced linear premise, ReLU propagation, and terminal contradiction, replayed unchanged. |
| [Solver_ReLU_Examples.thy](Isabelle/Solver_ReLU_Examples.thy) | A real model of that capture's linear relaxation and proof that no linear leaf alone can certify its root query. |
| [Imported_Marabou_Solver_Relu_Aux.thy](Isabelle/Imported_Marabou_Solver_Relu_Aux.thy), [active](Isabelle/Imported_Marabou_Solver_Relu_Aux_Active.thy) | Actual solver-produced auxiliary lemmas, checked with their lower explanations and auxiliary equations, then composed with terminal contradictions. |
| [Imported_Marabou_Solver_Relu_Split.thy](Isabelle/Imported_Marabou_Solver_Relu_Split.thy), [Solver_ReLU_Split_Examples.thy](Isabelle/Solver_ReLU_Split_Examples.thy) | A solver-produced binary split, exact checks and UNSAT theorems for both children, and a proved model of the root's linear relaxation. |
| [capture_marabou_solver.py](Isabelle/tools/capture_marabou_solver.py), [capture.cpp](Isabelle/tools/solver_capture/capture.cpp) | Reproducible native-engine build, pre-solve snapshot, solver-owned certificate export, provenance, and standalone replay generation. |
| [import_marabou_json.py](Isabelle/tools/import_marabou_json.py) | Untrusted strict JSON adapter; exact decimal decoding, independent query matching, and reconstruction of candidate weights. |
| [import_marabou_source.py](Isabelle/tools/import_marabou_source.py) | Imports the captured source and introduction list alongside the processed query and proof; emits reordering, transformation equality, and source UNSAT obligations. |
| [Imported_Marabou_Source_Relu_Split.thy](Isabelle/Imported_Marabou_Source_Relu_Split.thy) and four companion `Imported_Marabou_Source_*` theories | Generated source/processed equisatisfiability and source UNSAT proofs for the five original solver scenarios. |
| [import_marabou_relu_intro.py](Isabelle/tools/import_marabou_relu_intro.py) | Strict six-artifact import: before-query, native ReLU introduction record, independent after-source, tableau steps, processed query, and native proof. |
| [Imported_Marabou_Native_Relu_Intro.thy](Isabelle/Imported_Marabou_Native_Relu_Intro.thy) | Exact native-introduction result, before/processed equisatisfiability, and UNSAT of the captured query before its ReLU auxiliary existed. |
| [ReLU_Auxiliary_Sequence.thy](Isabelle/ReLU_Auxiliary_Sequence.thy) | Finite checked ReLU steps, composition/failure laws, real SAT/UNSAT preservation and `check_after_relu_aux_sequence_sound`. |
| [import_marabou_relu_sequence.py](Isabelle/tools/import_marabou_relu_sequence.py) | Six-artifact import with an ordered native ReLU introduction list, full result matching and generated sequence proof obligations. |
| [Imported_Marabou_Native_Relu_Sequence.thy](Isabelle/Imported_Marabou_Native_Relu_Sequence.thy), [ReLU_Auxiliary_Sequence_Examples.thy](Isabelle/ReLU_Auxiliary_Sequence_Examples.thy) | Native two-ReLU replay, SAT sequence witnesses, late-failure rejection and proof that both ReLUs are necessary. |
| [Imported_Marabou_Native_Relu_Chain.thy](Isabelle/Imported_Marabou_Native_Relu_Chain.thy) | Two native ReLU introductions, five tableau steps, all four native propagation lemmas and a linear leaf prove the captured six-variable starting query UNSAT. |
| [Rational_Assignment.thy](Isabelle/Rational_Assignment.thy) | `check_rat_assignment`: exact evaluation of every linear atom, bound and ReLU for a finite rational assignment; soundness, completeness for rational assignments, lifting through checked introductions, and SML export. |
| [Rational_Assignment_Examples.thy](Isabelle/Rational_Assignment_Examples.thy) | Accepted models, rejection of duplicates, missing values, perturbations, bound and ReLU violations, witnesses for two earlier SAT relaxations, and a ReLU-only violation of the native SAT query. |
| [Inequality_Auxiliary.thy](Isabelle/Inequality_Auxiliary.thy) | LE/GE conversion with the native +1 slack coefficient and the appropriate signed bound; model extension/projection and SAT/UNSAT preservation. |
| [Rational_Inequality_Auxiliary.thy](Isabelle/Rational_Inequality_Auxiliary.thy) | Exact index/type/freshness guards, constructed result, embedding and certificate soundness. |
| [Inequality_Auxiliary_Sequence.thy](Isabelle/Inequality_Auxiliary_Sequence.thy) | Finite composition, checked SAT witnesses and composition with ReLU/tableau introductions and proof replay; SML export. |
| [Inequality_Auxiliary_Examples.thy](Isabelle/Inequality_Auxiliary_Examples.thy) | Both signs, affine and duplicate terms, zero slack, collision/sign counterexamples, checked UNSAT and SAT examples, and a decoded inequality text. |
| [import_marabou_assignment.py](Isabelle/tools/import_marabou_assignment.py) | Strict native assignment import: exact binary values of the reported doubles first, a bounded small-denominator repair only if needed, then generated exact-model obligations. |
| [Imported_Marabou_Native_Relu_Sat.thy](Isabelle/Imported_Marabou_Native_Relu_Sat.thy) | The native SAT run's exact assignment is a model of the processed, source and before-ReLU queries; SAT is also derived through the checked introductions. |
| [Exact_Query_Format.thy](Isabelle/Exact_Query_Format.thy) | The `marabou-exact-query-v1` text format: `decode_query` on byte lists (its meaning), the canonical `encode_query`, the round-trip theorem `decode_encode_query`, and a build-time file/byte-list check. |
| [Exact_Query_Format_Examples.thy](Isabelle/Exact_Query_Format_Examples.thy) | Decoding of every statement and number form, a model read from bytes, and rejection of many malformed inputs. |
| [exact_query_text.py](Isabelle/tools/exact_query_text.py), [Imported_Marabou_Exact_Texts.thy](Isabelle/Imported_Marabou_Exact_Texts.thy) | Untrusted exporter of captured starting queries to `.mqx` files; generated proofs that each file's checked bytes decode to the replayed starting query, with its UNSAT or SAT result restated. |
| [verify_query_file.py](Isabelle/tools/verify_query_file.py), [import_marabou_query_file.py](Isabelle/tools/import_marabou_query_file.py) | One-command query-file workflow, and the adapter binding a file to its native capture and generating the theorem theory. |
| [Isabelle/examples](Isabelle/examples) and `Imported_Marabou_Example_*` theories | Solvable example files with main-session theorems about their bytes, and files illustrating rejection reasons; see [the workflow note](notes/QUERY_FILE_WORKFLOW.md#examples-and-durable-evidence). |
| [Preprocessing_Projection.thy](Isabelle/Preprocessing_Projection.thy), [Preprocessing_Projection_Examples.thy](Isabelle/Preprocessing_Projection_Examples.thy) | Checked facts (implied bounds, ReLU hull rows, phase facts, the ReLU propagation rules) and a projection: every renamed row of a proposed preprocessed query is exactly implied, and every ReLU is linked to an original one. Examples cover merging, fixing, renumbering and the ReLU facts, plus rejected tolerance snapping. |
| [import_marabou_preprocessing.py](Isabelle/tools/import_marabou_preprocessing.py), `Imported_Marabou_Preprocessed_*` | Untrusted exact re-derivation of native tightenings, and projection witnesses; generated replay theories for four `--preprocess` example runs. |
| [ReLU_Phase_Fixing.thy](Isabelle/ReLU_Phase_Fixing.thy), [ReLU_Phase_Fixing_Examples.thy](Isabelle/ReLU_Phase_Fixing_Examples.thy) | A ReLU phase justified by an exact linear proof of a phase-deciding bound from the query plus `y ≥ 0`, `y ≥ x`; model-set equality with the phase's split query; the `Relu_Fix_Active/Inactive` certificate steps; rejection of epsilon-style premises, including a satisfiable query whose unchecked phase fix would be UNSAT. |
| `Imported_Marabou_File_Phase_*`, `Imported_Marabou_Example_Phase_*` | Native file runs whose initial bounds fix a ReLU phase: three UNSAT proofs that depend on the unexplained phase bounds, replayed with checked phase steps, and one SAT model. |
| [Bounded_Inequality_Auxiliary.thy](Isabelle/Bounded_Inequality_Auxiliary.thy), [Bounded_Inequality_Examples.thy](Isabelle/Bounded_Inequality_Examples.thy) | A slack introduction plus an exactly implied finite opposite bound (cap); finite sequences; `bounded_decodes_like` transfer to a file's bytes; rejected unjustified caps. |
| [prepare_inequalities.py](Isabelle/tools/prepare_inequalities.py), `Imported_Marabou_Prepared_Inequality_*` | Untrusted local `le`/`ge` preparation with interval-arithmetic caps; generated replay theories for the three inequality example files. |
| [refresh_native_fixtures.py](Isabelle/tools/refresh_native_fixtures.py) | Reruns every native scenario and example file; requires identical data and refreshes only run reports, logs and provenance. |
| [Imported_Marabou_Solver_Relu_Aux_Inactive.thy](Isabelle/Imported_Marabou_Solver_Relu_Aux_Inactive.thy), [source](Isabelle/Imported_Marabou_Source_Relu_Aux_Inactive.thy) | A native proof whose sole PLC lemma is positive auxiliary lower to output upper zero, replayed to UNSAT of the processed query and, through three tableau steps, of the captured five-variable source. |

An expression `Linexpr c [(a1,x1), …]` evaluates as
`c + a1*v(x1) + …`. Lists are finite by construction and may contain duplicate
variables or zero coefficients. Coefficients, constants, bounds and valuations
are **mathematical reals** in the semantic core. The executable layer uses
separate rational data and `embed_query` to connect it to that same real
semantics; it does not restrict valuations to rational values.

A query conjoins its three finite lists: `linear_atoms`, `query_bounds`, and
`relu_atoms`. Missing bounds mean no restriction in that direction. Valuations
are total functions on natural numbers; only variables appearing in the query
are constrained. There is no C++ variable-count field in the abstract model.

## Assurance from the proved theorems

All project theory proofs are completed; there are no admitted proofs, aborted
proofs, or added axioms. The usual Isabelle/HOL foundations and proof kernel are
the basis of the result. Conditional theorems state their premises explicitly.

| Theorem(s) | Precisely what follows |
| --- | --- |
| `eval_terms_append`, `eval_add_linexpr`, `eval_scale_linexpr`, `eval_terms_cong` | Expression operations have the claimed real arithmetic meaning; evaluation depends only on mentioned variables. |
| `linear_eq_iff_two_inequalities`, `lower_bound_as_linear`, `upper_bound_as_linear` | Equality and bounds have the expected linear-constraint encodings. |
| `linear_le_add`, `linear_le_scale_nonnegative` | Adding valid inequalities, or scaling one by a nonnegative real, preserves truth. These are building blocks, not a complete certificate checker. |
| `inconsistent_bounds`, `query_inconsistent_bounds` | A lower bound strictly exceeding an upper bound excludes every valuation satisfying both. |
| `relu_phase_decomposition`, `satisfies_relu_phase_decomposition` | `y = max 0 x` is equivalent to `(x ≤ 0 ∧ y = 0) ∨ (0 ≤ x ∧ y = x)`. |
| `relu_phases_overlap_iff` | Both phase conditions hold exactly when input and output are zero. |
| `models_relu_split` | **If `ReLU x y` belongs to the query**, the parent model set equals the union of the two child model sets. All other constraints are retained. |
| `satisfiable_relu_split`, `unsatisfiable_relu_split` | Under that membership premise, SAT is equivalent to SAT of either child; UNSAT of both children implies UNSAT of the parent. |
| `satisfiable_iff_models_nonempty`, `unsatisfiable_iff_no_valuation`, `unsatisfiable_iff_models_empty` | Model-set and existential/universal definitions agree. |
| `fixed_aux_model_extension`, `fixed_aux_model_projection` | For a selected equality and globally fresh `s`, assigning `s=b` extends every original model; resetting `s` in a transformed model gives an original model. |
| `satisfiable_introduce_fixed_aux_iff`, `unsatisfiable_introduce_fixed_aux_iff` | Replacing the selected `e=b` by `e-s=0` and fixing both bounds of fresh `s` to `b` preserves SAT and UNSAT. |
| `check_after_fixed_aux_sound` | A checked rational auxiliary step followed by an accepted certificate proves UNSAT of the source query, with freshness and selection checked by the function. |
| `solver_linear_before_aux_unsatisfiable` | The explicit two-variable source query is UNSAT: its checked auxiliary step equals the earlier processed snapshot, whose native certificate replays. |
| `fixed_aux_sequence_satisfiable_iff`, `fixed_aux_sequence_unsatisfiable_iff` | Every successful finite list of checked introductions preserves SAT and UNSAT over real valuations. Each step checks the current query. |
| `check_after_fixed_aux_sequence_sound` | A successful sequence followed by an accepted terminal certificate proves the source query UNSAT. Failed steps cannot be skipped. |
| `relu_aux_model_extension/projection`, `satisfiable_introduce_relu_aux_iff` | A present ReLU and globally fresh `a` justify adding `y-x-a=0`, `a≥0`, and an optional upper cap derived from an explicit input lower bound. Models extend with `a=y-x` and project back; SAT/UNSAT are preserved. |
| `check_after_relu_aux_sound` | One checked ReLU introduction, followed by checked scalar-fixed steps and a certificate, proves UNSAT of the source over real valuations. |
| `solver_before_relu_aux_unsatisfiable` | The explicit four-variable source is UNSAT through a checked ReLU auxiliary introduction and existing solver-produced evidence. The earlier source is hand-written HOL data. |
| `Imported_Marabou_Native_Relu_Intro.imported_before_relu_query_unsatisfiable` | The captured four-variable query is UNSAT through a checked native ReLU introduction, three tableau introductions, and the complete solver-produced proof. Extraction and decoding remain unverified. |
| `relu_aux_sequence_satisfiable_iff`, `check_after_relu_aux_sequence_sound` | Every successful finite checked ReLU sequence preserves real satisfiability; composing it with tableau steps and an accepted proof certifies the original query UNSAT. |
| `Imported_Marabou_Native_Relu_Sequence.imported_before_relu_query_unsatisfiable` | The captured six-variable query is UNSAT through two checked native ReLU introductions, five tableau steps and the complete solver proof. |
| `Imported_Marabou_Native_Relu_Chain.imported_before_relu_query_unsatisfiable` | The preserved chained query's full proof, including the positive-output rule, certifies its explicit six-variable starting query UNSAT over real valuations. A fresh native run reproduces the data exactly. |
| `native_source_needs_both_relus` | The two-ReLU before-query is UNSAT, and either one-ReLU deletion has an explicit real model. |
| `solver_split_before_aux_unsatisfiable` | Five checked introductions and a proved term-order equivalence connect an explicit nine-variable source query to the binary-split capture and its replayed certificate. |
| `normalize_linear_correct`, `normalize_bound_correct`, `embed_query_normalization` | Rational query normalization preserves the meaning of each constraint over real valuations, with ReLU atoms retained separately. |
| `weighted_sum_wellformed`, `weighted_sum_nonpositive` | Successful combination requires matching lengths and nonnegative weights; its value is nonpositive in every model of the normalized rows. |
| `eval_collect_terms`, `constant_contradiction_positive` | Combining repeated variable coefficients preserves evaluation; an accepted constant contradiction evaluates strictly positively for every real valuation. |
| `check_linear_leaf_sound` | `check_linear_leaf Q ws` implies `unsatisfiable (embed_query Q)`, including when the query still contains ReLUs. No assumptions on the solver are needed. |
| `check_linear_implication_sound`, `check_linear_bound_sound` | An accepted nonnegative row combination proves the proposed inequality or bound in every real model of `embed_query Q`. |
| `rat_linear_bound_preserves_models` | Adding an accepted linear bound preserves the entire real model set; the premise is checked before insertion. |
| `embed_rat_active_split`, `embed_rat_inactive_split` | Rational child-query operations embed to exactly the existing real splits. |
| `check_relu_upper_bound_sound`, `rat_relu_upper_preserves_models` | A present ReLU and an explicit input upper bound justify an output bound at least `max(0,u)`; adding it preserves the real model set. |
| `check_relu_aux_upper_bound_sound`, `rat_relu_aux_upper_preserves_models` | A present ReLU, an explicit input lower bound `l`, and two checked linear witnesses for `f-b-a=0` justify `a≤max(0,-l)` or a weaker bound, preserving all real models. |
| `check_relu_output_aux_upper_bound_sound`, `rat_relu_output_aux_upper_preserves_models` | A present ReLU, an explicit strictly positive output lower bound, and two checked equation witnesses justify auxiliary upper bound zero or weaker, preserving all real models. Zero output alone is insufficient. |
| `check_relu_aux_lower_output_upper_bound_sound`, `rat_relu_aux_lower_output_upper_preserves_models` | A present ReLU, an explicit strictly positive auxiliary lower bound, and two checked equation witnesses justify output upper bound zero or weaker, preserving all real models. A zero auxiliary alone is insufficient. |
| `Imported_Marabou_Source_Relu_Aux_Inactive.imported_source_query_unsatisfiable` | The explicit captured five-variable source of the `relu_aux_inactive` run is UNSAT over real valuations, through checked tableau steps and the native proof using the positive-auxiliary rule. Extraction and decoding remain unverified. |
| `check_rat_assignment_iff`, `check_rat_assignment_sound` | For a finite rational assignment with distinct variables, acceptance holds exactly when its embedding is a real model of the embedded query; acceptance gives SAT. |
| `fixed_aux_sequence_assignment_satisfiable`, `relu_aux_sequence_assignment_satisfiable` | An assignment accepted for a processed query proves its explicit starting query SAT through checked introductions. |
| `Imported_Marabou_Native_Relu_Sat.imported_before_relu_query_model` | The exactly reconstructed native SAT assignment is a real model of the explicit seven-variable starting query. Extraction, decoding and the solver are unverified. |
| `decode_encode_query` | Every query whose linear expressions have constant 0 is decoded back exactly from its canonical bytes. |
| `Imported_Marabou_Exact_Texts.solver_<scenario>_text_unsatisfiable` / `solver_relu_sat_text_model` | The query denoted by the exact bytes of each saved `.mqx` file is UNSAT (nine scenarios) or has the exact native model (`relu_sat`). The native run built its query in C++; it did not read these files. |
| `same_constraints_models`, `decodes_like_unsatisfiable`, `decodes_like_model` | A result about a query transfers to any file whose decoding has the same constraint sets, whatever its statement order or number spelling. |
| `inequality_aux_model_extension`, `satisfiable_introduce_inequality_aux_iff` | A fresh slack set to `b−eval(e)` gives the exact equality replacement with a nonnegative LE or nonpositive GE bound; satisfiability is preserved. |
| `check_after_inequality_aux_sequence_sound` | Checked inequality, ReLU and scalar-fixed introductions followed by an accepted certificate prove real-semantic UNSAT of the original query. |
| `check_assignment_after_inequality_aux_sequence_sound` | An exact model after a checked inequality sequence is also a model of the starting query. |
| `bounded_inequality_sequence_satisfiable_iff`, `bounded_decodes_like_unsatisfiable`, `bounded_decodes_like_model` | Slack introductions with exactly implied caps preserve real satisfiability. A result about the captured prepared query transfers to the original `le`/`ge` file's bytes. |
| `Imported_Marabou_Example_*.query_file_unsatisfiable` / `query_file_model` | The query denoted by the exact bytes of each example file, which the native engine itself read, is UNSAT or has the exact native model. |
| `apply_facts_models`, `check_projection_model`, `check_projection_unsatisfiable` | Checked facts keep every real model. An accepted projection maps every model of the original query to a model of the proposed preprocessed query, so its UNSAT proves the original UNSAT. |
| `check_relu_fixed_active_sound`, `relu_fixed_active_models` (and inactive versions) | An exactly proved phase-deciding bound makes the query's real models exactly those of that phase's split query; `Relu_Fix_*` certificate steps rely on this. |
| `check_certificate_sound`, `check_certificate_no_model` | An accepted finite tree excludes every real valuation of its embedded root query. Split nodes check membership and both phases; propagation nodes check the rule and their continuation. |
| `check_certificate_rejects_model` | A query with a real model has no accepted certificate of this datatype. Rejection of one certificate does not imply SAT. |
| `Imported_Marabou_*.imported_query_unsatisfiable` | The explicit processed rational queries in these theories have no real solutions. Hash comments record file provenance; byte decoding and preprocessing are not formalized. |
| `Imported_Marabou_Source_*.imported_steps_match_query` | The checked finite introductions produce exactly the independently captured processed query, including all rows, bounds, and ReLUs. |
| `Imported_Marabou_Source_*.imported_source_equisatisfiable/imported_source_query_unsatisfiable` | Each explicit captured source is equisatisfiable with its processed query and is UNSAT, using the checked sequence and native proof. |

Each split replaces every copy of the selected ReLU atom with explicit linear
phase constraints. The active child adds `x ≥ 0, y - x = 0`; the inactive child
adds `x ≤ 0, y = 0`. The theorem allows duplicate atoms, zero input, and even
equal variable indices; it does not assume that the branches are disjoint.

The hand-written examples use variable 0 for `x` and variable 1 for `y`:

* `sat_example_satisfiable`: `x + y = 2`, `-1 ≤ x ≤ 1`, `y = ReLU(x)`.
  `sat_example_witness` proves that the valuation assigning 1 to every variable
  satisfies it.
* `unsat_example_unsatisfiable`: `x ≤ 0`, `y ≥ 1`, `y = ReLU(x)`.
  Both children contain only linear atoms and bounds. The active child would
  require `y = x ≤ 0`; the inactive child would require `y = 0`. Both contradict
  `y ≥ 1`, and the general splitting theorem closes the parent.
* `zero_in_both_children`: the zero valuation satisfies both children of a
  query containing a single ReLU.

The rational examples additionally prove acceptance of fractional contradictory
bounds, an affine equality with repeated variables, and a constant-only
contradiction. They prove rejection of negative weights, missing/extra weights,
zero weights, zero contradiction margin, an empty query, and a nonzero residual
coefficient of `1/1000000`. Two satisfiable counterexamples have explicit real
models. These computations use `code_simp` to produce HOL proofs.

`unsat_example_via_leaf_certificates` closes the earlier ReLU example using
two accepted leaf certificates and the existing splitting theorem. Explicit
equalities identify the embedded rational leaves with the original real child
queries. `unsat_example_via_recursive_certificate` now proves the same result
with the general tree checker, and `nested_query_unsatisfiable` exercises two
levels of splitting.

`Relu_Upper x y u b child` adds `y ≤ b` after checking the ReLU, the existing
bound `x ≤ u`, and `max(0,u) ≤ b`. The extended soundness theorem composes this
inference with linear leaves and splits. See the [propagation
contract](notes/RELU_BOUND_PROPAGATION.md) for source correspondence and examples.

`Linear_Bound bound weights child` first checks an exact linear implication,
then checks the continuation with the proved bound added. This supplies
non-ground input premises to `Relu_Upper`. The [linear implication
contract](notes/RATIONAL_LINEAR_IMPLICATION.md) explains the residual-constant
check and the native `e_x + wᵀA` explanation reconstruction.

`Relu_Aux_Upper b f a l u pos neg child` checks `f=ReLU(b)` membership,
`b≥l`, two linear witnesses for `f-b-a=0`, and `max(0,-l)≤u` before adding
`a≤u`. The [auxiliary propagation contract](notes/RELU_AUX_BOUND_PROPAGATION.md)
explains the lower-bound reconstruction and actual solver captures.

## Import and replay

The adapter accepts the pinned `JsonWriter::writeProofToJson` format for finite
homogeneous tableaux, finite bounds, auxiliary-form ReLUs, binary phase splits,
linear contradictions, and **the four PLC lemma patterns above, with empty or
nonempty tableau explanations reconstructed exactly**.
Auxiliary lemmas additionally require checked witnesses for their equation.
It requires a
separate expected processed-query file. Numbers mean the exact rational values
of their serialized decimal tokens; they do not silently mean the original
binary doubles or network-file numbers.

From the project root, create a replay session in a new directory:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/nested_query.json \
  --certificate Isabelle/tests/fixtures/marabou/nested.json \
  --output /tmp/marabou-replay/Imported_Check.thy --session
isabelle build -d Isabelle -D /tmp/marabou-replay
```

The first command reconstructs candidate data. The successful Isabelle build
proves `Imported_Check.imported_query_unsatisfiable` by `code_simp` and
`check_certificate_sound`. The [import contract](notes/CERTIFICATE_IMPORT.md)
documents unsupported evidence, fixture provenance, and test commands.

The first [actual solver capture](notes/SOLVER_CAPTURE.md) uses the native
engine with proof production enabled and preprocessing/DeepSoI disabled.
Initialization succeeds, `solve` reports UNSAT, and its row certificate replays
unchanged through the existing importer. This run has no ReLUs or simplex
pivots; it tests the linear proof-production and capture path.

The subsequent [ReLU solver capture](notes/SOLVER_RELU_CAPTURE.md) produces
`b ≤ -1/2 ⇒ ReLU(b) ≤ 0` and a linear contradiction with margin `1/4`.
The entire native certificate replays through the existing checker. A separate
HOL witness proves its linear relaxation satisfiable, so nonlinear evidence is
essential. Reproduce it with:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output /tmp/marabou-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-relu-capture
```

The [auxiliary captures](notes/RELU_AUX_BOUND_PROPAGATION.md) now replay the
previously unsupported broader variant without editing its proof. A second
run uses `b≥1/2 ⇒ aux≤0` as its sole nonlinear inference, followed by an exact
contradiction. Its linear relaxation also has a proved real model.

The [binary split capture](notes/SOLVER_RELU_SPLIT_CAPTURE.md) now exercises
native branching and backtracking: one split, three tableau pivots, and two
closed linear children. Each child has an exact contradiction margin of `1/2`.
The unchanged checker proves both child queries and their parent UNSAT; a
separate HOL model shows that the root's linear relaxation is satisfiable.

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_split --output /tmp/marabou-relu-split
isabelle build -d Isabelle -D /tmp/marabou-relu-split
```

The [auxiliary introduction](notes/TABLEAU_AUXILIARY.md) adds a first verified
transformation before certificate checking. `rat_introduce_fixed_aux Q i s`
checks a selected equality and global freshness, then constructs the new row
and fixed bounds. The earlier linear capture is now linked exactly to an
explicit pre-auxiliary query. That first example uses hand-written HOL source data.

The [finite-sequence extension](notes/TABLEAU_AUXILIARY_SEQUENCE.md) composes
those steps and applies them to the binary-split capture. Five introductions
give exactly the saved fourteen-variable query. A separate arithmetic proof
accounts for the final equation's term order, and the native certificate
proves UNSAT of the explicitly described nine-variable source query.

The [source capture/import extension](notes/SOURCE_QUERY_CAPTURE.md) now emits
the source query and proposed steps automatically from each native run.
The five original scenarios have been recaptured and replayed, with unchanged processed
query and proof bytes. The capture command above now generates a source-query
UNSAT theorem as well as the processed-query theorem. A separate
`import_marabou_source.py` command can replay the four saved artifacts without
running the solver; instructions are in the linked note.

[Fresh ReLU auxiliary introduction](notes/RELU_AUXILIARY.md) is now verified
as a separate mathematical step. It retains the ReLU and adds its defining
auxiliary equation and justified bounds. One checked step exactly produces
the saved `relu_aux` source query; its existing tableau introductions and
native proof then certify the earlier four-variable HOL query.

The [native ReLU introduction capture](notes/NATIVE_RELU_INTRO_CAPTURE.md)
now starts with a plain `ReluConstraint(0,1)`, calls the real
`transformToUseAuxVariables` method, and independently records its entire
before/after query. The six-artifact importer generates a checked
four-variable source UNSAT theorem. General preprocessing remains disabled.
That single-introduction milestone contained 48 theories and 146 importer tests.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_intro --output /tmp/marabou-native-relu-intro
isabelle build -d Isabelle -D /tmp/marabou-native-relu-intro
```

The [finite ReLU sequence extension](notes/RELU_AUXILIARY_SEQUENCE.md) now
captures two native calls and checks their entire final result. That milestone
contained 51 theories and 174 importer tests.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sequence --output /tmp/marabou-two-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-two-relu-capture
```

The [positive-output extension](notes/RELU_OUTPUT_BOUND_PROPAGATION.md) now
checks the rule encountered in the preserved exploratory chained query.
Its complete unchanged proof replays, and a fresh `relu_chain` solver run
reproduces all six data artifacts. That milestone brought the main session to
54 theories, with 197 importer tests and 55 exported SML checks passing.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_chain --output /tmp/marabou-output-bound-capture
isabelle build -d Isabelle -D /tmp/marabou-output-bound-capture
```

The [positive-auxiliary extension](notes/RELU_AUX_LOWER_BOUND_PROPAGATION.md)
verifies the dual rule and a new `relu_aux_inactive` native run whose only PLC
lemma is `aux>=1/4 ⇒ f<=0`. Its unmodified proof replays to UNSAT of the
captured source. That milestone brought the session to 58 theories, with 221
importer tests and 70 exported SML checks passing.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_aux_inactive --output /tmp/marabou-aux-lower-capture
isabelle build -d Isabelle -D /tmp/marabou-aux-lower-capture
```

[Exact SAT assignments](notes/SAT_ASSIGNMENTS.md) add `check_rat_assignment`
and a native `relu_sat` run: one ReLU forced active, one inactive, both with
native auxiliary introductions. Its reported doubles are exactly dyadic and
are proved to be a model of every captured query stage. The main session now
contained 61 theories, with 236 importer tests and 81 exported SML checks passing.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sat --output /tmp/marabou-sat-capture
isabelle build -d Isabelle -D /tmp/marabou-sat-capture
```

The [exact text format](notes/EXACT_QUERY_FORMAT.md) gives queries a meaning
defined in HOL. Ten `.mqx` fixtures hold the captured starting queries; the
build checks each file against its HOL byte list and proves what it decodes
to. That milestone brought the session to 64 theories, with 246 importer tests
and 81 exported SML checks passing.

The [query-file workflow](notes/QUERY_FILE_WORKFLOW.md) lets the native harness
read such a file itself. Three example files were solved this way; their runs
reproduced the scenario artifacts byte-for-byte, and main-session theorems now
concern the examples' own bytes. That milestone contained 67 theories, with
262 importer tests and 81 exported SML checks passing.

The [inequality introduction extension](notes/INEQUALITY_AUXILIARY.md) adds
four theories and an exported module with 16 checks, bringing the session to
71 theories. Its examples are hand-written exact evidence. Two tableau-state
theories followed. A later step checked finite slack caps and connected
`le`/`ge` files to the native workflow, with three native inequality example
files. It was finished with fresh reruns of every native capture; the session
then had 81 theories and 279 Python tests passed.

[Phase fixing](notes/RELU_PHASE_FIXING.md) adds two theories and two
certificate constructors, and removes the workflow's last ReLU rejection
reason. The harness records ReLUs fixed before search, and four new native
example files replay. The session had 91 theories, with 290 Python tests
and 107 exported SML checks passing.

[Native preprocessing](notes/NATIVE_PREPROCESSING.md) adds a `--preprocess`
capture mode, the projection theory and its examples, an exact
re-derivation importer and four example files. Their results: two UNSAT with
native proofs after preprocessing, one refuted inside preprocessing, and one
SAT. That milestone had 101 theories; 307 Python tests and 107 exported SML
checks passed.

[Tableau pivots](notes/TABLEAU_PIVOT.md) continue the solver calculus: the
exact basis exchange, the exact form of Marabou's default ratio test,
moving pivots and bound flips, the native index arrays, and the soundness of
the simplex failure branch. A fuelled exact loop has proved `Feasible` and
`Infeasible` results. The session has 106 theories; 307 Python tests and 107
exported SML checks pass.

[Tableau initialization](notes/TABLEAU_INITIALIZATION.md) builds that loop's
starting tableau from a query, so its results are theorems about the query.
It copies Marabou's initial-basis selection exactly and matches the native
basis on all 20 captured runs, and it refutes `examples/linear_unsat.mqx`
without Marabou. The session has 110 theories; 312 Python tests and 107
exported SML checks pass.

## Connection to source and remaining scope

The inspected upstream revisions are pinned by the existing submodules:

* Marabou: `1c2f4788c32e2f4e407c356b763a8025c5578722`.
* ReluplexCav2017: `60b482eec832c891cb59c0966c9821e40051c082`.

The sources were inspected without modifying either repository. Findings and
open questions are recorded in:

* [MARABOU_SOURCE_MAP.md](notes/MARABOU_SOURCE_MAP.md): C++ concepts and control flow.
* [FORMALIZATION_MAP.md](notes/FORMALIZATION_MAP.md): the relation between HOL concepts and source, including mismatches.
* [LINEAR_CERTIFICATES.md](notes/LINEAR_CERTIFICATES.md): exact leaf-certificate mathematics, existing evidence, papers, and the next step.
* [RATIONAL_LINEAR_CHECKER.md](notes/RATIONAL_LINEAR_CHECKER.md): the implemented checker and its verified contract.
* [CERTIFICATE_IMPORT.md](notes/CERTIFICATE_IMPORT.md): recursive checking, the native JSON adapter, numeric contract, and replay instructions.
* [RELU_BOUND_PROPAGATION.md](notes/RELU_BOUND_PROPAGATION.md): the checked propagation rule, native lemma fields, scope restrictions, and replay examples.
* [RATIONAL_LINEAR_IMPLICATION.md](notes/RATIONAL_LINEAR_IMPLICATION.md): exact linear premises, their recursive checking, and native explanation reconstruction.
* [SOLVER_CAPTURE.md](notes/SOLVER_CAPTURE.md): the first actual solver execution, saved artifacts, reproduction commands, and precise assurance boundary.
* [SOLVER_RELU_CAPTURE.md](notes/SOLVER_RELU_CAPTURE.md): solver-produced nonlinear evidence, exact reconstruction, coverage limitations, and replay.
* [RELU_AUX_BOUND_PROPAGATION.md](notes/RELU_AUX_BOUND_PROPAGATION.md): the auxiliary rule, checked defining equation, lower explanations, and two additional solver captures.
* [SOLVER_RELU_SPLIT_CAPTURE.md](notes/SOLVER_RELU_SPLIT_CAPTURE.md): a native binary split, both exact leaf contradictions, source correspondence, and replay.
* [TABLEAU_AUXILIARY.md](notes/TABLEAU_AUXILIARY.md): one verified auxiliary introduction, checked rational interface, and the first explicit source-to-processed query connection.
* [TABLEAU_AUXILIARY_SEQUENCE.md](notes/TABLEAU_AUXILIARY_SEQUENCE.md): finite composition, the five-step binary-split connection, and the remaining capture/import boundary.
* [SOURCE_QUERY_CAPTURE.md](notes/SOURCE_QUERY_CAPTURE.md): captured pre-initialization queries and proposed introductions, strict import, and source/processed replay for the five original native scenarios.
* [RELU_AUXILIARY.md](notes/RELU_AUXILIARY.md): one fresh ReLU auxiliary, optional finite cap, and checked source-query certificate composition.
* [NATIVE_RELU_INTRO_CAPTURE.md](notes/NATIVE_RELU_INTRO_CAPTURE.md): the native method call, six artifacts, full replay, and extraction boundary.
* [RELU_AUXILIARY_SEQUENCE.md](notes/RELU_AUXILIARY_SEQUENCE.md): finite checked ReLU composition, the two-ReLU native capture, and real replay.
* [RELU_OUTPUT_BOUND_PROPAGATION.md](notes/RELU_OUTPUT_BOUND_PROPAGATION.md): the strict positive-output rule, complete replay of the preserved chain, boundary counterexamples, and fresh native provenance.
* [RELU_AUX_LOWER_BOUND_PROPAGATION.md](notes/RELU_AUX_LOWER_BOUND_PROPAGATION.md): the dual positive-auxiliary rule, its native capture and replay, and an inventory of the remaining emitted native ReLU lemma patterns.
* [SAT_ASSIGNMENTS.md](notes/SAT_ASSIGNMENTS.md): the exact assignment checker, the native SAT capture, reconstruction policy and assurance boundary.
* [EXACT_QUERY_FORMAT.md](notes/EXACT_QUERY_FORMAT.md): the exact text format, its HOL decoder and round trip, the ten capture texts, and the remaining trust boundary.
* [QUERY_FILE_WORKFLOW.md](notes/QUERY_FILE_WORKFLOW.md): the one-command query-file workflow, supported inputs, rejection reasons, examples and trust boundary.
* [INEQUALITY_AUXILIARY.md](notes/INEQUALITY_AUXILIARY.md): verified signed slack introductions, finite composition, SAT/UNSAT checking, checked finite caps and the `le`/`ge` file workflow.
* [NATIVE_PREPROCESSING.md](notes/NATIVE_PREPROCESSING.md): the `--preprocess` mode, checked facts and projection, re-derived infeasibility, examples and limits.
* [RELU_PHASE_FIXING.md](notes/RELU_PHASE_FIXING.md): ReLU phases fixed by the initial bounds, the checked `Relu_Fix_*` steps, the harness record and four native examples.
* [TABLEAU_ASSIGNMENT_UPDATE.md](notes/TABLEAU_ASSIGNMENT_UPDATE.md): the first exact tableau-state transition, corresponding to `Tableau::setNonBasicAssignment(..., true)`.
* [TABLEAU_PIVOT.md](notes/TABLEAU_PIVOT.md): exact pivots, the zero-tolerance Harris ratio test, native index arrays, the simplex failure theorem and a fuelled sound loop.
* [TABLEAU_INITIALIZATION.md](notes/TABLEAU_INITIALIZATION.md): the starting tableau of a query, query-level SAT/UNSAT results, the native initial basis reproduced on 20 runs, and findings.
* [CONTINUATION_LOG.md](notes/CONTINUATION_LOG.md): the persistent per-invocation working record.
* [ACTIVATION_REUSE.md](notes/ACTIVATION_REUSE.md): UAT's existing polymorphic `Sigmoid_Definition.sigmoid`, recorded for future real sigmoid semantics without duplicating its definition.
* [RELUPLEX_MARABOU_LINEAGE.md](notes/RELUPLEX_MARABOU_LINEAGE.md): historical comparison, with Marabou as the verification target.

The restricted `InputQuery` extraction and JSON import are unverified programs.
No verified C++/JSON input decoder, Alethe importer, or support for propagation
rules beyond the four described above (plus the checked root phase-fixing
steps) is implemented. The `.mqx` format has
a HOL decoder and a build-time check binding its byte list to the file.
SAT assignments are checked
exactly, but reconstruction from native doubles is an untrusted step.
The model does not
establish the correctness of the preprocessing procedure (the results of
`--preprocess` runs are checked instead),
tableau construction, the C++ simplex and pivot code, floating-point
comparisons, search termination, or C++ state updates. Pivots and simplex
steps are modeled only as exact abstractions
([TABLEAU_PIVOT.md](notes/TABLEAU_PIVOT.md)). In particular, it does not prove that any
actual Marabou call satisfies the hypotheses of our split rule.

Network file parsing, ONNX/TensorFlow, other activations, DeepPoly, DeepSoI,
parallel search, Split-and-Conquer, and Gurobi integration remain outside the
initial fragment. A proof about an imported processed tableau still
needs a justified connection to the original query and its numeric interpretation.

## Next smallest meaningful target

The three checker extensions requested after milestone 20 are complete:
`le`/`ge` files, ReLU phases fixed before search, and checked native
preprocessing. What remains outside the checked pipeline is described in
[NATIVE_PREPROCESSING.md](notes/NATIVE_PREPROCESSING.md#assurance-and-limits).

The solver calculus now runs from a query to a result. It builds the starting
tableau as Marabou does, including its initial basis, and ends in an exact
simplex loop whose `Simplex_Unsat` result proves the query unsatisfiable
([TABLEAU_INITIALIZATION.md](notes/TABLEAU_INITIALIZATION.md)). ReLUs are
only relaxed. The next targets follow the audit:
* the bound-application and local-conflict milestone;
* native auxiliary-form ReLU splitting in the tableau state;
* one search frame with a coverage invariant.

Together these would let the HOL solver refute queries that need case
splits. These remain exact real-arithmetic models; factorization and
floating point stay outside the theorems. See
[the project-direction audit](notes/PROJECT_DIRECTION_AUDIT.md).
