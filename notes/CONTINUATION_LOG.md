# Continuation log

Persistent working record required by [CLAUDE_HANDOFF.md](../CLAUDE_HANDOFF.md)
section 12. Newest entry last. Earlier milestone results are in
[BUILD_RESULT.md](BUILD_RESULT.md).

## 2026-09-23, invocation 1: positive auxiliary lower bound (milestone 17)

Current objective and completion condition:
verify `y = ReLU(x), y - x - a = 0, 0 < l <= a  ⇒  y <= u` for every `u >= 0`,
add it to the recursive checker and SML export, extend the strict adapter, and
replay an unmodified native proof that contains this lemma to a starting-query
UNSAT theorem through the existing checked pipeline.

Baseline re-established before editing (HEAD `60016b0`, staging empty, large
inherited uncommitted tree preserved):

* `isabelle version`: `Isabelle2025-2`.
* `isabelle build -D Isabelle`: exit 0, up to date, `0:00:02 elapsed time`.
* `python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'`: exit 0,
  197 tests passed.
* `upstream/Marabou` at `1c2f4788c32e2f4e407c356b763a8025c5578722`, clean.

Source re-inspected at that revision:

* `src/engine/ReluConstraint.cpp::notifyLowerBound`, lines 207–226: the
  `_auxVarInUse && variable == _aux && FloatUtils::isPositive(bound)` branch
  calls `addLemmaExplanationAndTightenBound(_f, 0, UB, {_aux}, LB, *this,
  true, LEMMA_CERTIFICATION_TOLERANCE)`, then tightens `_b <= -bound` through
  the tightening row (a linear, explained update, not a lemma).
  `checkIfLowerBoundUpdateFixesPhase` marks the phase inactive first.
* `src/proofs/Checker.cpp::checkReluLemma`, lines 685–689: `causingVar == aux`,
  LB, `affectedVar == f`, UB, `isPositive(explainedBound + epsilon)`, returns 0.
  Epsilon is not inherited; HOL requires an exact positive premise.
* `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound`,
  lines 414–494: a lemma is recorded only if the affected bound tightens.
* `src/engine/BoundManager.cpp::propagateTightenings`, lines 268–284: constraint
  notifications run in ascending variable index, lower before upper. This fixes
  which ReLU rule fires first when several bounds tighten in the same round.

Progress checkpoint (same invocation):

* Added `Isabelle/ReLU_Aux_Lower_Bound_Propagation.thy`:
  `relu_positive_aux_output_zero`, the zero-boundary fact
  `relu_zero_aux_does_not_fix_output`, `check_relu_aux_lower_output_upper_bound`,
  `check_relu_aux_lower_output_upper_bound_sound`,
  `rat_relu_aux_lower_output_upper_preserves_models`,
  `unsatisfiable_relu_aux_lower_output_upper_bound`.
* `Rational_Proof_Trees.thy`: constructor `Relu_Aux_Lower_Output_Upper`,
  its `check_certificate` equation and soundness-induction case; both SML
  `export_code` lines include the constructor and checker.
* Local harness only: `capture.cpp` scenario `relu_aux_inactive`
  (aux=x0, b=x1, f=x2, w=x3, t=x4; a=w, f=t, f-b-a=0; w,t in [1/4,2]).
  A probe and the canonical driver run (`Isabelle/generated/aux_lower_capture`)
  both exited 0 and produced byte-identical data: one native PLC lemma
  `causVar 0 L -> affVar 2 U, bound 0.0, expl [row0: -1]`, then a row leaf.
  The generated standalone replay built with exit 0.
* Importer: `AuxLowerOutputUpperLemma` / `ReluAuxLowerOutputUpper`; lower-cause
  lemmas must match exactly one pattern and ReLU in total; premise must be
  exactly positive; the conclusion bounds the output; both equation directions
  reconstructed. Capture driver checks the certificate shape.
* Generated `Imported_Marabou_Solver_Relu_Aux_Inactive.thy` and
  `Imported_Marabou_Source_Relu_Aux_Inactive.thy`; wrote
  `ReLU_Aux_Lower_Bound_Examples.thy`. `isabelle build -D Isabelle`: exit 0
  (0:00:45). `build_log -H 'Error|Warning'`: no output.
* Python suite at this point: 8 expected provenance failures (harness and
  importer hashes changed). Plan: finish tests, freeze tool sources, then rerun
  all nine scenarios and refresh provenance from actual executions.

Milestone 17 result: **complete** (both the generic theorem and an unmodified
native proof using the rule, replayed to a starting-query theorem).

Files changed or added this milestone:
`Isabelle/ROOT`, `Isabelle/Rational_Proof_Trees.thy`,
`Isabelle/ReLU_Aux_Lower_Bound_Propagation.thy` (new),
`Isabelle/ReLU_Aux_Lower_Bound_Examples.thy` (new),
`Isabelle/Imported_Marabou_Solver_Relu_Aux_Inactive.thy` and
`Isabelle/Imported_Marabou_Source_Relu_Aux_Inactive.thy` (generated),
`Isabelle/tools/import_marabou_json.py`, `Isabelle/tools/capture_marabou_solver.py`,
`Isabelle/tools/solver_capture/capture.cpp`,
`Isabelle/tests/test_marabou_aux_lower_bound.py` (new),
`Isabelle/tests/test_marabou_import.py`, `Isabelle/tests/test_marabou_source_import.py`,
`Isabelle/tests/proof_tree_smoke.ML`, seven new `solver_relu_aux_inactive*`
fixtures, eight refreshed `solver_*_provenance.json` files, and notes
(`RELU_AUX_LOWER_BOUND_PROPAGATION.md` new; README, BUILD_RESULT,
CERTIFICATE_IMPORT, FORMALIZATION_MAP, MARABOU_SOURCE_MAP,
RELU_OUTPUT_BOUND_PROPAGATION and the fixture README updated).

Last successful Isabelle build: `isabelle build -c -e -D Isabelle` exit 0
(58 theories, 0:00:48), then `isabelle build -D Isabelle` exit 0, up to date.
Other checks: 221 Python tests OK; SML 8 + 62 OK; build_log filter empty;
no forbidden tokens; 360 local links resolve; `git diff --check` clean.

Native artifacts / provenance: new `relu_aux_inactive` capture; all nine
scenarios rerun under `Isabelle/generated/aux_lower_refresh_<scenario>`, data,
reports and logs byte-identical; only tool/binary hashes changed in the eight
older provenance records, now replaced by the refreshed ones.

Open issue / boundary: the capture's auxiliary is an explicit source variable,
not a `transformToUseAuxVariables` result. No solver defect is claimed.

Next concrete action (milestone 18, roadmap A): support the emitted
`ReluConstraint.cpp:294` lemma, output upper to input upper
(`x <= relu(x) = y <= u` gives `x <= c` for `u <= c`), with an exact guard,
constructor, importer pattern, tests and a native capture; then line 366,
auxiliary upper zero to input lower zero (first lower-bound conclusion).

## 2026-09-23, invocation 1 continued: roadmap A inventory, then roadmap D

Inventory of proof-mode ReLU lemma sites (`ReluConstraint.cpp` lines 180,
201, 212, 237, 294, 317, 344, 366) is in RELU_AUX_LOWER_BOUND_PROPAGATION.md.
Six are supported. Lines 294 and 366 are not. A scratch probe
(`Isabelle/tools/solver_capture/probes/relu_lemma_reachability.cpp`, built in
the session scratchpad from the pinned sources, not linked into the capture
harness) ran four tiny queries: none emitted either lemma; three ended with
row contradictions, `aux_zero` with `f>=-1` ended with a delegated leaf.
Reasons from source: the row tightener throws on crossing bounds before
notification (line 294), and row-derived upper bounds are loosened by 1e-6 so
`isZero` fails (line 366). Decision: leave both open until needed.

Next objective (milestone 18, roadmap D): exact rational SAT assignments.
Completion condition: a HOL checker whose acceptance proves a real model of
`embed_query Q` (every linear atom, bound and ReLU), lifted through checked
introductions to the starting query, plus an actual native SAT run whose
reported assignment is reconstructed exactly and checked in Isabelle.

Milestone 18 result: **complete**. `Rational_Assignment.thy` (checker,
soundness, completeness for rational assignments, lifting, SML export),
`Rational_Assignment_Examples.thy`, `Imported_Marabou_Native_Relu_Sat.thy`
(generated), `import_marabou_assignment.py` (new), `import_marabou_source.py`
(`reconstruct_queries` factored out, behavior unchanged), `capture.cpp`
(`relu_sat`), `capture_marabou_solver.py` (SAT branch), new tests
`test_marabou_assignment.py` and `assignment_smoke.ML`, nine `solver_relu_sat*`
fixtures, ten refreshed provenance records, notes (`SAT_ASSIGNMENTS.md` new;
README, BUILD_RESULT, CERTIFICATE_IMPORT, FORMALIZATION_MAP,
MARABOU_SOURCE_MAP and fixture README updated).

Last successful Isabelle build: `isabelle build -c -e -D Isabelle` exit 0
(61 theories), then `isabelle build -D Isabelle` exit 0, up to date.
Other checks: 236 Python tests OK; SML 8 + 62 + 11 OK; build_log filter empty;
no forbidden tokens; 380 links resolve; `git diff --check` clean; upstream clean.

Boundary: reconstruction of doubles is untrusted; the SAT theorem concerns the
explicit HOL queries and assignment only.

Next concrete action (milestone 19, roadmap B): specify a narrow exact input
representation for linear/ReLU queries (starting from the existing
`marabou-plain-relu-query-v1`/`marabou-source-query-v1` JSON shape, exact
decimal meaning), state the relation from structured data to `rat_query`, and
choose a verified or proof-producing decoding workflow with an explicit trust
boundary; test malformed data and theorem-statement substitution.

Milestone 19 result: **complete** (first bounded step of roadmap B).
Added `Exact_Query_Format.thy` (decoder = meaning, encoder, round-trip
`decode_encode_query`, build-time `Exact_Query_Text.check_file`),
`Exact_Query_Format_Examples.thy`, generated `Imported_Marabou_Exact_Texts.thy`,
`tools/exact_query_text.py`, `tests/test_exact_query_text.py`, ten
`solver_<scenario>.mqx` fixtures, `notes/EXACT_QUERY_FORMAT.md`; README,
BUILD_RESULT, FORMALIZATION_MAP, CERTIFICATE_IMPORT and fixture README updated.
No harness or importer change, so provenance stayed valid.

Last successful Isabelle build: `isabelle build -c -e -D Isabelle` exit 0
(64 theories, 0:01:16), then `isabelle build -D Isabelle` exit 0, up to date.
Other checks: 246 Python tests OK; SML 8 + 62 + 11 OK; build_log filter
empty; no forbidden tokens; 395 links resolve; `git diff --check` clean.

Boundary: the native runs did not read the `.mqx` files; they were exported
from the JSON snapshots afterwards. The file check is build infrastructure.

Next concrete action (milestone 20, roadmap E): teach the local harness to
read a `.mqx` file (C++ parser, untrusted) into the plain-ReLU `InputQuery`,
capture as in `relu_sequence`/`relu_sat` (UNSAT or SAT), and have one driver
command emit a theory proving `decode_query <file bytes> = Some <captured
before-query>` plus the UNSAT or SAT theorem about the file; reject with clear
reasons otherwise. Include adversarial mutations and exact build instructions.

Milestone 20 result: **complete** (roadmap E, the bounded restricted-fragment
workflow). Added the harness `file` mode (`read_query_file`), `same_constraints`
/ `decodes_like` in `Exact_Query_Format.thy`, `import_marabou_query_file.py`,
`verify_query_file.py`, `capture_marabou_solver.py --query-file`, six example
files, three `Imported_Marabou_Example_*` theories, adversarial HOL lemmas,
`test_marabou_query_file.py`, `file_<example>_*` fixtures, refreshed provenance
for all ten scenarios, and `notes/QUERY_FILE_WORKFLOW.md`.

Last successful Isabelle build: `isabelle build -c -e -D Isabelle` exit 0
(67 theories, 0:01:40), then `isabelle build -D Isabelle` exit 0, up to date.
Other checks: 262 Python tests OK; SML 8 + 62 + 11 OK; build_log filter empty;
no forbidden tokens; 410 links resolve; `git diff --check` clean; upstream
clean; staging empty.

Open items (none blocking): the driver's pre-check rejection message mentions
a log directory that was not created (fix at the next harness/driver change,
which will need another provenance refresh); lines 294/366 ReLU lemma patterns
unsupported but hard to reach; `le`/`ge`, initial phase fixing, preprocessing,
network files and verified C++ remain out of scope.

State: the handoff's bounded roadmap (A inventory, B first step, D, E) has a
working, validated restricted-fragment release. Further work is scope
expansion (item C preprocessing, wider input support) and should be chosen
with the user.

## 2026-09-23, Codex resumption: review and signed slack introductions (milestone 21)

User requested review of Claude's progress and continued implementation.
Milestones 17–20 were complete, not an interrupted version of milestone 17.
The inherited 67-theory session built (exit 0, 0:00:03), and all 262 Python
tests passed in 2.664 seconds. The large inherited working tree was preserved.
Both upstream repositories were clean.

Reviewed the auxiliary-lower proof, exact assignment checker and lifting,
HOL decoder/round trip, constraint-set transfer, ML file comparison and
`external_file` use, query-file adapter/driver, and checkpoint records.
No soundness defect was identified in those examined parts. The known
nonexistent-log-directory diagnostic remains open; no shared capture/importer
source or saved provenance has been changed in this milestone.

Selected the next bounded preprocessing target: exact conversion of LE/GE
to equality with a fresh signed slack, and checked finite composition.
Inspected `Preprocessor.cpp::makeAllEquationsEqualities` (224–244):
both directions append +1; LE adds slack >= 0 and GE slack <= 0.
The native private method is called early by `Preprocessor::preprocess`,
whose remaining transformations are not justified by this single rule.

Added `Inequality_Auxiliary.thy`, `Rational_Inequality_Auxiliary.thy`,
`Inequality_Auxiliary_Sequence.thy` and `Inequality_Auxiliary_Examples.thy`.
Proved model extension/projection, embedding, real SAT/UNSAT preservation,
sequence/failure laws, composition with ReLU/tableau introductions and
certificate soundness, and exact SAT witness projection. Examples cover
both signs, affine and duplicate terms, zero slack, all-component freshness,
late failures, wrong-sign/collision counterexamples, decoded text and a
composed nonlinear refutation with a satisfiable linear relaxation.

The 71-theory session built and exported, exit 0:
`isabelle build -e -D Isabelle`, 0:01:46 elapsed.
All four SML scripts passed: 8 leaf, 62 tree, 11 assignment and 16 new
inequality-introduction checks. The new export reports three generated-library
partial-match warnings; index guards and finite-set construction were inspected
and the hidden helpers are not part of its public interface.

A fresh native UNSAT file capture is in
`Isabelle/generated/resume_review_chain`. The wrapper's first replay hit a
sandbox read-only SQLite database. The direct replay with required access
then passed (parent 0:01:48, replay 0:00:15, total 0:02:08).
Fresh complete-wrapper verification then passed for SAT in
`Isabelle/generated/resume_review_sat` and UNSAT in
`Isabelle/generated/resume_review_chain_full`. Both wrappers exited 0 and
printed their checked theorem. The generated sessions took 0:00:20 and
0:00:19 respectively. All six captured data artifacts from each run match
the canonical `relu_sat`/`relu_chain` fixtures exactly.

Milestone 21 result: **complete as a mathematical/checker milestone**.
Final `isabelle build -D Isabelle` exited 0, up to date, 0:00:03.
The final Python suite passed all 262 tests in 2.026 seconds; the four SML
scripts passed 97 total checks. The Isabelle Error/Warning log filter was
empty. The generated SML warnings discussed above remain documented rather
than hidden. No unfinished-proof or added-axiom commands occur in the 71
project theories. All 430 local links in 32 Markdown files resolve;
whitespace and `git diff --check` passed. Staging remains empty.

New durable files: the four theories above,
`Isabelle/tests/inequality_auxiliary_smoke.ML` and
`notes/INEQUALITY_AUXILIARY.md`. Updated `Isabelle/ROOT`, README, source and
formalization maps, the file-workflow note, this log, BUILD_RESULT and the
historical handoff's status pointer. No Python/C++ implementation, native
fixture or provenance record was changed.

Next integration boundary: the native pipeline still requires finite bounds
in both directions. Prove/check the opposite slack bound with exact linear
implications, then connect independently captured inequality-conversion
results to the native file workflow. New examples here are hand-written;
no native inequality preprocessing execution is claimed certified.

## 2026-09-23, invocation 2: first tableau assignment transition

The project-direction audit identified the absence of any formal tableau
state as the main Level-2 gap. The primary direction is now solver-calculus
formalization; existing certificate checking remains a secondary artifact.

Inspected `src/engine/Tableau.cpp` at the pinned upstream Marabou revision
`1c2f4788c32e2f4e407c356b763a8025c5578722`:

* `computeAssignment` (around line 376) defines the solved-row relation
  `xB = inv(B)*b - inv(B)*AN*xN`.
* `computeChangeColumn` (lines 1452–1457) computes `inv(B)*A_j`.
* `setNonBasicAssignment` (lines 1484–1504) changes a nonbasic value and,
  when `updateBasics` is true, adjusts every basic value by subtracting the
  corresponding change-column component times the value delta. Lower/upper
  bound update handlers call this with `true` at lines 1794 and 1816.

Added `Isabelle/Tableau_State.thy` and
`Isabelle/Tableau_Assignment_Update.thy`. The proved transition preserves
exact solved-row consistency, state well-formedness, and nonbasic bounds when
the assigned target obeys its bound. It also proves the resulting candidate
satisfies the represented tableau equations. The coefficient helper handles
duplicate linear-expression terms. No `sorry`, `oops`, `axiomatization`, or
`undefined` occurs in these theories.

Updated README and `notes/FORMALIZATION_MAP.md` to distinguish the modeled
operation from the unverified native factorization, floating-point status
logic, and cost-cache invalidation. Added `notes/TABLEAU_ASSIGNMENT_UPDATE.md`
with the equation/sign convention and the boundary of the claim.

Validation: `/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle build
-D Isabelle` exited 0: `Finished Marabou_Verification (0:01:39 elapsed time,
0:07:25 cpu time, factor 4.46)`. No Python suite was run; this checkpoint
adds HOL state/transition proofs and documentation only.

Next source audit: `Tableau::performPivot` (around line 696) and
`updateAssignmentForPivot` (line 2345). Native fake pivots only move a
nonbasic to another bound, while actual pivots swap entering/leaving
variables, update assignments/cost functions/indexes, and update the basis
factorization. Formalize the row-space-preserving basis exchange in exact
solved-row semantics before claiming any correspondence to that larger C++
transition.

## 2026-09-23, Claude invocation 3: user requested all three scope expansions

The user asked for all three expansions offered at the end of milestone 20:
`le`/`ge` support, certified initial phase fixing, and native preprocessing.
At start, the working tree held later Codex work: milestone 21 (signed
slacks), an unrecorded bounded-inequality file integration, the direction
audit, and the first tableau-state theories. A `codex` process was idle in
this directory. It made no file changes during this invocation.

Milestone 22 (finish `le`/`ge`): reviewed the bounded-inequality work;
added `tools/refresh_native_fixtures.py`; renamed the now-accepted
`rejected_inequality.mqx` to `inequality_linear_sat.mqx` and saved its
first native artifact set, with two new generated theories; generalized
the full-artifact example table; added provenance tests. Every native
capture was rerun under `Isabelle/generated/m22_refresh`; all saved data
reproduced exactly. Clean build (81 theories) exit 0, four SML scripts 97
checks, 279 Python tests OK, links/diff clean. See BUILD_RESULT.

Next: milestone 23, certified phase fixing. Design, from source:
`informConstraintsOfInitialBounds` fixes ReLU phases before any bound
manager exists. `Engine::solve` then applies each valid split through
`applySplit`, which adds every strictly tighter split bound as an
*unexplained* ground bound (Engine.cpp 2108–2134). The native checker never
sees these bounds. The plan is a checked HOL phase-fixing certificate step:
an exact linear implication of the phase condition from the query plus the
ReLU hull facts y ≥ 0 and y ≥ x, then the phase's split query. The harness
will record the ReLUs whose phase is fixed before solving, and the importer
will insert the steps at the proof root.

Milestone 23 (phase fixing) complete: `ReLU_Phase_Fixing` +
`_Examples`, `Relu_Fix_Active/Inactive` certificate constructors, harness
record `_phase_fixing.json` (file mode), importer premise search, four native
example files (three UNSAT proofs unreconstructable without the record),
11 new tests. Reruns `m23_refresh`: all old data, reports and logs identical.
Clean build (91 theories) exit 0; 107 SML checks; 290 Python tests OK.

Next: milestone 24, native preprocessing. Plan: run
`Engine::processInputQuery(input, true)` in a new harness mode. Capture the
preprocessor's output query P0 from a second, identical
`Preprocessor::preprocess` call, plus the variable maps from
`Engine::getPreprocessor()`. Check in HOL: the file's query → native slack
introductions → native ReLU auxiliaries (both already verified) → a new
checked *projection* to P0 (every renamed P0 constraint exactly implied,
after checked ReLU facts) → the existing tableau steps → certificate. SAT is
checked directly on the file's query.

Milestone 24 (native preprocessing) complete: `Preprocessing_Projection`
(+ `_Examples`), harness mode `file-preprocess` with a map record and an
infeasibility record, `import_marabou_preprocessing.py`, driver/wrapper
`--preprocess`, four native example files (two UNSAT with proofs after
preprocessing, one refuted inside preprocessing, one SAT), 17 new tests.
Reruns `m24_refresh`: all earlier data identical. Clean build (101
theories) exit 0 in 2:23; 107 SML checks; 307 Python tests OK; links and
diff clean.

State: all three requested scope expansions are implemented and validated.
Nothing is staged or committed. The audit's solver-calculus roadmap (next:
a basis-exchange pivot) is unchanged and is the natural next direction if
the user wants to continue.

2026-09-24. The user asked to commit and push, then to focus on the tableau
pivot. All prior work was committed as `0cd0dc4` and pushed to
`origin/main`. The commit message names the earlier agent sessions whose
uncommitted work it includes.

Milestone 25 (tableau pivots) complete. New theories: `Tableau_Pivot`,
`Tableau_Simplex_Step`, `Tableau_Index_Layout`, `Tableau_Simplex_Run`,
`Tableau_Pivot_Examples`. They cover:
* the exact exchange;
* the zero-tolerance Harris ratio test with admissibility and invariants;
* the simplex failure theorem;
* the native array refinement;
* a fuelled loop with sound `Feasible` and `Infeasible` results;
* worked runs.

Pure HOL; no tool or fixture changed. Clean build (106 theories) exit 0;
307 Python tests OK; SML smoke tests unchanged and passing; links and diff
clean. See [TABLEAU_PIVOT.md](TABLEAU_PIVOT.md).

Next (recommended): initialization. Build the initial tableau from a query's
equations with the scalar-fixed auxiliaries as basis. Prove
`tableau_represents` and the invariant, so that `simplex_run` gives
query-level results. Then the audit's milestone 3, bound application and
local conflicts. At the user's request, the milestone-25 work was then
committed and pushed as its own commit.

2026-09-24. The user chose initialization next: build the starting tableau
from a query so that the loop's results are statements about the query.

Milestone 26 complete:
* new theories `Tableau_Initialization`, `Tableau_Initial_Basis`,
  `Tableau_Initialization_Examples` and the generated
  `Imported_Marabou_Initial_Bases`;
* the harness records the native initial basis (`_initial_basis.json`);
* `import_initial_basis.py`;
* `test_initial_basis.py`.

Rerun `m26_refresh`: all earlier data identical, and 20 new records. HOL
reproduces the native basis on all 20. `examples/linear_unsat.mqx` is
refuted by the HOL simplex alone. See
[TABLEAU_INITIALIZATION.md](TABLEAU_INITIALIZATION.md).

Next (per the audit): bound application and local conflicts, then native
auxiliary-form ReLU splits and one search frame. The HOL solver could then
refute queries that need case splits. At the user's request, milestone 26
was then committed and pushed as its own commit.
