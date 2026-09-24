# Marabou JSON writer fixtures

`linear.json`, `relu.json`, `nested.json`, the four `propagation*.json`,
and the two `explained_*.json`
certificate files are the unedited output of the
pinned upstream `JsonWriter::writeProofToJson`, invoked by
[marabou_json_fixture.cpp](../../marabou_json_fixture.cpp).
The harness constructs the query, certificate, and `PLCLemma` objects by hand
and uses the real `ReluConstraint::getCaseSplit` for phase bounds.
For `explained_negative/positive` it calls `BoundExplainer::updateBoundExplanation`
on a supplied tableau row and `UNSATCertificateUtils::computeBound` on the
result; these explanation weights are computed by the native component.
It does not run the solver, preprocessing, or bound-notification/PLC callbacks.

For these nine fixtures, the separate `*_query.json` files are hand-written expected processed-query
manifests. Their numbers deliberately have exact finite binary representations,
so the writer's decimal rounding does not change these examples.

From the project root, regenerate the nine native certificate files with:

```sh
python3 Isabelle/tests/build_marabou_fixtures.py Isabelle/tests/fixtures/marabou
```

The generated `Imported_Marabou_Linear`, `Imported_Marabou_Relu`, and
`Imported_Marabou_Nested`, four `Imported_Marabou_Propagation*`, and two
`Imported_Marabou_Explained_*` theories
are part of the main Isabelle session.
Importer tests check that their data and provenance hashes match regeneration.
See the [import contract](../../../../notes/CERTIFICATE_IMPORT.md) for the
supported schema, exact numeric meaning, replay command, and assurance limits.
The [propagation contract](../../../../notes/RELU_BOUND_PROPAGATION.md) documents
the exact rule and the new fixtures: negative/positive input bounds, ordered
lemmas, and propagation in both branches of a split.
The [linear implication contract](../../../../notes/RATIONAL_LINEAR_IMPLICATION.md)
documents nonempty explanations, their exact reconstruction, and the native
component calls used for the two explained fixtures.

`solver_linear.json` is a tenth certificate with different provenance: a real
proof-enabled `Engine::solve` execution produced it. Its query snapshot was
written before solving, independently of the proof header. The capture harness
does not construct proof nodes or contradictions. The saved `solver_linear.log`,
`solver_linear_run.json`, and `solver_linear_provenance.json` record the execution
and hashes. `Imported_Marabou_Solver_Linear` replays it in the main session.
See [SOLVER_CAPTURE.md](../../../../notes/SOLVER_CAPTURE.md) for its exact query,
build dependencies, and assurance limits.

Regenerate this capture separately, using a new or empty output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --output /tmp/marabou-solver-capture
isabelle build -d Isabelle -D /tmp/marabou-solver-capture
```

The nine-fixture component generator above does not overwrite this capture.

`solver_relu.json` is an eleventh certificate, also produced by an actual
`Engine::solve` execution. One native ReLU upper-propagation lemma with a
nonempty explanation precedes its linear contradiction. The complete writer
output is retained; no lemmas were filtered. The matching snapshot, run report,
log, and provenance use the `solver_relu` prefix.
`Imported_Marabou_Solver_Relu` proves UNSAT, and `Solver_ReLU_Examples` proves
that its linear relaxation has a model, so the nonlinear inference is necessary.

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output /tmp/marabou-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-relu-capture
```

See [SOLVER_RELU_CAPTURE.md](../../../../notes/SOLVER_RELU_CAPTURE.md) for the
exact input, explanation weights, source correspondence, and supported-path
limitations. Both solver captures are separate from the nine-fixture generator.

`solver_relu_aux.json` and `solver_relu_aux_active.json` are two further actual
solver captures. The negative variant includes the auxiliary lemma rejected
by the earlier importer, with the same query/proof bytes as that trial.
The active variant has one auxiliary-upper lemma that closes its contradiction.
Their explanations, defining auxiliary equations, and UNSAT conclusions replay
in `Imported_Marabou_Solver_Relu_Aux` and `Imported_Marabou_Solver_Relu_Aux_Active`.
The active query's linear relaxation has a proved real model.

Both have independent query snapshots and `_run.json`, `.log`, `_provenance.json`
companions. Reproduce them with `--scenario relu_aux` and
`--scenario relu_aux_active` respectively. The negative lemma's `1.750002` is
decoded exactly as a rational weaker conclusion, not assumed equal to a
binary double. See
[RELU_AUX_BOUND_PROPAGATION.md](../../../../notes/RELU_AUX_BOUND_PROPAGATION.md)
for commands, formulas, source correspondence, and scope.
The component generator does not overwrite any solver capture.

`solver_relu_split.json` is the fourteenth certificate and fifth actual
solver capture. The native search produces one binary ReLU split and closes
both children with row-combination contradictions, each of exact margin `1/2`.
There are no PLC lemmas or delegated leaves. The independent query snapshot,
run report, log, and provenance use the same `solver_relu_split` prefix.
`Imported_Marabou_Solver_Relu_Split` replays the entire tree;
`Solver_ReLU_Split_Examples` proves both child queries UNSAT separately and
the root's linear relaxation satisfiable.

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_split --output /tmp/marabou-relu-split
isabelle build -d Isabelle -D /tmp/marabou-relu-split
```

See [SOLVER_RELU_SPLIT_CAPTURE.md](../../../../notes/SOLVER_RELU_SPLIT_CAPTURE.md)
for the query, native search settings, exact reconstruction, and assurance.
All four earlier solver scenarios were rerun with the shared final harness:
their query/proof bytes stayed unchanged; saved reports and provenance now
describe those refreshed executions.

All five actual scenarios have now been rerun with source capture enabled.
Each also has `_source.json` (copied from the actual `InputQuery` before
initialization) and `_steps.json` (proposed scalar-fixed introductions recovered
from added tableau columns before solving). Their processed-query/proof bytes
remain unchanged. Logs, reports and provenance record the refreshed runs and
the new artifact/importer hashes.

The five generated `Imported_Marabou_Source_*` theories prove the term-order
equivalence, exact result of the introductions, source/processed
equisatisfiability, and source UNSAT through the existing native proof.
The capture command now emits this source-aware replay automatically.
The list is a checked harness proposal, not a native initialization log.
See [SOURCE_QUERY_CAPTURE.md](../../../../notes/SOURCE_QUERY_CAPTURE.md)
for the four-file schema, standalone import command, and assurance boundary.

`solver_relu_intro.json` is a fifteenth saved writer certificate from a sixth
actual solver scenario. The input starts with a plain ReLU. The real native
`ReluConstraint::transformToUseAuxVariables` method introduces its auxiliary
before engine initialization. `_before_relu.json` and `_relu_step.json` record
the four-variable starting query and native call. The existing `_source.json`,
`_steps.json`, `_query.json` and `.json` record the five-variable result, three
tableau steps, eight-variable processed query, and full native proof.

`Imported_Marabou_Native_Relu_Intro` replays all six inputs and proves UNSAT
of the before-query. The after-query, tableau steps, processed query and proof
match the earlier `relu_aux` bytes; their native introduction provenance is new.
All five older scenarios were also rerun with the final shared harness, with
unchanged source/step/query/proof bytes and refreshed reports/logs/provenance.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_intro --output /tmp/marabou-native-relu-intro
isabelle build -d Isabelle -D /tmp/marabou-native-relu-intro
```

See [NATIVE_RELU_INTRO_CAPTURE.md](../../../../notes/NATIVE_RELU_INTRO_CAPTURE.md)
for the exact native call path, finite-bound import restrictions, generated
theorems and assurance boundary. The component fixture generator leaves this
capture untouched.

`solver_relu_sequence.json` is the sixteenth accepted writer certificate and
seventh fully replayed native scenario. Two plain ReLUs receive native
auxiliaries: six variables become eight, then thirteen after five tableau
introductions. The native proof has two explained output-upper lemmas, one
per ReLU, and one linear contradiction. Both ReLUs are necessary for UNSAT,
as proved by deletion models in `ReLU_Auxiliary_Sequence_Examples`.

`_before_relu.json`, `_relu_steps.json`, `_source.json`, `_steps.json`,
`_query.json` and `.json` are the six replay inputs.
`Imported_Marabou_Native_Relu_Sequence` checks the complete composition and
proves the original six-variable query UNSAT. Reports, logs and provenance
record the actual execution. All six earlier scenarios were rerun with the
final harness; their data bytes remained unchanged.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sequence --output /tmp/marabou-two-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-two-relu-capture
```

See [RELU_AUXILIARY_SEQUENCE.md](../../../../notes/RELU_AUXILIARY_SEQUENCE.md).
The separate [rejected_relu_chain](rejected_relu_chain/README.md) directory
preserves an exploratory native run whose output-lower propagation rule was
initially unsupported. That full proof now replays unchanged. The historical
directory name and original seven JSON files are retained.

`solver_relu_chain.json` is the seventeenth canonical accepted writer
certificate and eighth fully replayed native scenario. Its fresh run
reproduces all six historical data artifacts byte-for-byte, with full
provenance for the new execution. Two native ReLU introductions and five
tableau steps precede four native PLC lemmas, including strictly-positive
output lower to auxiliary upper zero. `Imported_Marabou_Native_Relu_Chain`
proves UNSAT of the captured six-variable starting query.
The fourth lemma is checked even though a shorter proof could omit it.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_chain --output /tmp/marabou-output-bound-capture
isabelle build -d Isabelle -D /tmp/marabou-output-bound-capture
```

See [RELU_OUTPUT_BOUND_PROPAGATION.md](../../../../notes/RELU_OUTPUT_BOUND_PROPAGATION.md)
for the exact positivity guard, boundary counterexamples, native correspondence
and provenance limits. All seven older scenarios were rerun with the final
sources; their data bytes are unchanged and their provenance is refreshed.

`solver_relu_aux_inactive.json` is the eighteenth canonical accepted writer
certificate and ninth fully replayed native scenario. An actual proof-enabled
`Engine::solve` run on a five-variable source with an explicit ReLU auxiliary
emits one PLC lemma, strictly-positive auxiliary lower to output upper zero
(`aux=x0 >= 1/4` from row 0, then `f=x2 <= 0`), followed by a row contradiction.
The harness chooses aux as variable 0 so that its bound notification comes
first; no lemma or node is constructed by hand or filtered.
`_source.json`, `_steps.json`, `_query.json` and `.json` are the four replay
inputs, with `_run.json`, `.log` and `_provenance.json` companions.
`Imported_Marabou_Solver_Relu_Aux_Inactive` proves the processed query UNSAT;
`Imported_Marabou_Source_Relu_Aux_Inactive` proves the captured source UNSAT
through three checked tableau introductions. `ReLU_Aux_Lower_Bound_Examples`
proves the processed query's linear relaxation and a `w>=0` relaxation of the
source satisfiable.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_aux_inactive --output /tmp/marabou-aux-lower-capture
isabelle build -d Isabelle -D /tmp/marabou-aux-lower-capture
```

See [RELU_AUX_LOWER_BOUND_PROPAGATION.md](../../../../notes/RELU_AUX_LOWER_BOUND_PROPAGATION.md).
All eight older scenarios were rerun with the final sources; their data,
reports and logs are byte-identical, and only provenance hashes of the edited
harness, capture script, importer and rebuilt binary changed.

`solver_relu_sat_assignment.json` records the tenth native scenario, the first
with a SAT result. There is no certificate. The run starts with two plain
ReLUs, performs both native auxiliary introductions (7 → 9 variables) and five
tableau introductions (→ 14), and `Engine::solve` returns SAT.
`_before_relu.json`, `_relu_steps.json`, `_source.json`, `_steps.json`,
`_query.json` and `_assignment.json` are the six replay inputs; `_run.json`,
`.log` and `_provenance.json` describe the execution. Each assigned double is
stored as a round-trip decimal and an exact hexadecimal float.
`Imported_Marabou_Native_Relu_Sat` proves that their exact binary values are a
real model of the processed, source and before-ReLU queries.

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sat --output /tmp/marabou-sat-capture
isabelle build -d Isabelle -D /tmp/marabou-sat-capture
```

See [SAT_ASSIGNMENTS.md](../../../../notes/SAT_ASSIGNMENTS.md). All nine UNSAT
scenarios were rerun with the final sources; their data, reports and logs are
byte-identical and only provenance hashes of edited tools and the binary changed.

The ten `solver_<scenario>.mqx` files state each scenario's starting query in
the [exact text format](../../../../notes/EXACT_QUERY_FORMAT.md): the
before-ReLU query for `relu_intro`, `relu_sequence`, `relu_chain` and
`relu_sat`, and the source query otherwise. They were exported after the
fact from the JSON snapshots by `tools/exact_query_text.py`; the native runs
did not read them. `Imported_Marabou_Exact_Texts` checks each file against its
HOL byte list during the build and proves what it decodes to. Regenerate with:

```sh
python3 Isabelle/tools/exact_query_text.py --fixtures Isabelle/tests/fixtures/marabou \
  --theory Isabelle/Imported_Marabou_Exact_Texts.thy
```

`file_<example>_run.json`, `file_<example>.log` and
`file_<example>_provenance.json` record the final runs of the
[query-file workflow](../../../../notes/QUERY_FILE_WORKFLOW.md) on
`Isabelle/examples/relu_chain_unsat.mqx`, `relu_sat.mqx` and
`linear_unsat.mqx`: the native harness read each file itself. Their data
artifacts were byte-identical to the `solver_relu_chain`, `solver_relu_sat`
and `solver_linear` fixtures, so only these three companions are stored; the
provenance records the file's SHA-256 and each artifact hash.

The complete artifact sets `file_inequality_relu_unsat_*`,
`file_inequality_relu_sat_*` and `file_inequality_linear_sat_*` come from
query-file runs on the `le`/`ge` example files. The driver first wrote the
checked slack proposals (`_inequality_steps.json`) and the equality-only
`_prepared.mqx`, which the harness then read. These runs have no hard-coded
scenario counterpart. The generated `Imported_Marabou_Prepared_Inequality_*`
replay theories and `Imported_Marabou_Example_Inequality_*` theorem theories
are in the main session; see the
[inequality note](../../../../notes/INEQUALITY_AUXILIARY.md#finite-slack-caps-and-the-file-workflow).

The complete artifact sets `file_phase_active_unsat_*`,
`file_phase_inactive_unsat_*`, `file_phase_chain_unsat_*` and
`file_phase_fixed_sat_*` come from query-file runs where the initial bounds
fix a ReLU phase before search. Each includes the harness's
`_phase_fixing.json` record (`marabou-root-phase-fixing-v1`) of the fixed
ReLUs and their native valid splits. The importer justifies each phase exactly
and inserts `Relu_Fix_Active`/`Relu_Fix_Inactive` at the proof root; see
[RELU_PHASE_FIXING.md](../../../../notes/RELU_PHASE_FIXING.md). The generated
`Imported_Marabou_File_Phase_*` and `Imported_Marabou_Example_Phase_*`
theories are in the main session.

The complete artifact sets `file_preprocess_*` come from query-file runs with
`--preprocess`, which enables Marabou's own preprocessing. Each has a
`_preprocessing.json` record (`marabou-preprocessing-map-v1`) of the native
variable maps, or of an infeasibility found inside preprocessing. Where it
exists, `_source.json` is the preprocessed query from which the tableau steps
start. See [NATIVE_PREPROCESSING.md](../../../../notes/NATIVE_PREPROCESSING.md).
The generated `Imported_Marabou_Preprocessed_*` and
`Imported_Marabou_Example_Preprocess_*` theories are in the main session.

Every run that initializes a tableau also has an `_initial_basis.json` record
(`marabou-initial-basis-v1`). It holds the basic and nonbasic index orders
that `Engine::processInputQuery` chose, read from the tableau state before
solving. File examples that reproduce a scenario share that scenario's
record. [import_initial_basis.py](../../../tools/import_initial_basis.py)
turns the 20 distinct records into `Imported_Marabou_Initial_Bases`. There
HOL recomputes each basis from the run's source query and must match it
exactly; see [TABLEAU_INITIALIZATION.md](../../../../notes/TABLEAU_INITIALIZATION.md).

To refresh every native capture after a tool change, run from the project
root with a new tag:

```sh
python3 Isabelle/tools/refresh_native_fixtures.py --tag <new-tag>
```

It reruns all ten scenarios and every example file under
`Isabelle/generated/<new-tag>`. Each rerun must reproduce the saved data
artifacts byte for byte. It then copies the new run reports, logs and
provenance records. A data artifact with no saved counterpart is new and is
saved. A changed artifact is reported and refused unless
`--accept-data-changes` is given.
