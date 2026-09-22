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
The component generator does not overwrite any of these four solver captures.
