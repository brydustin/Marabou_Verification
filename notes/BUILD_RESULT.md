# Build records

Date: 2026-09-22. Working directory:
`/home/dusty/Desktop/Marabou Verification`.

Version: `Isabelle2025-2`. Session: `Marabou_Verification`, parent `HOL`.
Project session option: `quick_and_dirty = false`.

The first milestone is recorded below, followed by the rational-checker and
recursive-checker/import milestones, then the ReLU propagation milestone and
their build/execution results.

The initial five-theory semantic checkpoint built successfully before the
splitting theory and examples were added. The complete seven-theory session
then built successfully. All intermediate proof errors were resolved without
admitting or aborting proofs.

## Clean rebuild of the final theories

Command:

```sh
isabelle build -c -D Isabelle
```

Exit status: **0**. Exact output:

```text
Cleaned Marabou_Verification
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:04 elapsed time, 0:00:05 cpu time, factor 1.23)
0:00:07 elapsed time, 0:00:05 cpu time, factor 0.72
```

## Final requested command

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

This invocation found the first milestone's session up to date following its
clean rebuild. The later rational-checker milestone extends that theory set.

## Additional checks

```sh
isabelle build_log -H 'Error|Warning' Marabou_Verification
```

Exit status: **0**, with no output. No build errors or warnings were reported.

A search of `Isabelle/` for `sorry`, `oops`, `axiomatization`, `axioms`, `admit`,
`skip_proof`, `cheat`, and `oracle` found no matches. Theories use ordinary HOL
definitions and completed proofs (`simp`, `auto`, induction, cases, `blast`,
and `linarith`), not a custom proof oracle. This source check supplements the
successful build; it is not a separate verification of Isabelle itself.

Both upstream working trees were clean after the work, and `git submodule
status` still reported the revisions recorded in the source audit. No upstream
C++ tests or solver executions were performed; this milestone's machine-checked
results are the HOL theorems listed in the README.

## Second milestone: rational linear-leaf checker

Date: 2026-09-22. Same Isabelle installation and session options.

Added `Rational_Linear_Constraints`, `Rational_Linear_Certificates`, and
`Rational_Linear_Examples`; the session now contains ten project theories.
The rational normalization checkpoint built first, followed by the checker and
soundness theorem, then the acceptance/rejection and ReLU-composition examples.

The final theory-changing build compiled the SML checker, checked all example
proofs, and exported its executable source:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:09 elapsed time, 0:00:15 cpu time, factor 1.60)
Exporting Marabou_Verification ...
0:00:13 elapsed time, 0:00:15 cpu time, factor 1.19
```

The exported file is `Isabelle/generated/Marabou_Linear_Leaf.ML`. Its public
interface was executed with:

```sh
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/linear_leaf_smoke.ML
```

Exit status: **0**. Exact output:

```text
8 exported SML checker tests passed
```

The final required command was then run:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
0:00:03 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'
Marabou_Verification` also exited **0** with no output. No theory or ROOT changes
were made after these checks.

The scan of all project `.thy` files again found no `sorry`, `oops`,
`axiomatization`, `axioms`, `admit`, `skip_proof`, `cheat`, or `oracle` tokens.
Acceptance/rejection examples use proof-producing `code_simp`; the exported
SML smoke tests are a separate execution check, not premises of the theorems.
All local documentation links and whitespace checks passed. Both upstream
working trees remain clean at the original pinned revisions.

## Third milestone: recursive certificates and native JSON import

Date: 2026-09-22. Same `Isabelle2025-2` installation, HOL parent, and
`quick_and_dirty = false`. The session now contains fifteen project theories.

Added `Rational_Proof_Trees`, `Rational_Proof_Tree_Examples`, and three generated
`Imported_Marabou_*` theories. The recursive soundness theorem and abstract
examples built first. The subsequent build replayed all three imported native
writer fixtures and compiled/exported both SML checkers:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:14 elapsed time, 0:00:25 cpu time, factor 1.79)
Exporting Marabou_Verification ...
0:00:18 elapsed time, 0:00:25 cpu time, factor 1.40
```

The fixture harness compiled unchanged upstream source components and generated
the native JSON files successfully:

```sh
python3 Isabelle/tests/build_marabou_fixtures.py Isabelle/tests/fixtures/marabou
```

Exit status: **0**. Output:

```text
Wrote three fixtures using upstream JsonWriter; evidence was hand constructed.
```

This is a partial C++ component build, not a solver build or an `Engine::solve`
run. The separate expected-query manifests were hand written. The adapter
generated the three project replay theories; each has a proof-producing
`code_simp` acceptance fact and a real-semantic UNSAT theorem. Python tests
confirm that these theories match regeneration, including both source hashes.

The standalone replay workflow was also exercised on the nested fixture:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/nested_query.json \
  --certificate Isabelle/tests/fixtures/marabou/nested.json \
  --output Isabelle/generated/import_replay/Imported_Check.thy --session
isabelle build -d Isabelle -D Isabelle/generated/import_replay
```

Both commands exited **0**. Exact build output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:16 elapsed time, 0:00:29 cpu time, factor 1.83)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:22 elapsed time, 0:00:32 cpu time, factor 1.43
```

The importer validation command passed **28 tests**, including malformed input,
query substitution, wrong phases, unproved auxiliary bounds, unsupported
lemmas, exact small margins, and reproducible theory generation:

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Both generated SML public interfaces were executed with the installed Poly/ML:

```sh
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/linear_leaf_smoke.ML
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/proof_tree_smoke.ML
```

Each exited **0**, reporting respectively:

```text
8 exported SML checker tests passed
5 exported SML proof-tree tests passed
```

The final required command was:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'
Marabou_Verification` exited **0** with no output. No project theories or ROOT
files changed after these checks; only documentation was completed.

A scan of project theories found no `sorry`, `oops`, `axiomatization`, `axioms`,
`admit`, `skip_proof`, `cheat`, or `oracle` tokens. Local links were checked in
all ten project Markdown files. Both upstream working trees are clean and
still pinned to the audited revisions. Git staging was left unchanged.

The precise import limitations and the remaining original-query/preprocessing
obligations are recorded in [CERTIFICATE_IMPORT.md](CERTIFICATE_IMPORT.md).

## Fourth milestone: ReLU upper-bound propagation and imported evidence

Date: 2026-09-22. Same `Isabelle2025-2` installation and HOL session options.
The project now has **21 theories**. Added `ReLU_Bound_Propagation`,
`ReLU_Bound_Examples`, and four `Imported_Marabou_Propagation*` theories.
`Rational_Proof_Trees` now includes `Relu_Upper` and a completed additional
induction case in `check_certificate_sound`.

The rule and extended soundness theorem compiled at the first successful
checkpoint. The build including all abstract examples and the four new imported
proofs was then run with code export:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:14 elapsed time, 0:00:33 cpu time, factor 2.31)
Exporting Marabou_Verification ...
0:00:17 elapsed time, 0:00:33 cpu time, factor 1.87
```

The C++ fixture generator was extended with hand-constructed `PLCLemma` objects
and run against the unchanged upstream writer:

```sh
python3 Isabelle/tests/build_marabou_fixtures.py Isabelle/tests/fixtures/marabou
```

Exit status: **0**. Exact output:

```text
Wrote seven fixtures using upstream JsonWriter; evidence was hand constructed.
```

The four new fixtures cover negative and positive input upper bounds, two
ordered propagation steps, and propagation in each branch of an independent
ReLU split. The earlier three fixtures still match their stored replay
theories. The new theories prove checker acceptance by `code_simp` and then
UNSAT over real valuations. The harness does not invoke the C++ bound-notification
callbacks, bound manager's lemma-recording method, or solver.

The standalone chain replay was also tested after completing the theory text:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/propagation_chain_query.json \
  --certificate Isabelle/tests/fixtures/marabou/propagation_chain.json \
  --output Isabelle/generated/propagation_replay/Imported_Propagation_Check.thy --session
isabelle build -d Isabelle -D Isabelle/generated/propagation_replay
```

Both commands exited **0**. Exact build output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:17 elapsed time, 0:00:37 cpu time, factor 2.14)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:01 elapsed time)
0:00:22 elapsed time, 0:00:39 cpu time, factor 1.71
```

The importer suite passed **45 tests** with:

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py' -v
```

The added cases test the exact native schema, stronger-by-`1/10^20` conclusions,
missing/reordered evidence, wrong ReLU pairs, removed ReLUs, sibling isolation,
and rejection of every nonempty explanation. Regeneration of all seven stored
import theories matches their stored text and hashes.

The exported tree-checker interface passed **13 execution tests**:

```sh
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/proof_tree_smoke.ML
```

Exit status: **0**. Exact output:

```text
13 exported SML proof-tree tests passed
```

The final required build was:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'
Marabou_Verification` exited **0** with no output. No theories or ROOT files
changed after these checks; only documentation was completed.

No project theory contains `sorry`, `oops`, `axiomatization`, `axioms`, `admit`,
`skip_proof`, `cheat`, or `oracle` tokens. Local links were checked across eleven
Markdown files. Both upstream working trees remain clean at their audited
revisions, and Git staging was left unchanged.

The assurance is the exact rule, preservation of real models, and its checked
composition with UNSAT certificates. It does not verify C++ propagation or
preprocessing. The supported `expl = []` evidence pattern and the next target
are described in [RELU_BOUND_PROPAGATION.md](RELU_BOUND_PROPAGATION.md).

## Fifth milestone: exact linear implications and nonempty explanations

Date: 2026-09-22. Same `Isabelle2025-2` installation and HOL session options.
The project now has **25 theories**. Added `Rational_Linear_Implication`,
`Rational_Linear_Implication_Examples`, `Imported_Marabou_Explained_Negative`,
and `Imported_Marabou_Explained_Positive`. The generic `rat_add_bound` helper
moved into `Rational_Linear_Constraints`. `Linear_Bound` extends the recursive
certificate with a completed soundness induction case.

The implication checker and tree theorem built successfully before adding
the examples/imported fixtures. The complete build and code export was:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:16 elapsed time, 0:00:43 cpu time, factor 2.58)
Exporting Marabou_Verification ...
0:00:20 elapsed time, 0:00:43 cpu time, factor 2.12
```

The native fixture generator was compiled and executed against unchanged
upstream components:

```sh
python3 Isabelle/tests/build_marabou_fixtures.py Isabelle/generated/explained_writer_fixtures
```

Exit status: **0**. Exact output:

```text
Wrote nine fixtures using upstream JsonWriter; two explanations were computed by BoundExplainer on hand-constructed rows. No Engine::solve run.
```

All seven earlier writer outputs matched their stored fixtures byte-for-byte.
The two new outputs were copied into `tests/fixtures/marabou`, paired with
separately written expected-query manifests, imported, and included in ROOT.
The harness calls `BoundExplainer::updateBoundExplanation/getExplanation` and
`UNSATCertificateUtils::computeBound` on supplied rows. It assembles the query,
PLC objects and terminal contradictions; it does not run solver search.

The fresh standalone replay was:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/explained_positive_query.json \
  --certificate Isabelle/tests/fixtures/marabou/explained_positive.json \
  --output Isabelle/generated/explanation_replay/Imported_Explanation_Check.thy --session
isabelle build -d Isabelle -D Isabelle/generated/explanation_replay
```

Both commands exited **0**. Exact build output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:20 elapsed time, 0:00:49 cpu time, factor 2.38)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:26 elapsed time, 0:00:51 cpu time, factor 1.91
```

The importer suite passed **57 tests**:

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py' -v
```

Coverage includes missing/corrupt explanations, exact-zero and tiny nonzero
weights, coefficient signs, original-row indexing under splits, malformed
indices and fields, sibling isolation, and keeping checked linear premises
separate from native ground-bound updates. All nine generated import theories
match regeneration, including their query/certificate hashes.

The exported recursive checker passed **23 execution tests**:

```sh
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/proof_tree_smoke.ML
```

Exit status: **0**. Exact output:

```text
23 exported SML proof-tree tests passed
```

The final required command was:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. Diagnostic checks with `isabelle build_log -H
'Error|Warning'` for both `Marabou_Verification` and `Marabou_Import_Replay`
exited **0** with no output. No theories or ROOT files changed after these
checks; only documentation was completed.

A scan of all 25 project theories found no `sorry`, `oops`, `axiomatization`,
`axioms`, `admit`, `skip_proof`, `cheat`, or `oracle` tokens. Local links were
checked in all twelve project Markdown files. Both upstream working trees are
clean, and Git staging was left unchanged.

The new assurance is entailment of accepted linear bounds in every real model,
preservation of those models when the bound is added, and sound recursive use
of the bound before ReLU propagation. The exact import contract and remaining
solver/preprocessing obligations are in
[RATIONAL_LINEAR_IMPLICATION.md](RATIONAL_LINEAR_IMPLICATION.md).

## Sixth milestone: actual native solver capture and HOL replay

Date: 2026-09-22. Same `Isabelle2025-2` installation and HOL session options.
The session now has **26 theories**, including
`Imported_Marabou_Solver_Linear`. No kernel definition or soundness theorem
needed modification: the solver emitted an already supported linear leaf.

Added an external C++ engine embedding and CMake build, the
`capture_marabou_solver.py` driver, and five saved `solver_linear*` artifacts.
The engine and its real factories compile directly from the unchanged pinned
checkout. No proof nodes, PLC lemmas, or contradictions are created by the
capture harness. The compiler was GCC 13.3.0 with CMake 3.28.3, Boost 1.83, and
GMP; the local dependency setup is documented in
[SOLVER_CAPTURE.md](SOLVER_CAPTURE.md).

The final reproducible capture command was:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --output Isabelle/generated/solver_capture_replay
```

Exit status: **0**. The captured engine output was:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 3; rows: 1
Main-loop iterations: 2; simplex steps: 0
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
```

The printed iteration value is the native `NUM_MAIN_LOOP_ITERATIONS` counter;
`mainLoopStatistics` increments it before entering the loop too.
The saved report additionally records one explicit-basis-tightening call,
one explained leaf, zero delegated leaves, and zero ReLU constraints.
The harness checks that initialization succeeds, that `solve` returns UNSAT,
and that the certificate is a visited, closed, nondelegated linear leaf.
The separately written initial query agrees exactly with the saved native
tableau and initial ground bounds in runtime comparisons.

The raw query and proof match across the capture runs and were saved unchanged
under `Isabelle/tests/fixtures/marabou`. Provenance records the pinned revision,
120 compiled-source hashes, compiler command/version, linked-library hashes,
binary hash, and artifact hashes. These records describe the execution; they
are not proof premises.

The main session build including the new replay theorem was:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:17 elapsed time, 0:00:43 cpu time, factor 2.56)
0:00:20 elapsed time, 0:00:43 cpu time, factor 2.12
```

The standalone session emitted by the final capture driver was also built:

```sh
isabelle build -d Isabelle -D Isabelle/generated/solver_capture_replay
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:21 elapsed time, 0:00:51 cpu time, factor 2.43)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:01 elapsed time)
0:00:26 elapsed time, 0:00:52 cpu time, factor 1.97
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py' -v` passed
**61 tests**, including artifact/source provenance consistency, native run
metadata, corrupting the captured row weight, and relaxing the auxiliary
bound to make the captured query satisfiable. All ten imported theories
match regeneration. The mathematical kernel and exported SML code are
unchanged; the earlier 23 SML execution tests were not repeated for this
data/import integration milestone.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'` for both
`Marabou_Verification` and `Marabou_Import_Replay` exited **0** with no output.
No theories or ROOT files changed after these checks; only documentation was
completed.

All 26 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links resolve in all thirteen Markdown files.
Both upstream working trees are clean, and Git staging was left unchanged.

The new result is an unconditional HOL UNSAT theorem for the captured processed
query, derived from an actual solver-produced certificate. There is no verified
query extractor, JSON decoder, general original-query correspondence, or C++
correctness theorem. No ReLU inference or simplex pivot was exercised in this
linear execution.

## Seventh milestone: solver-produced ReLU propagation and exact replay

Date: 2026-09-22. Same `Isabelle2025-2` installation, HOL parent, and
`quick_and_dirty = false`. The session now has **28 theories**, adding
`Imported_Marabou_Solver_Relu` and `Solver_ReLU_Examples`.
The mathematical checker, its soundness theorem, and the JSON adapter are
unchanged. The capture harness now supports `--scenario relu` as well as
the existing default linear case.

The final reproducible ReLU capture command was:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output Isabelle/generated/solver_relu_capture
```

Exit status: **0**. Captured engine output:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 8; rows: 3
PLC lemmas: 0 before solve; 1 after solve
Main-loop iterations: 2; simplex steps: 0
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
```

The report also records an unfixed ReLU phase before solving, one explicit-basis
tightening call, one explained leaf, no delegation, and no root children.
The harness supplies the query but never creates or filters proof nodes,
PLC lemmas, or contradictions. Its full solver-produced evidence contains a
ReLU upper-propagation lemma with explanation weight `-1` on original row 0,
followed by a contradiction with weight `1` on original row 2.
The query and proof matched a previous successful execution byte-for-byte.

Five `solver_relu*` artifacts are saved beside the earlier fixtures. The
linear scenario was rerun with the final shared harness using:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario linear --output Isabelle/generated/solver_linear_refresh
```

That command also exited **0**. Its query and proof are byte-for-byte identical
to the earlier capture; its report/log/provenance were refreshed from this
actual new execution. Both provenance records bind the final harness and
driver source hashes. The source revision remains
`1c2f4788c32e2f4e407c356b763a8025c5578722`.

The main session build, including imported certificate acceptance, UNSAT,
the linear-relaxation witness, and impossibility of a linear leaf alone, was:

```sh
isabelle build -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:17 elapsed time, 0:00:46 cpu time, factor 2.62)
0:00:21 elapsed time, 0:00:46 cpu time, factor 2.13
```

The standalone replay emitted by the final capture driver was built with:

```sh
isabelle build -d Isabelle -D Isabelle/generated/solver_relu_capture
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:21 elapsed time, 0:00:53 cpu time, factor 2.50)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:27 elapsed time, 0:00:55 cpu time, factor 2.01
```

The importer command:

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py' -v
```

exited **0**, with **68 tests passed**. Coverage includes both captures'
provenance, all eleven generated import theories, missing or corrupted ReLU
explanations, a conclusion too strong by `1/10^20`, a corrupt terminal
contradiction, and a relaxed satisfiable query. The kernel and exported SML
definitions are unchanged; the earlier 23 exported tree-checker execution
tests were not repeated for this integration milestone.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:03 elapsed time
```

The session was up to date. Diagnostic commands `isabelle build_log -H
'Error|Warning'` for `Marabou_Verification` and `Marabou_Import_Replay` both
exited **0** with no output. No theories or ROOT files changed after these
checks; only documentation was completed.

All 28 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links resolve in all fourteen Markdown files. Both
upstream working trees are clean at the audited revisions, and Git staging
was left unchanged.

The new theorem excludes every real model of the explicit captured processed
query, using nonlinear evidence produced during a solver execution. Its
linear relaxation has a proved real model, so no linear leaf alone suffices.
Broader exploratory inputs emitted a currently unsupported auxiliary-bound
lemma; those imports were rejected, and no evidence was silently discarded.
No incorrect solver result or soundness failure was observed.
The capture, decoder, original-query correspondence, and C++ implementation
remain unverified. Full source correspondence and the next small target are
in [SOLVER_RELU_CAPTURE.md](SOLVER_RELU_CAPTURE.md).

## Eighth milestone: auxiliary-upper rule and solver evidence

Date: 2026-09-22. Same `Isabelle2025-2` installation, HOL parent, and
`quick_and_dirty = false`. The session now has **32 theories**, adding
`ReLU_Aux_Bound_Propagation`, `ReLU_Aux_Bound_Examples`,
`Imported_Marabou_Solver_Relu_Aux`, and
`Imported_Marabou_Solver_Relu_Aux_Active`.

The new rule proves `aux≤max(0,-l)` from `b≥l`, `f=ReLU(b)`, and an
auxiliary equation established by two exact linear implications. Its soundness
and model-preservation theorems, and the new `Relu_Aux_Upper` case of
`check_certificate_sound`, built before the new capture theories were added.
No premise is imported solely from auxiliary-variable metadata.

The two actual capture commands were:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux --output Isabelle/generated/solver_aux_capture
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux_active --output Isabelle/generated/solver_aux_active_capture
```

Both exited **0**. The broader negative variant's engine output was:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 8; rows: 3
PLC lemmas: 0 before solve; 2 after solve
Main-loop iterations: 2; simplex steps: 0
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
```

The active variant reported the same dimensions/outcome and
`PLC lemmas: 0 before solve; 1 after solve`. Each has one explained,
nondelegated leaf and an unfixed ReLU before solving. The negative variant's
query and native proof match the earlier rejected exploratory capture
byte-for-byte. No evidence was constructed or filtered by the capture harness.

The earlier `linear` and `relu` scenarios were rerun with the final shared
harness into `Isabelle/generated/aux_milestone_linear_refresh` and
`Isabelle/generated/aux_milestone_relu_refresh`. Both exited **0**; their
query/proof bytes are unchanged. Saved report/log/provenance were refreshed
from these actual executions. All four provenance records now include the
adapter hash as well as capture source, build inputs, binary, libraries, and
artifact hashes.

The complete theory build and code export was:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:20 elapsed time, 0:00:59 cpu time, factor 2.84)
Exporting Marabou_Verification ...
0:00:24 elapsed time, 0:00:59 cpu time, factor 2.44
```

This includes the two new imported UNSAT theorems, negative/zero/positive rule
examples, rejection computations, and a real model of the active capture's
linear relaxation. The latter proves that no linear leaf alone can certify
that root.

Both standalone driver outputs were built. First:

```sh
isabelle build -d Isabelle -D Isabelle/generated/solver_aux_capture
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:22 elapsed time, 0:01:00 cpu time, factor 2.63)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:29 elapsed time, 0:01:03 cpu time, factor 2.14
```

Then:

```sh
isabelle build -d Isabelle -D Isabelle/generated/solver_aux_active_capture
```

Exit status: **0**. Exact output:

```text
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:06 elapsed time
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py' -v` exited
**0** with **86 tests passed**. Tests include all thirteen theory-regeneration
checks, four captures' provenance, absent auxiliary equations or either zero
slack bound, lower-explanation signs, tiny coefficients, overstrong conclusions,
native ground updates, independent branches, and altered satisfiable queries.

The exported recursive checker was executed with:

```sh
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly --script Isabelle/tests/proof_tree_smoke.ML
```

Exit status: **0**. Exact output:

```text
35 exported SML proof-tree tests passed
```

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'` for both
`Marabou_Verification` and `Marabou_Import_Replay` exited **0** with no output.
No theories or ROOT files changed after these checks; only documentation was
completed.

All 32 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links resolve in all fifteen Markdown files.
Both upstream working trees remain clean at the audited revisions.
Git staging was left unchanged.

The new assurance is exact auxiliary-bound soundness and its recursive use,
plus unconditional real-semantic UNSAT for the two explicit processed queries.
The negative certificate's non-dyadic `1.750002` is accepted as an exact
rational weaker conclusion than `7/4`, without trusting binary rounding.
The new active capture uses its auxiliary lemma as the sole nonlinear step.
The C++ implementation, decoder, preprocessing, auxiliary introduction, and
original-query correspondence remain unverified. Source correspondence and
remaining scope are in [RELU_AUX_BOUND_PROPAGATION.md](RELU_AUX_BOUND_PROPAGATION.md).
