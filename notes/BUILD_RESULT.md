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

## Ninth milestone: solver-produced binary ReLU split and both children

Isabelle version: `Isabelle2025-2`. The session now has **34 theories**,
including `Imported_Marabou_Solver_Relu_Split` and
`Solver_ReLU_Split_Examples`. No logical checker, certificate datatype,
soundness proof, importer rule, or exported-checker definition changed.
The shared capture harness gained a `relu_split` scenario and native-tree
guards; its driver requires the reconstructed result to have two linear children.

### Actual solver capture

Command from the project root:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_split --output Isabelle/generated/solver_split_capture
```

Exit status: **0**. Native run output:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 14; rows: 5
PLC lemmas: 0 before solve; 0 after solve
Main-loop iterations: 12; simplex steps: 9
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
Binary ReLU split: one active and one inactive child, both closed.
Search splits: 1; tableau pivots: 3; explained leaves: 2
```

The report also records violation threshold 1, two search pops, maximum depth
one, and no delegated leaves. The harness supplies the query and search
options; the unchanged native engine creates the split, both children, and
both contradictions. No proof evidence is inserted or filtered by the harness.
The unchanged native writer emits the complete certificate.

Saved artifacts are `solver_relu_split{_query.json,.json,_run.json,.log,_provenance.json}`
under `Isabelle/tests/fixtures/marabou/`. They were copied from this execution,
then the checked-in theory was emitted by `import_marabou_json.py`.
Both child combinations have exact positive margin **1/2**.
All four older scenarios were also executed again with the final shared
capture sources. Their saved query/proof bytes were asserted identical before
refreshing the run reports and provenance from those real executions.
The prior solver logs also remained unchanged.

### HOL replay

The first main-session checkpoint, including both new theories, used
`isabelle build -D Isabelle` and exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:20 elapsed time, 0:00:58 cpu time, factor 2.89)
0:00:23 elapsed time, 0:00:58 cpu time, factor 2.48
```

The fresh standalone capture replay then ran:

```sh
isabelle build -d Isabelle -D Isabelle/generated/solver_split_capture
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:24 elapsed time, 0:01:08 cpu time, factor 2.79)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time)
0:00:31 elapsed time, 0:01:11 cpu time, factor 2.29
```

The imported theory proves `imported_certificate_checked` using `code_simp`
and derives `imported_query_unsatisfiable` from `check_certificate_sound`.
The examples theory separately proves `captured_active_child_checked`,
`captured_inactive_child_checked`, and both child UNSAT theorems.
It also supplies a real model of the root's linear relaxation and proves
`captured_split_requires_nonlinear_evidence`.

### Tests and final checks

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **96 tests passed** (0.625 seconds). These include fourteen
theory-regeneration checks, all five capture provenance checks, independently
corrupting either leaf, omitted children, duplicated phases, swapped
contradictions, stronger phase assumptions, reversed child order, and loss
of the active phase's tableau premise. Relaxing either branch's positive
offsets gives an explicitly checked exact model and rejects the old certificate.
The earlier 35 exported SML tests were not repeated because the checker and
its export definitions did not change; the changed HOL data was replayed.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. The following exited **0** with no output:

```sh
isabelle build_log -H 'Error|Warning' Marabou_Verification Marabou_Import_Replay
git diff --check
```

All 34 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links were checked in all sixteen project Markdown
files. Both upstream working trees remain clean. Git staging was not changed.
Only documentation was edited after the final build.

The assurance is unconditional real-semantic UNSAT of the explicit processed
parent and both canonical children, backed by actual solver-produced evidence.
It does not verify the native search, pivoting, decoder, preprocessing, or
original-query correspondence. See
[SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md) for the exact
query, source correspondence, and next target: one verified scalar-fixed
tableau auxiliary introduction.

## Tenth milestone: one verified scalar-fixed tableau auxiliary

Isabelle version: `Isabelle2025-2`. The main session has **37 theories**,
with `quick_and_dirty = false`. Added:

* `Tableau_Auxiliary.thy`: variable support, one indexed equation replacement,
  real model extension/projection, and SAT/UNSAT equivalence under freshness.
* `Rational_Tableau_Auxiliary.thy`: checked index/type/freshness, a proved
  embedding of the executable transformation, and `check_after_fixed_aux_sound`.
* `Tableau_Auxiliary_Examples.thy`: exact connection to the earlier linear
  capture, a source-query UNSAT theorem, affine/negative/zero scalar examples,
  and rejected invalid selections or variable reuse.

No existing certificate constructor, recursive checker definition, importer,
capture program, or evidence fixture changed in this milestone. No new solver
run was performed or claimed. The additional wrapper constructs a query using
one checked transformation and then invokes the existing checker.

The source inspection covered `src/engine/Engine.cpp::addAuxiliaryVariables`,
`createConstraintMatrix`, and the native initialization call path;
`src/engine/Query.cpp::setLowerBound/setUpperBound`; and the `Equation` addend
and scalar representation. Both upstream repositories remain unchanged at
the previously audited revisions.

### Proofs and examples

The real-theory checkpoint built successfully before the rational layer was
added. The rational layer also built, including Standard ML compilation with
`export_code rat_introduce_fixed_aux check_after_fixed_aux checking SML`.
The complete build including the examples used `isabelle build -D Isabelle`
and exited **0** with exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:22 elapsed time, 0:01:09 cpu time, factor 3.11)
0:00:25 elapsed time, 0:01:09 cpu time, factor 2.69
```

`fixed_aux_model_extension` assigns the fresh variable to the selected scalar.
`fixed_aux_model_projection` allows any value for that variable in the original
query. `satisfiable_introduce_fixed_aux_iff` and its UNSAT corollary prove
preservation. The full model-set theorem explicitly includes the additional
condition `v s=b`; no incorrect full valuation-set equality is asserted.
All freshness and selection premises of the rational wrapper are executable
checks, rather than caller-supplied logical assumptions.

Eleven new `code_simp` computations check concrete transformations, rejection
cases, and certificate acceptance. Other example proofs give explicit real
models and derive UNSAT from the soundness theorems. In particular:

* `solver_linear_aux_matches_snapshot` proves that one checked introduction
  from the explicit two-variable source query gives the entire existing
  `Imported_Marabou_Solver_Linear.imported_query` record.
* `solver_linear_before_aux_unsatisfiable` reuses that capture's native
  certificate to prove the source query UNSAT.
* A separate satisfiable source becomes UNSAT under an unguarded variable
  collision. The checked interface rejects that step, even with a valid
  certificate of its inconsistent result. This is a designed negative
  control, not a reported solver failure.

### Regression and final checks

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **96 tests passed** (0.654 seconds). All fourteen generated
import theories and all five saved solver-capture provenance records still
match. The unchanged standalone leaf/tree SML smoke tests were not repeated;
the new interface's SML compilation and its concrete HOL computations were
checked by the main build.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. `git diff --check` also exited **0** with no output.
All 37 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links were checked in all seventeen project Markdown
files. Both upstream working trees remain clean and Git staging was unchanged.
Only documentation was edited after the final build.

The new assurance covers one exact transformation over real semantics and
UNSAT of an explicit pre-auxiliary query through existing solver evidence.
The source query is hand-written HOL data; no C++ decoder, native-loop
refinement, or general preprocessing theorem is claimed. The precise contract,
source map, and next target—composition of finitely many checked steps—are in
[TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md).

## Eleventh milestone: finite checked auxiliary sequences

Isabelle version: `Isabelle2025-2`. The main session now has **39 theories**.
Added `Tableau_Auxiliary_Sequence.thy` and
`Tableau_Auxiliary_Sequence_Examples.thy`; the existing single-step function,
certificate datatype, recursive checker, importer, capture program, and saved
evidence were unchanged in this milestone.

The new sequence function processes a finite list of equation-index/fresh-variable
pairs. It checks each pair against the preceding query, constructs the next
query using the verified single step, and returns `None` after any failed step.
The empty list is the identity. The concatenation and failed-prefix laws are
proved; singleton functions agree with the previous interfaces.

Induction proves `fixed_aux_sequence_satisfiable_iff`, with the UNSAT
equivalence as a corollary. `check_after_fixed_aux_sequence_sound` combines
this preservation with the existing terminal certificate theorem to prove
UNSAT of the source query. A source model excludes every accepted
sequence/certificate pair.

### Compiling checkpoints and application

The composition theory built successfully before the concrete examples were
added. It includes Standard ML compilation of both new executable functions.
That checkpoint exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:22 elapsed time, 0:01:12 cpu time, factor 3.17)
0:00:26 elapsed time, 0:01:12 cpu time, factor 2.74
```

The complete build, including the five-step connection to the existing
binary-split capture, also exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:24 elapsed time, 0:01:17 cpu time, factor 3.18)
0:00:27 elapsed time, 0:01:17 cpu time, factor 2.78
```

`solver_split_sequence_matches_snapshot` computes the full query-record
equality after `[(0,9),(1,10),(2,11),(3,12),(4,13)]`. The result is exactly the
earlier fourteen-variable imported query. A separate pointwise semantic
theorem justifies reordering `f-b-a` to the snapshot's `-b+f-a`.
`solver_split_before_aux_checked` replays the existing native binary-split
certificate after the five introductions. `solver_split_before_aux_unsatisfiable`
proves UNSAT of the explicitly described nine-variable source query in its
original term order.

The source and step list are hand-written HOL definitions. No new solver
run, native transformation log, or verified input decoder is claimed.
Source inspection reconfirmed
`upstream/Marabou/src/engine/Engine.cpp::addAuxiliaryVariables` and
`src/proofs/JsonWriter.cpp::writeProofToJson/writeInitialTableau`, plus the
input construction and `snapshot` function in the local capture harness.

### Regression and final checks

Six new `code_simp` computations cover the exact five-step result, terminal
acceptance, invalid later indices, collisions with earlier auxiliaries or
original variables, empty/partial sequences with the saved certificate,
corruption of either child, and repeated processing of an equation with
distinct fresh variables. The latter verifies that the second step reads the
current scalar zero, not the original `3/4`. Explicit real models and the
general model-rejection theorem cover this satisfiable example.

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **96 tests passed** (0.694 seconds). All fourteen generated
import theories and five saved solver-capture provenance records still match.
The unchanged standalone SML smoke tests were not repeated; compilation of
the new functions and the concrete HOL computations passed in the main build.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. `git diff --check` also exited **0** with no output.
All 39 project theories were scanned for admitted-proof/added-axiom tokens,
with none found. Local links were checked in all eighteen project Markdown
files. Both upstream repositories remain clean. Git staging was unchanged;
only documentation was edited after the final build.

This verifies mathematical finite composition and its use with an existing
native proof. It does not verify the C++ initialization loop or the origin of
the hand-written source/step data. The next small target is capture/import of
that data alongside the processed snapshot and proof from one tiny run.
See [TABLEAU_AUXILIARY_SEQUENCE.md](TABLEAU_AUXILIARY_SEQUENCE.md) for the
interface, source correspondence, and precise assurance.

## Twelfth milestone: captured source queries and introduction lists

Isabelle version: `Isabelle2025-2`. The main session has **44 theories**.
Added five generated `Imported_Marabou_Source_*` theories, the strict
`tools/import_marabou_source.py` adapter, and 26 source-import tests.
The external capture harness and driver now save and import source queries
and proposed introduction lists. The logical checkers, generic soundness
theorems, and original proof adapter are unchanged.

### Actual captures

All five scenarios were executed with the final capture sources:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario linear --output Isabelle/generated/source_capture_linear_v3
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output Isabelle/generated/source_capture_relu_v3
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux --output Isabelle/generated/source_capture_relu_aux_v3
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux_active --output Isabelle/generated/source_capture_relu_aux_active_v3
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_split --output Isabelle/generated/source_capture_relu_split_v3
```

Every command exited **0**. Each initialization succeeded, native `solve`
returned UNSAT, and the complete unmodified native proof was retained.
The source was saved before initialization via an `InputQuery::generateQuery`
copy; the proposed list was recovered from added columns before solving.
There are respectively **1, 3, 3, 3, and 5 introductions**.
The split execution again reported one split, two closed children, twelve
main-loop iterations, nine simplex steps, three tableau pivots, and zero
delegated leaves.

Before updating saved artifacts, a byte comparison asserted that each
processed-query/proof pair was identical to its earlier fixture. The new
`_source.json` and `_steps.json` files, refreshed reports/logs, and provenance
were copied from these executions. Provenance includes both new artifact
hashes and the new adapter hash; no execution record was synthesized.
The original fourteen processed-query replay theories remain unchanged.

### HOL replay

The first split source replay built before adding all five theories to the
main session. The complete main-session checkpoint then ran
`isabelle build -D Isabelle` and exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:26 elapsed time, 0:01:29 cpu time, factor 3.34)
0:00:30 elapsed time, 0:01:29 cpu time, factor 2.95
```

The standalone replay emitted by the final split capture was also checked:

```sh
isabelle build -d Isabelle -D Isabelle/generated/source_capture_relu_split_v3
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:28 elapsed time, 0:01:30 cpu time, factor 3.14)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time, 0:00:03 cpu time)
0:00:35 elapsed time, 0:01:34 cpu time, factor 2.63
```

Every generated source theory proves pointwise term-order equivalence,
complete processed-query equality after the checked sequence, certificate
acceptance, source/processed equisatisfiability, and unconditional
source-query UNSAT over real valuations. In particular,
`Imported_Marabou_Source_Relu_Split.imported_source_query_unsatisfiable`
now uses imported source/step data and the native binary proof. The source's
four scalars `1/4` and final scalar zero are retained.

### Regression and audit

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **122 tests passed** (0.910 seconds). The new tests cover
source/scalar/bound substitution, missing and extra steps, collisions with
original or earlier variables, incorrect late row selections, independent
query and proof-header mismatch, corruption of either child, malformed
source schemas, exact numeric restrictions, and safe output handling.
A relaxed satisfiable source and corresponding processed query pass the
introduction bridge but reject the old certificate. All nineteen generated
theories match regeneration, and all five refreshed provenance records match
the saved outputs and current build sources.

The unchanged standalone SML smoke tests were not repeated. Existing SML
compilation checks and all new proof-producing HOL computations passed in
the main session. No admitted-proof/added-axiom tokens occur in the 44 project
theories. Both upstream repositories remain clean, and Git staging is unchanged.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:02 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'
Marabou_Verification Marabou_Import_Replay` and `git diff --check` exited **0**
with no output. All 234 local links resolve in the nineteen project Markdown
files. Only this build record was completed after the final build.

The new guarantee reaches the explicit captured source queries through
checked mathematical introductions and native proof replay. The list is a
harness proposal, not a verified record of the native initialization loop.
C++ extraction, JSON decoding, floating-point serialization in general,
original network files, and general preprocessing remain outside the theorem.
See [SOURCE_QUERY_CAPTURE.md](SOURCE_QUERY_CAPTURE.md) for schemas, source
correspondence, and the next target: one fresh ReLU auxiliary introduction.

## Thirteenth milestone: one verified fresh ReLU auxiliary

Isabelle version: `Isabelle2025-2`. The main session has **47 theories**.
Added `ReLU_Auxiliary.thy`, `Rational_ReLU_Auxiliary.thy`, and
`ReLU_Auxiliary_Examples.thy`. No existing checker definition, certificate
constructor, importer, capture source, or saved evidence changed.
No new native transformation or solver execution is claimed.

### Transformation and source audit

The operation retains a present `ReLU x y`, introduces a globally fresh `a`,
and appends `y-x-a=0` and `a≥0`. A selected explicit lower bound `l≤x` also
justifies `a≤max(0,-l)`. With `None`, no finite auxiliary upper bound is added.
Every premise is checked by `rat_introduce_relu_aux`, which constructs the
result rather than accepting a supplied query.

Source inspection covered `ReluConstraint.cpp::transformToUseAuxVariables`,
`PiecewiseLinearConstraint.h::existsLowerBound/getLowerBound`,
`Preprocessor.cpp::preprocess/informConstraintsOfInitialBounds/transformConstraintsIfNeeded`,
and `Query.cpp::addEquation/setLowerBound/setUpperBound`.
The native cached-bound access, variable-count allocation, infinity handling,
and `_auxVarInUse` no-op branch are distinguished from our exact mathematical
operation in [RELU_AUXILIARY.md](RELU_AUXILIARY.md).

The proofs characterize the full result model set, extend a model with
`a=y-x=ReLU(-x)`, project by forgetting that coordinate, and establish
SAT/UNSAT equivalence. The rational embedding theorem includes the optional
cap. `check_after_relu_aux_sound` composes this step with the existing
scalar-fixed tableau sequence and recursive certificate soundness.
An explicit source model rules out every accepted combined check.

### Compiling checkpoints and application

The real-theory checkpoint used `isabelle build -D Isabelle` and exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:25 elapsed time, 0:01:26 cpu time, factor 3.33)
0:00:29 elapsed time, 0:01:26 cpu time, factor 2.92
```

The rational layer, including Standard ML compilation of
`rat_introduce_relu_aux` and `check_after_relu_aux`, then built with exit **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:27 elapsed time, 0:01:30 cpu time, factor 3.33)
0:00:30 elapsed time, 0:01:30 cpu time, factor 2.93
```

The complete build including all examples also exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:28 elapsed time, 0:01:40 cpu time, factor 3.53)
0:00:31 elapsed time, 0:01:40 cpu time, factor 3.15
```

`solver_relu_aux_matches_captured_source` computes equality between the
new step's result and the entire existing `relu_aux` source snapshot.
`solver_before_relu_aux_checked` applies one ReLU introduction, the saved
three scalar-fixed introductions, and the existing native proof.
`solver_before_relu_aux_unsatisfiable` proves the earlier four-variable HOL
source UNSAT. That earlier source is hand-written; the actual saved native
run began with its ReLU auxiliary already present.

Fifteen new proof-producing `code_simp` computations check complete
transformations and certificate acceptance/rejection. They cover negative,
zero, positive, and absent finite lower bounds; input/output aliasing;
all-component freshness, including zero coefficients; auxiliary reuse;
missing or misidentified premises; incomplete tableau steps; and bad
terminal evidence. Real-model proofs establish satisfiable examples and
show that an old value of the new coordinate may need changing.

Two designed negative controls give valid linear UNSAT certificates for
raw transformations that omit freshness or ReLU membership, while their
sources have explicit real models. The guarded interface rejects these
attempted lifts. These are counterexamples to weakened mathematical rules,
not observed Marabou failures.

### Regression and audit

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **122 tests passed** (0.860 seconds).
All nineteen generated import theories and all five capture provenance
records still match. The unchanged standalone SML smoke tests were not
repeated; the new interface's SML compilation and HOL computations passed
in the main build.

No admitted-proof or added-axiom tokens occur in the 47 project theories.
Both upstream repositories remain clean at the audited revisions.
Git staging is unchanged.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**. Exact output:

```text
0:00:03 elapsed time
```

The session was up to date. `isabelle build_log -H 'Error|Warning'
Marabou_Verification` and `git diff --check` exited **0** with no output.
All 253 local links resolve in the twenty project Markdown files.
Only this build record was completed after the final build.

The new assurance is exact ReLU auxiliary extension over real semantics,
its checked rational implementation, and sound composition with existing
native evidence. C++ execution, native cached-bound/allocation invariants,
decoding, and general preprocessing remain unverified. The next small
integration target is capture/import of one actual native ReLU introduction
from a query that does not already supply its auxiliary.

## Fourteenth milestone: captured native ReLU introduction and full replay

Date: 2026-09-22. Isabelle version: `Isabelle2025-2`.
The main session now has **48 theories**, including
`Imported_Marabou_Native_Relu_Intro`. The logical checker and its soundness
theorems are unchanged; the new replay applies the existing guarded ReLU
introduction, scalar-fixed sequence and recursive certificate checker.

### Native call, artifacts and import

Command:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_intro --output Isabelle/generated/native_relu_intro_capture
```

Exit status: **0**. The actual capture reports:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 8; rows: 3
PLC lemmas: 0 before solve; 2 after solve
Main-loop iterations: 2; simplex steps: 0
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
Captured pre-initialization source query and 3 proposed scalar-fixed introductions.
Native ReluConstraint::transformToUseAuxVariables: one call; 4 -> 5 variables.
Captured queries before and after the native ReLU introduction.
```

The native method created the row `f-b-a=0` and bounds `0<=a<=2`.
The harness called `Preprocessor::informConstraintsOfInitialBounds` first;
it did not enable the full preprocessing pipeline. The independent
before-query was saved before those notifications. Both the native call and
the solver execution use the unmodified pinned Marabou sources.

Six data artifacts plus report, log and provenance are saved under
`Isabelle/tests/fixtures/marabou/solver_relu_intro*`. The new strict
`import_marabou_relu_intro.py` checks the whole independently supplied
after-query, then reuses source/step and proof reconstruction. It emits
theorems for exact introduction equality, before/after and before/processed
equisatisfiability, combined checker acceptance, and before-query UNSAT.
All computational proof obligations use proof-producing `code_simp`.

The same final capture harness was used to execute all five older scenarios
again, into `Isabelle/generated/native_relu_refresh_<scenario>`. Each exited
**0**. Their source, step, processed-query and proof bytes remained unchanged;
their saved logs/reports/provenance now describe these new runs. The new
`relu_intro` after-source, steps, processed query and proof also happen to
match the older `relu_aux` bytes exactly. The additional assurance is the
captured native introduction and its checked connection to the before-query,
not a claim of distinct proof contents.

There are fifteen saved writer proof files, six actual solver scenarios, and
twenty generated import theories.

### Isabelle replay checkpoints

First, the standalone generated capture replay:

```sh
isabelle build -d Isabelle -D Isabelle/generated/native_relu_intro_capture
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:33 elapsed time, 0:01:50 cpu time, factor 3.32)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:03 elapsed time, 0:00:05 cpu time, factor 1.72)
0:00:41 elapsed time, 0:01:56 cpu time, factor 2.84
```

After adding the fixture-generated theory to the main ROOT,
`isabelle build -D Isabelle` exited **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:30 elapsed time, 0:01:47 cpu time, factor 3.57)
0:00:34 elapsed time, 0:01:47 cpu time, factor 3.17
```

In particular,
`Imported_Marabou_Native_Relu_Intro.imported_before_relu_query_unsatisfiable`
proves there is no real model of the explicit four-variable query captured
before introduction, by `check_after_relu_aux_sound`. No native status flag,
freshness assertion, or lower-bound claim is assumed as a theorem premise.

### Tests and final audit

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **146 tests passed** (0.978 seconds). The 24 new tests
cover six-artifact binding/regeneration, native-run provenance, missing and
misidentified ReLUs, occupied auxiliaries, invalid finite premises, unsupported
schemas/types, altered before/after atoms and caps, incorrect subsequent
steps, substituted processed/proof headers, corrupt PLC/leaf evidence,
overwrite guards and generated-text injection guards.

A coherent relaxation of before/after/processed queries has an explicit
rational model. Its old proof is rejected because its first PLC conclusion is
too strong under the relaxed premise. This is a deliberate negative control,
not an observed solver failure. All twenty generated theories regenerate
byte-for-byte; all six capture provenance checks pass.

The final required command was `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:02 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. No admitted-proof or added-axiom tokens occur in the 48 project
theories. All 277 local links in the 22 project Markdown files resolve,
including the existing UAT source links. Whitespace checks and
`git diff --check` passed. Both upstream repositories remain clean at the
audited revisions, and Git staging remains empty. Only this build record
was completed after the final build. The unchanged standalone SML smoke
tests were not repeated; the main session still checks code compilation.

[ACTIVATION_REUSE.md](ACTIVATION_REUSE.md) records the existing polymorphic
UAT sigmoid definition and the exact inspected working-copy fingerprint.
UAT was neither modified nor rebuilt, and no new sigmoid definition or
session dependency was added here.

The new assurance is native-introduction capture and exact replay for this
explicit before-query. C++ execution/extraction, JSON decoding, the full
preprocessor and original network-file correspondence remain unverified.
The next small target is finite checked ReLU introductions and a two-ReLU
native capture.

## Fifteenth milestone: finite ReLU introductions and native two-ReLU replay

Date: 2026-09-22. Isabelle version: `Isabelle2025-2`.
The main session now has **51 theories**. New theories:

* `ReLU_Auxiliary_Sequence`: executable finite composition, singleton and
  append laws, failure persistence, SAT/UNSAT preservation over real
  valuations, and `check_after_relu_aux_sequence_sound`.
* `Imported_Marabou_Native_Relu_Sequence`: generated whole-query matching,
  before/processed equisatisfiability, combined checker acceptance and
  UNSAT of the captured six-variable before-query.
* `ReLU_Auxiliary_Sequence_Examples`: SAT sequence witnesses, late rejection
  checks, and `native_source_needs_both_relus`, proving that removing either
  ReLU from the new captured query yields a real model.

Every introduction checks the query produced by the previous step.
No certificate constructor or earlier inference rule was changed.
Both new public functions pass Standard ML code compilation in the session.
The single-introduction and tableau-sequence interfaces remain compatible.

### Native capture and preserved rejected trial

The accepted query is `b=c=z<=-1/2`, `f+g=w>=1/4`,
`f=ReLU(b)` and `g=ReLU(c)`, with explicit finite bounds.
The real native method introduces `a=x6` and `d=x7` from the six-variable
plain query; engine initialization adds five scalar-fixed auxiliaries.

Command:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sequence --output Isabelle/generated/native_relu_sequence_capture
```

Exit status: **0**. Native output:

```text
Engine::processInputQuery(input, false): true
Engine::solve(10): false; exit code UNSAT
Proof production: true; preprocessing: false; DeepSoI: false
Processed variables: 13; rows: 5
PLC lemmas: 0 before solve; 2 after solve
Main-loop iterations: 2; simplex steps: 1
Initial query/tableau/ground-bound snapshot comparison: exact match
Captured unmodified solver certificate and pre-solve query snapshot.
Captured pre-initialization source query and 5 proposed scalar-fixed introductions.
Native ReluConstraint::transformToUseAuxVariables: two calls; 6 -> 8 variables.
Captured queries before and after the native ReLU introduction sequence.
```

The two PLC lemmas have nonempty linear explanations and conclude `f<=0`
and `g<=0` respectively. Both are replayed, followed by the native linear
contradiction. The harness constructs no proof nodes or added ReLU equations.
It invokes the native introduction methods directly after the upstream
initial-bound notification helper; full preprocessing remains disabled.

Six data artifacts and three provenance/report/log files are saved under
`Isabelle/tests/fixtures/marabou/solver_relu_sequence*`. The new strict
`import_marabou_relu_sequence.py` constructs every introduction, compares the
entire independent final source, and invokes the existing downstream import.
The generated HOL independently checks all transformations and the proof.

All six earlier accepted solver scenarios were executed again with the final
shared harness into `Isabelle/generated/sequence_refresh_<scenario>`.
All exited **0**. All data inputs remained byte-identical; saved logs,
reports and provenance were refreshed from those executions.
There are sixteen accepted writer certificate files, seven fully replayed
native scenarios, and twenty-one generated import theories.

An earlier exploratory chained query `b=z, c=f-1/4, g=w` produced four
native PLC lemmas. Its fourth lemma uses a positive lower bound on the second
ReLU's **output** to force its auxiliary to zero. The existing importer
supports the input-based auxiliary rule, so it rejected the entire proof.
The seven unchanged JSON artifacts are isolated in
`Isabelle/tests/fixtures/marabou/rejected_relu_chain` and tested to remain
rejected. No HOL acceptance is claimed for that trial, and its direct binary
invocation did not create full build provenance. It is excluded from the
accepted-certificate count. No node or lemma was filtered into a replay.

Source inspection covered `Preprocessor::transformConstraintsIfNeeded`,
`informConstraintsOfInitialBounds`, and
`ReluConstraint::transformToUseAuxVariables/notifyUpperBound/notifyLowerBound`.
The latter's positive-output branch is documented as the next inference-rule
target. An unsupported rule is a coverage limit, not evidence of a solver bug.

### Compiling checkpoints

The completed generic sequence theory first built with exit **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:30 elapsed time, 0:01:49 cpu time, factor 3.57)
0:00:34 elapsed time, 0:01:49 cpu time, factor 3.20
```

The standalone native replay command was:

```sh
isabelle build -d Isabelle -D Isabelle/generated/native_relu_sequence_capture
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:32 elapsed time, 0:01:50 cpu time, factor 3.35)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:04 elapsed time, 0:00:06 cpu time, factor 1.59)
0:00:40 elapsed time, 0:01:56 cpu time, factor 2.86
```

The complete main session, including all new examples, then built with
`isabelle build -D Isabelle`, exit **0**:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:31 elapsed time, 0:01:54 cpu time, factor 3.65)
0:00:34 elapsed time, 0:01:54 cpu time, factor 3.27
```

### Tests and final audit

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exit status: **0**, **174 tests passed** (1.095 seconds).
The 28 new tests cover native sequence replay and regeneration, provenance,
empty/singleton compatibility, execution order, incomplete/duplicate steps,
late freshness and premise failures, altered before/after atoms and metadata,
unjustified caps, incorrect later tableau steps, corrupted/omitted native
lemmas, terminal evidence, overwrite/injection guards, and the preserved
unsupported trial. A coherent relaxed before/after/processed query has an
explicit rational model and rejects the old contradiction.

All twenty-one generated theories match regeneration. All seven accepted
capture provenance records match their saved artifacts and current sources.
The unchanged standalone SML smoke tests were not repeated; SML compilation
of the new sequence functions and proof-producing HOL computations passed.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:03 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. No admitted-proof or added-axiom tokens occur in the 51 project
theories. All 301 local links resolve in 24 project Markdown files. Whitespace
checks and `git diff --check` passed. Both upstream repositories remain clean
at the audited revisions, and Git staging remains empty. Only this record
was completed after the final build.

The precise new assurance is finite checked ReLU composition over real
semantics and UNSAT of the explicit captured two-ReLU before-query.
Native iteration, extraction/decoding, general preprocessing and original
network-file correspondence remain unverified. The next small target is the
observed strictly-positive-output-lower-bound auxiliary rule and replay of
its preserved evidence. UAT's existing sigmoid reuse note remains applicable;
no sigmoid definition or dependency was added.

## Sixteenth milestone: positive-output propagation and preserved proof replay

Completed on 2026-09-22 with Isabelle2025-2. The previously unsupported
positive-output rule is now checked, and the complete preserved chain replays.
The fifteenth milestone's rejection records describe its historical state.

### Verified rule and importer

Added `ReLU_Output_Bound_Propagation.thy`:

```text
y = ReLU(x),  0 < l <= y,  y - x - a = 0  imply  a = 0.
```

`check_relu_output_aux_upper_bound` checks ReLU membership, the explicit
output lower bound, exact strict positivity, two linear implication witnesses
for the auxiliary equation, and a nonnegative proposed auxiliary upper bound.
Its soundness and model-preservation theorems justify adding the bound.
The new `Relu_Output_Aux_Upper` constructor is included in the recursive
soundness induction and exported SML interface.

The adapter distinguishes input and output lower causes and reconstructs
explanations using the actual causing variable. It checks every native lemma
and continuation; linear premises still do not become native ground updates.
Ambiguous input/output roles reject. No floating-point epsilon is used.

`ReLU_Output_Bound_Examples.thy` proves acceptance and UNSAT for a small
single-rule example, exact tiny-positive acceptance, weaker-cap acceptance,
real SAT witnesses, and rejection of wrong/missing premises and equation
witnesses. At the zero boundary, `x=-1,y=0,a=1` is a model. Incorrectly adding
`a<=0` creates a linear contradiction, but the guarded rule rejects the
attempted lift. A relaxed native chained source also has a proved real model
and admits no accepted composed certificate.

Inspected native correspondence:

* `src/engine/ReluConstraint.cpp::notifyLowerBound`, positive `_f` branch
  around lines 177–196.
* `src/proofs/Checker.cpp::checkReluLemma`, lines 674–678. Its epsilon-based
  positivity test is not inherited by HOL.
* `src/proofs/UnsatCertificateUtils.cpp`,
  `UNSATCertificateUtils::computeBound/getExplanationRowCombination`.
* `src/proofs/JsonWriter.cpp::writePLCLemmas` and
  `ReluConstraint::transformToUseAuxVariables`.

### Preserved evidence and fresh native reproduction

The standalone replay generated directly from the historical six data files
built with:

```sh
isabelle build -d Isabelle -D Isabelle/generated/output_bound_replay
```

Exit status: **0**. Exact output:

```text
Building Marabou_Verification ...
Finished Marabou_Verification (0:00:37 elapsed time, 0:02:08 cpu time, factor 3.40)
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:07 elapsed time, 0:00:13 cpu time, factor 1.74)
0:00:49 elapsed time, 0:02:22 cpu time, factor 2.86
```

A fresh execution used:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_chain --output Isabelle/generated/native_output_bound_capture
```

Exit status: **0**. Native proof production was enabled, preprocessing and
DeepSoI disabled. The run performed two native ReLU introductions
(6 → 8 variables), then five tableau introductions (8 → 13), three main-loop
iterations and one simplex step. Initialization succeeded; `Engine::solve`
returned false with exit code UNSAT. The proof has four PLC lemmas, one
explained leaf, no split and no delegation.

All six `solver_relu_chain` data artifacts match the preserved exploratory
files byte-for-byte. New report/log/provenance files describe this fresh run;
they do not retroactively attest the original exploratory binary invocation.
All seven historical JSON files remain unchanged.

The four recorded native lemmas replay in order:

1. Input `b<=-1/2` gives output `f<=0`.
2. Input `c>=-1/4` justifies the weaker auxiliary cap `d<=0.250001`.
3. Input `c<=-1/4` justifies the weaker output cap `g<=1.750001`.
4. Output `g>=1/4` and the checked equation `g-c-d=0` give `d<=0`.

The last lemma is not essential to every possible refutation of this query:
the earlier prefix can already close the recorded leaf, as a regression
test checks. The full native proof still validates all four lemmas.
Corrupting the fourth explanation rejects rather than skipping that node.
The separate small query exercises a certificate that needs the new rule.

`Imported_Marabou_Native_Relu_Chain.imported_before_relu_query_unsatisfiable`
proves real-semantic UNSAT of the explicit six-variable starting query,
through both ReLU introductions, five tableau steps and the entire proof.
All seven older scenarios were rerun under
`Isabelle/generated/output_bound_refresh_<scenario>`. Every run exited **0**,
their data artifacts remained byte-identical, and saved provenance was
refreshed from those actual executions.

### Build, tests and final audit

The main session with all 54 theories and examples built and exported using
`isabelle build -e -D Isabelle`. Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:37 elapsed time, 0:02:18 cpu time, factor 3.65)
Exporting Marabou_Verification ...
0:00:41 elapsed time, 0:02:18 cpu time, factor 3.31
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'` exited **0**:
**197 tests passed** in 1.448 seconds, including 23 new rule/import tests.
Coverage includes full regeneration, preserved/fresh byte equality, provenance,
strict positivity at and near zero, cause-variable selection, both equation
directions, malformed evidence, a SAT relaxation, ordering and ground-state
distinctions, recursive child checks and sibling isolation.

Both smoke scripts passed against the refreshed SML exports:

```text
8 exported SML checker tests passed
47 exported SML proof-tree tests passed
```

The executable was
`/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly`,
invoked with `--script` on `Isabelle/tests/linear_leaf_smoke.ML` and
`Isabelle/tests/proof_tree_smoke.ML`. Both exited **0**.
HOL replay uses proof-producing computations; these separate execution tests
add the code-generation/compiler/runtime boundary.

All 22 generated import theories match regeneration. There are seventeen
canonical accepted writer fixtures: nine component fixtures and eight fully
replayed native scenarios, plus the retained duplicate historical chain.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:02 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. The 54 project theories contain no admitted-proof or added-axiom
tokens. All 325 local links resolve in 25 project Markdown files. Whitespace
checks and `git diff --check` passed. Both upstream repositories remain clean
at their pinned revisions; Git staging remains empty. Only this build record
was completed after the final build.

The new assurance is exact positive-output propagation and UNSAT of the
explicit captured chained query through checked introductions and proof
replay. The C++ implementation, extraction/decoding, floating-point refinement,
general preprocessing and correspondence to original network files remain
unverified. This extension resolves a coverage limit; it does not establish
an observed solver defect.

The next small rule target is the dual native branch: a strictly positive
auxiliary lower bound forces the ReLU output to zero, with exact premise and
equation checks followed by native evidence capture.

## Seventeenth milestone: positive-auxiliary propagation and native replay

Completed on 2026-09-23 with Isabelle2025-2. The dual of the positive-output
rule is verified, and a new actual native proof using it replays to a
starting-query UNSAT theorem. Details are in
[RELU_AUX_LOWER_BOUND_PROPAGATION.md](RELU_AUX_LOWER_BOUND_PROPAGATION.md).

### Verified rule and importer

Added `ReLU_Aux_Lower_Bound_Propagation.thy`:

```text
y = ReLU(x),  y - x - a = 0,  0 < l <= a  imply  y = 0.
```

`check_relu_aux_lower_output_upper_bound` checks ReLU membership, the explicit
auxiliary lower bound, exact strict positivity, two linear implication
witnesses for the auxiliary equation, and a nonnegative proposed output upper
bound. Soundness and model preservation justify adding `y<=u`. The new
`Relu_Aux_Lower_Output_Upper` constructor has its own case in the recursive
soundness induction and is included in the exported SML interface.

The adapter matches lower-cause lemmas against all three lower-cause patterns
and all ReLU metadata, requiring one match in total. The auxiliary premise is
reconstructed for the actual causing variable and must be exactly positive;
linear premises still do not become native ground updates.

Inspected native correspondence at `1c2f4788c32e2f4e407c356b763a8025c5578722`:

* `src/engine/ReluConstraint.cpp::notifyLowerBound`, lines 207–226, and
  `checkIfLowerBoundUpdateFixesPhase`, lines 125–133.
* `src/proofs/Checker.cpp::checkReluLemma`, lines 685–689; its epsilon-based
  positivity test is not inherited by HOL.
* `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound`,
  lines 414–494, and `propagateTightenings`, lines 268–284.
* `src/proofs/UnsatCertificateUtils.cpp` and `JsonWriter.cpp::writePLCLemmas`.

### Native capture

The local harness gained scenario `relu_aux_inactive`; upstream is unchanged.
A probe run of the rebuilt binary and the canonical command

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_aux_inactive --output Isabelle/generated/aux_lower_capture
```

both exited **0** with byte-identical data. Proof production was enabled,
preprocessing and DeepSoI disabled. Initialization succeeded with the phase
unfixed; `Engine::solve` returned false with exit code UNSAT after two
main-loop iterations and no simplex steps, splits or delegation. The proof has
one PLC lemma, `aux=x0 L -> f=x2 U, bound 0`, with explanation weight `-1` on
row 0, and one row contradiction. The generated standalone replay built with:

```sh
isabelle build -d Isabelle -D Isabelle/generated/aux_lower_capture
```

Exit status: **0**. Exact output:

```text
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time, 0:00:03 cpu time)
0:00:06 elapsed time, 0:00:03 cpu time, factor 0.52
```

`Imported_Marabou_Solver_Relu_Aux_Inactive.imported_query_unsatisfiable` and
`Imported_Marabou_Source_Relu_Aux_Inactive.imported_source_query_unsatisfiable`
are now in the main session. The latter proves UNSAT of the explicit captured
five-variable source over real valuations through three checked tableau
introductions, the exact auxiliary premise `a>=1/4`, the new rule and a leaf
of margin `1/4`. The processed query's linear relaxation has a proved model,
so a linear leaf alone cannot certify it.

Because the harness and importer changed, all nine scenarios were rerun under
`Isabelle/generated/aux_lower_refresh_<scenario>`. Every run exited **0**.
All data artifacts, run reports and logs are byte-identical to the saved
fixtures. The eight older provenance records differ only in the hashes of
`capture.cpp`, the capture script, the importer and the rebuilt binary; they
were replaced by the refreshed records from these actual executions. The
historical `rejected_relu_chain` files are unchanged.

### Build, tests and final audit

`isabelle build -c -e -D Isabelle` (clean rebuild and export of all 58
theories). Exit status: **0**. Exact output:

```text
Cleaned Marabou_Verification
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:44 elapsed time, 0:02:45 cpu time, factor 3.70)
Exporting Marabou_Verification ...
0:00:48 elapsed time, 0:02:45 cpu time, factor 3.41
```

Both smoke scripts, run with the same Poly/ML executable as before, exited
**0** against the refreshed exports:

```text
8 exported SML checker tests passed
62 exported SML proof-tree tests passed
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'` exited **0**:
**221 tests passed** in 1.558 seconds, including 24 new tests in
`test_marabou_aux_lower_bound.py`. All 24 generated import theories match
regeneration. There are eighteen canonical accepted writer fixtures: nine
component fixtures and nine fully replayed native scenarios.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:03 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. The 58 project theories contain no `sorry`, `oops` or
`axiomatization` tokens. All 360 local links resolve in 28 project Markdown
files. `git diff --check` passed and the new files have no trailing
whitespace. Both upstream repositories remain clean at their pinned
revisions; Git staging remains empty.

The new assurance is exact positive-auxiliary propagation and UNSAT of the
explicit captured `relu_aux_inactive` source query through checked
introductions and proof replay. In that source the auxiliary is an ordinary
variable with an explicit equation; no native-introduction run emitting this
rule is claimed. The C++ implementation, extraction/decoding, floating-point
refinement, general preprocessing and correspondence to original network
files remain unverified.

Two emitted native ReLU lemma patterns remain unsupported: output upper to
input upper, and auxiliary upper zero to input lower zero. Source inspection
and a scratch probe (no emission in four tiny runs; one delegated leaf) show
they are hard to reach in this configuration, so they stay open until a
capture needs them. The next bounded target is an exact SAT-assignment checker.

## Eighteenth milestone: exact SAT assignments and a native SAT capture

Completed on 2026-09-23 with Isabelle2025-2. This is roadmap item D. Details
are in [SAT_ASSIGNMENTS.md](SAT_ASSIGNMENTS.md).

### Checker

Added `Rational_Assignment.thy`. `check_rat_assignment Q σ` requires distinct
listed variables and exactly checks every linear atom, bound and ReLU of `Q`
at the finite rational assignment `σ` (unlisted variables are 0).
`check_rat_assignment_iff` proves this equivalent to the embedded valuation
being a real model of `embed_query Q`; `check_rat_assignment_sound` and
`check_rat_assignment_satisfiable` give models and SAT. Lifting theorems carry
an accepted processed-query assignment through checked tableau and ReLU
introductions to SAT of the starting query. The checker is exported as
`Marabou_Assignment_Checker.ML`. `Rational_Assignment_Examples.thy` proves
acceptance and rejection cases, including a ReLU-only violation.

### Native SAT capture

The local harness gained scenario `relu_sat`; upstream is unchanged. A probe
run and the canonical driver run exited **0**. Two plain ReLUs received native
auxiliaries (7 → 9 variables), five tableau slacks followed (→ 14), and
`Engine::solve` returned true with exit code SAT after five main-loop
iterations and two simplex steps, without splits. `Engine::extractSolution`
on the processed query supplied all 14 doubles, stored as round-trip decimals
and exact hexadecimal floats. Their exact binary values form a model; no
repair was needed. The new `import_marabou_assignment.py` generated
`Imported_Marabou_Native_Relu_Sat.thy`, whose `code_simp` proofs show that the
same exact assignment satisfies the explicit processed, source and
before-ReLU queries. The driver's standalone replay built with exit **0**:

```text
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:02 elapsed time, 0:00:04 cpu time)
0:00:55 elapsed time, 0:03:03 cpu time, factor 3.33
```

The harness, capture driver and source importer changed, so all ten scenarios
were rerun under `Isabelle/generated/sat_refresh_<scenario>`. Every run exited
**0**. All data artifacts, run reports and logs are byte-identical to the
saved fixtures; provenance differs only in the hashes of `capture.cpp`, the
capture script, the source importer and the binary (for `relu_sat`, of the
assignment importer, which gained an overflow guard after the trial run).
The refreshed records replaced the saved ones.

### Build, tests and final audit

`isabelle build -c -e -D Isabelle` (clean rebuild and export of all 61
theories). Exit status: **0**. Exact output:

```text
Cleaned Marabou_Verification
Running Marabou_Verification ...
Finished Marabou_Verification (0:00:46 elapsed time, 0:03:00 cpu time, factor 3.90)
Exporting Marabou_Verification ...
0:00:50 elapsed time, 0:03:00 cpu time, factor 3.59
```

The three smoke scripts, run with the same Poly/ML executable, exited **0**:

```text
8 exported SML checker tests passed
62 exported SML proof-tree tests passed
11 exported SML assignment tests passed
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'` exited **0**:
**236 tests passed** in 1.624 seconds, including 15 new tests in
`test_marabou_assignment.py`. All 25 generated import theories match
regeneration.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:03 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. The 61 project theories contain no `sorry`, `oops` or
`axiomatization` tokens. All 380 local links resolve in 29 project Markdown
files. `git diff --check` passed and the new files have no trailing
whitespace. Both upstream repositories remain clean at their pinned
revisions; Git staging remains empty.

The new assurance is that an exactly checked rational assignment is a real
model of an explicit query, and that the exact binary values reported by one
native SAT run are such a model for each captured stage of its query. No
theorem concerns the C++ SAT return value, its tolerance-based checks, or
extraction and decoding. The next bounded target is roadmap item B, a narrow
exact input representation with a stated decoding trust boundary.

## Nineteenth milestone: exact query text format with a HOL decoder

Completed on 2026-09-23 with Isabelle2025-2. This is the first step of
roadmap item B. Details are in [EXACT_QUERY_FORMAT.md](EXACT_QUERY_FORMAT.md).

### Format, decoder and round trip

Added `Exact_Query_Format.thy`. `decode_query` maps byte lists in the
`marabou-exact-query-v1` language (one-space tokens, LF-terminated lines,
exact integers, fractions and finite decimals) to `rat_query`, rejecting all
other input; it is the definition of the format's meaning. `encode_query` is
a canonical encoder, and `decode_encode_query` proves that every query whose
linear expressions have constant 0 decodes back exactly from its encoding.
`Exact_Query_Text.check_file` is a build-time ML check comparing a defined
byte list with a file. `Exact_Query_Format_Examples.thy` proves decoding of
every statement and number form and rejection of 25 malformed inputs.

### Capture texts

`tools/exact_query_text.py` exported the ten captured starting queries to
`tests/fixtures/marabou/solver_<scenario>.mqx` and generated
`Imported_Marabou_Exact_Texts.thy`. The build declares each file with
`external_file`, checks it against its byte list, proves by `code_simp` that
its decoding is the replayed starting query, and restates the nine UNSAT
theorems and the SAT model about the decoded bytes. A scratch session
confirmed that the file check accepts a matching list and fails the build on a
one-byte mismatch. No capture, importer or harness source changed, so no
provenance refresh was needed.

### Build, tests and final audit

`isabelle build -c -e -D Isabelle` (clean rebuild and export of all 64
theories). Exit status: **0**. Exact output:

```text
Cleaned Marabou_Verification
Running Marabou_Verification ...
Finished Marabou_Verification (0:01:12 elapsed time, 0:04:55 cpu time, factor 4.07)
Exporting Marabou_Verification ...
0:01:16 elapsed time, 0:04:55 cpu time, factor 3.87
```

The ten `code_simp` decodings account for most of the added build time.
The three smoke scripts exited **0**:

```text
8 exported SML checker tests passed
62 exported SML proof-tree tests passed
11 exported SML assignment tests passed
```

`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'` exited **0**:
**246 tests passed** in 1.572 seconds, including 10 new tests in
`test_exact_query_text.py`. All 26 generated theories match regeneration.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:02 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. The 64 project theories contain no `sorry`, `oops` or
`axiomatization` tokens. All 395 local links resolve in 30 project Markdown
files. `git diff --check` passed and the new files have no trailing
whitespace. Both upstream repositories remain clean at their pinned
revisions; Git staging remains empty.

The new assurance is that the relation from these files' bytes to the HOL
queries is defined and checked inside Isabelle. The native runs did not read
the files: the harness builds its queries in C++, and the files were exported
from the captured snapshots afterwards. The next bounded target is roadmap E,
a single invocation that reads a user-supplied `.mqx` file, runs the native
solver on it and yields a theorem about that file's decoded bytes.

## Twentieth milestone: one-command query-file workflow

Completed on 2026-09-23 with Isabelle2025-2. This is roadmap item E. Details
are in [QUERY_FILE_WORKFLOW.md](QUERY_FILE_WORKFLOW.md).

### What was added

* `capture.cpp`: a `file QUERY.mqx` mode with a strict, untrusted C++ reader
  (GMP-checked exact doubles; equalities only; exactly one finite lower and
  upper bound per variable), any number of plain ReLUs through the native
  introduction sequence, and arbitrary nondelegated proof trees or a SAT
  assignment. Existing scenarios behave as before.
* `Exact_Query_Format.thy`: `same_constraints`, `decodes_like` and transfer
  lemmas, so a result about a captured query holds for any file whose decoding
  has the same constraint sets.
* `import_marabou_query_file.py`: pipeline pre-checks with readable reasons,
  binding of a file to its capture, and the generated theorem theory
  (byte list, `external_file`, file check, `decodes_like` by `code_simp`,
  transferred UNSAT or model theorem).
* `capture_marabou_solver.py --query-file` and the one-command wrapper
  `verify_query_file.py`.
* Examples in `Isabelle/examples`, three main-session theorem theories
  `Imported_Marabou_Example_*`, adversarial HOL lemmas in
  `Exact_Query_Format_Examples`, and `tests/test_marabou_query_file.py`.

### Native evidence

All ten scenarios were rerun under `Isabelle/generated/release_refresh_<scenario>`
and the three example files under `Isabelle/generated/release_file_<example>`
with the final sources. Every run exited **0**. Scenario data, reports and
logs are byte-identical to the saved fixtures; provenance changed only in the
hashes of `capture.cpp`, the capture script and the binary, and the refreshed
records replaced the saved ones. The file runs' snapshots, proofs and
assignment are byte-identical to the `relu_chain`, `relu_sat` and `linear`
fixtures, including for the reordered chain file; their reports, logs and
provenance are saved as `file_<example>_*`. Each generated file session built
with exit **0**:

```text
relu_chain_unsat: Finished Marabou_Import_Replay (0:00:13 elapsed time, 0:00:25 cpu time, factor 1.88)
relu_sat:         Finished Marabou_Import_Replay (0:00:16 elapsed time, 0:00:19 cpu time, factor 1.22)
linear_unsat:     Finished Marabou_Import_Replay (0:00:04 elapsed time, 0:00:05 cpu time, factor 1.22)
```

`python3 Isabelle/tools/verify_query_file.py Isabelle/examples/linear_unsat.mqx
Isabelle/generated/verify_linear_unsat` exited **0** and printed the checked
`Query_File_Theorem.query_file_unsatisfiable`. On
`rejected_inequality.mqx` it exited **1** before building, with
`le/ge statements are not supported by this capture pipeline`. The C++ reader,
run directly on the three rejected examples, a `1/0` bound and a missing final
newline, exited **1** with the corresponding specific messages.
In scratch copies of a generated session, changing only `query.mqx` failed
the build at `Byte list differs from file query.mqx`, and changing the file
and its byte list together failed the `decodes_like` proof.

### Build, tests and final audit

`isabelle build -c -e -D Isabelle` (clean rebuild and export of all 67
theories). Exit status: **0**. Exact output:

```text
Cleaned Marabou_Verification
Running Marabou_Verification ...
Finished Marabou_Verification (0:01:36 elapsed time, 0:06:50 cpu time, factor 4.26)
Exporting Marabou_Verification ...
0:01:40 elapsed time, 0:06:50 cpu time, factor 4.09
```

The three smoke scripts exited **0** with 8, 62 and 11 passed checks.
`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'` exited **0**:
**262 tests passed** in 2.035 seconds, including 16 new query-file tests.

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:03 elapsed time
```

`isabelle build_log -H 'Error|Warning' Marabou_Verification` exited **0**
with no output. The 67 project theories contain no `sorry`, `oops` or
`axiomatization` tokens. All 410 local links resolve in 31 project Markdown
files. `git diff --check` passed and the new files have no trailing
whitespace. Both upstream repositories remain clean at their pinned
revisions; Git staging remains empty.

The new assurance: for a supported `.mqx` file, one command yields an
Isabelle/HOL theorem about `decode_query` of the file's exact bytes, while
the C++ reader, solver, capture and JSON import are untrusted for it. Known
cosmetic issue: when the Python pre-check rejects a file, the driver's message
still names an output directory for logs that was not created.

## Twenty-first milestone: reviewed continuation and checked inequality auxiliaries

Completed on 2026-09-23 with Isabelle2025-2 after the user requested review of
Claude's progress and continued implementation. Claude's milestones 17–20
were already complete. The inherited 67-theory session built with exit 0
(0:00:03), and 262 Python tests passed in 2.664 seconds before editing.

### Review and new verified step

Reviewed the auxiliary-lower rule, exact rational assignment evaluation and
lifting, the HOL text decoder and round-trip structure, constraint-set
transfer, build-time file comparison and `external_file` use, query-file
adapter/driver, and milestone records. No soundness defect was identified in
the examined parts. This was not an exhaustive independent audit of every
line. The known pre-check message naming a not-yet-created log directory
remains a diagnostic issue.

Inspected `src/engine/Preprocessor.cpp::makeAllEquationsEqualities` at the
pinned Marabou revision, and its call within `Preprocessor::preprocess`.
The native method appends coefficient +1 in both directions:

```text
e <= b   becomes   e + s = b, s >= 0
e >= b   becomes   e + s = b, s <= 0
```

Added four theories:

* `Inequality_Auxiliary`: selected-atom characterization, extension with
  `s=b-eval(e)`, projection, and real SAT/UNSAT equivalence under freshness.
* `Rational_Inequality_Auxiliary`: executable index/type/global-freshness
  guards, constructed result, exact embedding and single-step certificate
  soundness.
* `Inequality_Auxiliary_Sequence`: finite checked composition and failure
  laws, model projection, SAT/UNSAT preservation, composition before existing
  ReLU/tableau introductions and certificate checking, exact SAT witness
  projection, and SML export.
* `Inequality_Auxiliary_Examples`: affine expressions, duplicate and zero
  terms, both signs and zero boundary, invalid indices and all-component
  collisions, late failures, SAT witnesses, UNSAT certificates and a decoded
  inequality text.

Counterexamples show how unchecked reuse of a bound-only name or an incorrect
GE sign would create a false contradiction. Checked interfaces reject those
attempts. A composed example includes two inequality introductions, one ReLU
introduction, three tableau introductions, a linear premise and nonlinear
propagation before the leaf. Its linear relaxation has a proved real model.
All new examples are hand-written HOL evidence; no native inequality
preprocessing execution or native `le`/`ge` file theorem is claimed.

### Compiling checkpoints and execution tests

The real theory compiled first, exit 0, total 0:01:45. After resolving a
datatype-existential proof in the rational interface, the rational and finite
sequence theories compiled, exit 0, total 0:01:48. No admission was used.

The completed 71-theory session built and exported with:

```sh
isabelle build -e -D Isabelle
```

Exit status: **0**. Exact output:

```text
Running Marabou_Verification ...
Finished Marabou_Verification (0:01:42 elapsed time, 0:07:22 cpu time, factor 4.34)
Exporting Marabou_Verification ...
0:01:46 elapsed time, 0:07:22 cpu time, factor 4.17
```

Using the same audited Poly/ML executable as previous milestones, all four
scripts exited **0**:

```text
8 exported SML checker tests passed
62 exported SML proof-tree tests passed
11 exported SML assignment tests passed
16 exported SML inequality auxiliary tests passed
```

The new script is `Isabelle/tests/inequality_auxiliary_smoke.ML`.
Its generated module reports three non-exhaustive-match warnings in library
helpers `nth`, `image` and set union. Inspection confirmed that the exported
interfaces guard indexed selections and construct finite sets from lists;
the partial helpers and set constructors are hidden by the module signature.
No reachable missing case was found through the exported interface.
The new tests include invalid indices and name collisions. Generated code
was not hand-edited to suppress these warnings.

The final Python command
`python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'`
exited **0**, **262 tests passed** in 2.026 seconds. No Python/C++ source,
saved native fixture or provenance record changed in this milestone.

### Independent review of the native file workflow

A fresh UNSAT file capture under `Isabelle/generated/resume_review_chain`
completed, but its first wrapper replay hit sandbox `SQLITE_READONLY` access
to Isabelle's user database. Re-running the generated session with required
access succeeded: parent 0:01:48, replay 0:00:15, total 0:02:08.
This was an environment restriction, not a proof or solver failure.

Both complete wrapper invocations then exited **0** with required access:

```sh
python3 Isabelle/tools/verify_query_file.py \
  Isabelle/examples/relu_sat.mqx Isabelle/generated/resume_review_sat
python3 Isabelle/tools/verify_query_file.py \
  Isabelle/examples/relu_chain_unsat.mqx Isabelle/generated/resume_review_chain_full
```

They printed `Query_File_Theorem.query_file_model` and
`Query_File_Theorem.query_file_unsatisfiable` respectively.
Exact standalone build output:

```text
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:16 elapsed time, 0:00:20 cpu time, factor 1.23)
0:00:20 elapsed time, 0:00:20 cpu time, factor 0.98
```

```text
Running Marabou_Import_Replay ...
Finished Marabou_Import_Replay (0:00:15 elapsed time, 0:00:27 cpu time, factor 1.81)
0:00:19 elapsed time, 0:00:27 cpu time, factor 1.45
```

All six captured data artifacts from each fresh execution match the
corresponding canonical `relu_sat`/`relu_chain` fixture bytes.

### Final state and assurance

Final required command: `isabelle build -D Isabelle`.
Exit status: **0**, up to date. Exact output:

```text
0:00:03 elapsed time
```

The Isabelle Error/Warning log filter exited 0 with no output. This is
separate from the documented standalone Poly/ML warnings above.
All 71 theories have completed proofs, without added axioms or unfinished-proof
commands. All 430 local links resolve in 32 project Markdown files.
Whitespace checks and `git diff --check` passed. Staging remains empty and
both upstream repositories are unchanged. Only documentation was completed
after the final build.

The new assurance is real-semantic correctness of checked signed slack
introductions and their composition with the existing SAT/UNSAT checking
pipeline. The native file workflow still rejects inequalities. The next
bounded target is a checked opposite finite slack bound, followed by capture
and import of the transformation alongside a tiny inequality file run.
General preprocessing and the C++ implementation remain unverified.

## Twenty-second milestone: `le`/`ge` files through checked finite slack caps

Completed on 2026-09-23 by Claude, after the user asked for `le`/`ge` support,
certified initial phase fixing and native preprocessing. The first of these
was already implemented in the working tree by an earlier Codex session,
but not recorded as complete. That session added
`Bounded_Inequality_Auxiliary`/`_Examples`, `prepare_inequalities.py`, driver
and adapter support, two native inequality file runs and their generated
theories. The direction audit then found three failing provenance tests
(stale tool hashes) and stale status text. This milestone reviewed that work,
finished it and recorded it.

### Work done

* Added [refresh_native_fixtures.py](../Isabelle/tools/refresh_native_fixtures.py).
  It reruns all ten scenarios and every example file. By default it refuses
  unless each rerun reproduces every saved data artifact byte for byte. It
  replaces only the run reports, logs and provenance, so provenance comes
  only from real reruns.
* The earlier `rejected_inequality.mqx` is accepted by the current pipeline:
  a scratch run of `verify_query_file.py` exited 0 with
  `Query_File_Theorem.query_file_model`. It was renamed
  `inequality_linear_sat.mqx`. Its complete artifact set is now saved, and
  two generated theories were added to the main session.
* `import_marabou_query_file.py` now has one table,
  `FULL_ARTIFACT_EXAMPLES`, for all file runs whose complete artifacts are
  saved.
* New tests cover every such example: exact theory regeneration and ROOT
  registration, the artifact set named by provenance, and provenance hashes
  for the run, log, tools and compiled sources.
* `verify_query_file.py` now lists the local inequality preparation among
  the untrusted components.
* The driver's pre-check message no longer names a log directory that does
  not exist; this was already fixed and tested in the working tree.

### Native reruns

```sh
python3 Isabelle/tools/refresh_native_fixtures.py --tag m22_refresh
```

Exit **0**, 6.4 s (native build cached). All ten scenarios and five of the
six example files reproduced every saved data artifact byte for byte. The
new `inequality_linear_sat` run saved its first artifact set. Only run
reports, logs and provenance records were replaced. This fixes the three
stale-provenance failures reported by the audit.

### Validation

```text
$ isabelle build -c -e -D Isabelle        (81 theories)
Finished Marabou_Verification (0:01:33 elapsed time, 0:06:55 cpu time, factor 4.44)
0:01:37 elapsed time, 0:06:55 cpu time, factor 4.27     exit 0

8 exported SML checker tests passed
62 exported SML proof-tree tests passed
11 exported SML assignment tests passed
16 exported SML inequality auxiliary tests passed      (all exit 0)

$ python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
Ran 279 tests in 2.047s
OK
```

The `build_log` Error/Warning filter was empty. No `sorry`, `oops`,
`axiomatization`, `axioms` or `undefined` token occurs in any project theory,
and `quick_and_dirty = false`. All 529 local links and anchors in 35 Markdown
files resolve, and `git diff --check` is clean. Both upstream checkouts are
clean at their pinned revisions and staging is empty. The seven
`rejected_relu_chain` JSON files are unchanged.

### Assurance

For the three `le`/`ge` example files, the theorems concern the original
bytes. HOL checks every slack, cap and witness produced by the Python
preparation. The native harness read only the prepared equality file.
Marabou's own `makeAllEquationsEqualities` was not executed on this route.

## Twenty-third milestone: certified ReLU phases fixed before solving

Completed on 2026-09-23. See [RELU_PHASE_FIXING.md](RELU_PHASE_FIXING.md).

### Finding

With preprocessing disabled, `informConstraintsOfInitialBounds` can fix a
ReLU phase before any bound manager exists. `Engine::solve` then applies the
phase's valid split. `Engine::applySplit` adds each strictly tighter split
bound as a new ground bound without an explanation. The native certificate
has no node for these bounds, so the file workflow used to reject such
queries.

### Work done

* HOL: [ReLU_Phase_Fixing.thy](../Isabelle/ReLU_Phase_Fixing.thy) proves
  `check_relu_fixed_active/inactive` sound. An exactly proved phase-deciding
  bound, from the query plus the ReLU hull rows `y ≥ 0` and `y ≥ x`, gives
  model-set equality with the phase's split query.
  [Rational_Proof_Trees.thy](../Isabelle/Rational_Proof_Trees.thy) adds
  `Relu_Fix_Active` and `Relu_Fix_Inactive` with their soundness cases. Both
  are exported, and 10 new SML checks cover them.
* [ReLU_Phase_Fixing_Examples.thy](../Isabelle/ReLU_Phase_Fixing_Examples.thy)
  covers:
  * acceptance by input, output and hull-row premises, and a proof that no
    weights work without the hull row;
  * relaxations with models;
  * epsilon-style and malformed rejections;
  * `tiny_positive`, a satisfiable query that an unchecked epsilon phase fix
    would refute.
* Harness (file mode only): writes `solver_file_phase_fixing.json` with each
  fixed ReLU and its native valid split, instead of rejecting. The run report
  sets `relu_phase_unfixed_before_solve` to false. Scenarios still reject
  fixed phases.
* Importer: strict record parsing, and an exact phase-premise search over the
  hull query. `Relu_Fix_*` steps go at the root, with the split bounds as
  ground bounds. The record is threaded through the source, sequence and
  query-file adapters.
* Four example files, with complete artifact sets and generated
  main-session theories: `phase_active_unsat`, `phase_inactive_unsat`,
  `phase_chain_unsat` (the root fix feeds two later native lemmas) and
  `phase_fixed_sat`. Without the record, none of the three UNSAT native
  proofs can be reconstructed.
* [test_marabou_phase_fixing.py](../Isabelle/tests/test_marabou_phase_fixing.py):
  11 tests.

### Native reruns

`refresh_native_fixtures.py --tag m23_refresh` exited 0 in 7.9 s. All ten
scenarios and the six earlier example files reproduced every saved data
artifact. Their run reports and solver logs are also byte-identical to the
milestone 22 reruns, so the harness change did not affect those runs. The
four new files saved their first artifact sets. Scratch builds of all four
generated sessions exited 0 (5–10 s each).

### Validation

```text
$ isabelle build -c -e -D Isabelle        (91 theories)
Finished Marabou_Verification (0:01:41 elapsed time, 0:07:41 cpu time, factor 4.55)
0:01:45 elapsed time, 0:07:41 cpu time, factor 4.39     exit 0

8 exported SML checker tests passed
72 exported SML proof-tree tests passed
11 exported SML assignment tests passed
16 exported SML inequality auxiliary tests passed      (all exit 0)

$ python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
Ran 290 tests in 2.314s
OK
```

The `build_log` Error/Warning filter was empty, and no forbidden proof or
axiom token occurs in any project theory. All 545 local links in 36 Markdown
files resolve and `git diff --check` is clean. The upstream checkouts are
clean at their pinned revisions and staging is empty.

### Assurance

A theorem about a phase-fixing file relies on the HOL kernel and the
build-time file check. The record, harness, solver and importer are
untrusted: a wrong record can only cause a rejection. Epsilon-decided phases
are rejected rather than approximated.

## Twenty-fourth milestone: checked native preprocessing

Completed on 2026-09-23. See [NATIVE_PREPROCESSING.md](NATIVE_PREPROCESSING.md).

### Work done

* HOL: [Preprocessing_Projection.thy](../Isabelle/Preprocessing_Projection.thy)
  defines checked facts and a projection:
  * the facts are implied bounds, ReLU hull rows, phase facts and the four
    ReLU rules (`fact`, `apply_facts`);
  * the projection (`check_projection`) requires every renamed row of a
    proposed preprocessed query to be exactly implied, and links each ReLU to
    an original ReLU up to proved equalities.

  Proved results: `apply_facts_models`, `check_projection_model`,
  `check_projection_unsatisfiable` and `check_projection_rejects_false_unsat`.
  The theory also has an `export_code ... checking SML` check.
* [Preprocessing_Projection_Examples.thy](../Isabelle/Preprocessing_Projection_Examples.thy)
  covers:
  * a merge, a fixed variable, tightening, renumbering and a ReLU link
    through the merge;
  * the ReLU fact kinds;
  * rejections of swapped renamings, over-tight bounds, missing link
    witnesses, foreign ReLUs and forged facts;
  * `snapped_projection_rejected`: a satisfiable query whose 10⁻⁵
    almost-fixed snapping would be UNSAT admits no accepted projection.
* Harness mode `file-preprocess`:
  * the reader accepts `le`/`ge` and missing bounds;
  * a standalone `Preprocessor::preprocess` exposes the preprocessed query
    (`_source.json`) and the variable maps (`_preprocessing.json`);
  * `processInputQuery(input, true)` must reproduce the same maps;
  * an `InfeasibleQueryException` in preprocessing is recorded as
    `result: "infeasible"` after the engine confirms UNSAT;
  * SAT solutions are extracted for the input variables.

  During development, a dangling reference (a range-for over a temporary
  query copy) crashed SAT runs; it was fixed before any capture was saved.
* [import_marabou_preprocessing.py](../Isabelle/tools/import_marabou_preprocessing.py)
  (untrusted):
  * HOL-mirroring native slack and ReLU auxiliary introductions;
  * exact re-derivation of the native tightenings as facts with witnesses;
  * projection witnesses (equality span with fixed variables, plus one
    inequality row), ReLU links and crossing-bound targets;
  * generated replay theories chaining introductions, projection, tableau
    steps and the native certificate.
* Driver and wrapper: `--preprocess`. The query-file adapter routes such runs
  and, in that mode only, relaxes the bound requirement. Provenance records
  the preprocessing importer and whether native preprocessing ran.
* Four examples with complete artifact sets and eight generated
  main-session theories:
  * `preprocess_split_unsat`: native split proof after tightening;
  * `preprocess_eliminate_unsat`: merge of the ReLU input, a fixed variable,
    renumbering;
  * `preprocess_inequality_unsat`: `le`/`ge`, missing bounds, refuted inside
    preprocessing;
  * `preprocess_mixed_sat`.
* [test_marabou_preprocessing.py](../Isabelle/tests/test_marabou_preprocessing.py):
  17 tests. The query-file tests now also cover the preprocessed examples'
  regeneration and provenance.

### Native reruns and end-to-end runs

`refresh_native_fixtures.py --tag m24_refresh` exited 0 in 9.9 s. All
earlier scenarios and example files reproduced every saved data artifact,
and the four new files saved their first artifact sets. With the final
tools, `verify_query_file.py --preprocess` on
`preprocess_eliminate_unsat.mqx` and `verify_query_file.py` on
`phase_chain_unsat.mqx` both exited 0 and printed
`Query_File_Theorem.query_file_unsatisfiable`. Earlier development runs
went through the same wrapper with `--preprocess` on
`solver_relu_split.mqx`, `relu_chain_unsat.mqx`,
`inequality_relu_unsat.mqx` (both refuted inside preprocessing) and
`relu_sat.mqx`. All exited 0; the two preprocessing-refuted runs did so
after the ordering fix described below.

The first generated theory for a preprocessing-refuted run used the crossing
query before its definition, so Isabelle rejected it. The template was
corrected before any fixture was saved.

### Validation

```text
$ isabelle build -c -e -D Isabelle        (101 theories)
Finished Marabou_Verification (0:02:23 elapsed time, 0:10:16 cpu time, factor 4.28)
0:02:27 elapsed time, 0:10:16 cpu time, factor 4.17     exit 0

8 exported SML checker tests passed
72 exported SML proof-tree tests passed
11 exported SML assignment tests passed
16 exported SML inequality auxiliary tests passed      (all exit 0)

$ python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
Ran 307 tests in 3.957s
OK
```

The `build_log` Error/Warning filter was empty, and no forbidden proof or
axiom token occurs in any project theory. All 593 local links in 37 Markdown
files resolve and `git diff --check` is clean. The upstream checkouts are
clean at their pinned revisions and staging is empty.
[PROJECT_THEORY_INVENTORY.md](PROJECT_THEORY_INVENTORY.md) now lists the 24
theories added after the audit snapshot.

### Assurance

A `--preprocess` theorem concerns the file's bytes. It relies on the HOL
kernel and the build-time file check, and says nothing about the
correctness of Marabou's preprocessor. It says that this run's preprocessed
query was exactly implied under the recorded renaming, and was refuted by
the native proof. Alternatively, it says that the run's infeasibility was
re-derived exactly. Results that depend on native tolerances are rejected.
Long derivations beyond the bounded search, network-level reasoning, and
removed redundant equations are unsupported.
