# First capture from a proof-producing solver execution

Completed on 2026-09-22 with Marabou
`1c2f4788c32e2f4e407c356b763a8025c5578722` and Isabelle2025-2.
An actual `Engine::solve` call generated the certificate replayed in
[Imported_Marabou_Solver_Linear.thy](../Isabelle/Imported_Marabou_Solver_Linear.thy).
The harness supplied the query, but did **not** construct its contradiction,
PLC lemmas, or proof nodes. Both upstream repositories remain unchanged.

## Query, execution, and checked result

The program constructs this tiny linear `InputQuery`:

```text
x = y
-2 ≤ x ≤ 1/4
1/2 ≤ y ≤ 2
```

`Engine::processInputQuery(input, false)` succeeds. Although preprocessing is
disabled, native initialization still introduces a tableau variable `z` fixed
to the equation's scalar, zero. The captured processed query is:

```text
x - y - z = 0
-2 ≤ x ≤ 1/4
1/2 ≤ y ≤ 2
z = 0
```

The call `Engine::solve(10)` returns false with exit code `UNSAT`. The captured
native certificate is a single visited, nondelegated leaf, with no PLC lemmas,
and row-combination weight `1` on original row 0. The harness checks these
conditions before passing the engine-owned root directly to `JsonWriter`.
It does not call the floating-point `Checker` or use its result as evidence.

The run report records one explicit-basis-tightening call, one explained leaf,
zero delegated leaves, zero simplex steps, and `NUM_MAIN_LOOP_ITERATIONS = 2`.
That last counter is incremented by `mainLoopStatistics`, including a call
before the loop; it is not a count of two completed loop bodies.
There are **no ReLUs, phase splits, or pivots in this example**.

The importer reconstructs:

```isabelle
Linear_Unsat [0, 1, 0, 1, 1, 0, 1, 0]
```

The selected normalized rows add as follows:

```text
(-x + y + z) + (x - 1/4) + (1/2 - y) + (-z) = 1/4.
```

All four rows must be nonpositive in a model, yielding the exact contradiction
`1/4 ≤ 0`. `imported_certificate_checked` is proved by `code_simp`, and
`Imported_Marabou_Solver_Linear.imported_query_unsatisfiable` follows from the
existing `check_certificate_sound` theorem. No checker rule was added or
weakened for this capture.

## Capture boundary and source correspondence

[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) uses public APIs only.
The processed query is copied and written **before** `solve`, independently of
the later certificate header. The harness also stores the initial engine state
and compares every captured matrix entry and ground bound with native state.
It rejects nonfinite numbers, duplicate columns, nonhomogeneous equations,
failed initialization, non-UNSAT exits, missing evidence, and delegated leaves.

| Pinned source | Role |
| --- | --- |
| `src/engine/InputQuery.{h,cpp}`, `Equation.{h,cpp}` | Constructs the two-variable query and its equality. |
| `src/configuration/Options.cpp`; `Engine.cpp::Engine` | Proof production is enabled before engine construction; native LP is selected. |
| `Engine.cpp::invokePreprocessor`, `processInputQuery` | The false flag skips preprocessing; initialization and initial constraint notification still occur. |
| `Engine.cpp::createConstraintMatrix`, `addAuxiliaryVariables` | Ordered query equations become tableau rows; a scalar-fixed variable is appended. |
| `Engine.cpp::getQuery`, `storeState`, `getGroundBound` | Public access used for the independent initial snapshot and runtime comparison. |
| `Engine.cpp::solve`, `explicitBasisBoundTightening`, `explainSimplexFailure` | Actual infeasibility search, bound tightening, and explanation path. The function name `explainSimplexFailure` does not imply a pivot occurred. |
| `Engine.cpp::computeContradiction`, `writeContradictionToCertificate`, `getUNSATCertificateRoot` | Native contradiction construction and read-only access to the resulting tree. |
| `src/proofs/JsonWriter.cpp::writeProofToJson` | Serializes that solver-owned root against the initial captured tableau and bounds. |

The normal CLI still has no found production call to `writeProofToJson`.
This project supplies an external embedding that calls it. The engine itself,
its real factories, and its proof-production code are compiled unchanged.
DeepSoI is disabled through its existing mutable configuration flag; there is
no network-level reasoner, Gurobi, OpenBLAS, parallel search, or network parser
in this execution.

## Reproduction and artifacts

The C++ embedding is built by
[CMakeLists.txt](../Isabelle/tools/solver_capture/CMakeLists.txt), separate from
upstream's top-level build so that CLI/ONNX dependency downloads are unnecessary.
It uses GCC 13.3.0, CMake 3.28.3, installed Boost 1.83 headers/thread library,
and GMP. Upstream's full CMake requests Boost 1.84; this narrower embedding uses
the locally available matching 1.83 headers and libraries, recorded in provenance.
There are no mock engine implementations.

Two missing runtime libraries were downloaded as Ubuntu packages and extracted
locally, without a system installation or upstream writes:

```sh
mkdir -p Isabelle/generated/solver_deps
cd Isabelle/generated/solver_deps
apt-get download libboost-program-options1.83.0=1.83.0-2.1ubuntu3.2 libboost-chrono1.83.0t64=1.83.0-2.1ubuntu3.2
dpkg-deb -x libboost-program-options1.83.0_1.83.0-2.1ubuntu3.2_amd64.deb root
dpkg-deb -x libboost-chrono1.83.0t64_1.83.0-2.1ubuntu3.2_amd64.deb root
cd ../../..
```

Package SHA-256 values:

* Program Options: `9e7c21160a9cf2e8847b0789bba7a2b3301a4846f0f999270b41b424afb37559`.
* Chrono: `cffb0d834e57190a04c60afc02906837570fc8a3eb560e51243a334a303d5c1d`.

With these dependencies available, use a new or empty output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --output /tmp/marabou-solver-capture
isabelle build -d Isabelle -D /tmp/marabou-solver-capture
```

The driver verifies the clean pinned checkout, builds the native embedding,
runs it with a process timeout, reconstructs the certificate, records hashes,
and emits `Captured_Solver_Linear.thy` plus a standalone session. It does not
download dependencies or silently replace an existing capture directory.
The normal `isabelle build -D Isabelle` needs no C++ build or extra libraries.

The saved files in [tests/fixtures/marabou](../Isabelle/tests/fixtures/marabou) are:

| File | Origin |
| --- | --- |
| `solver_linear_query.json` | Independent snapshot of `getQuery()` before solving. |
| `solver_linear.json` | Unedited upstream writer output from the solver-produced certificate. |
| `solver_linear_run.json` | Captured options, outcomes, dimensions, native counters, and runtime snapshot checks. |
| `solver_linear.log` | Captured stdout/stderr from the final execution. |
| `solver_linear_provenance.json` | Pinned revision, compiled-source hashes, compiler command/version, linked-library hashes, binary hash, and artifact hashes. |

The query and certificate agreed byte-for-byte across the capture runs.
Source/provenance and negative-control tests are included in the importer
suite. In particular, corrupting the row weight or relaxing the fixed
auxiliary bound rejects the proof. All imported theories match regeneration.
See [BUILD_RESULT.md](BUILD_RESULT.md) for exact Isabelle build results.

The later ReLU milestone extended the harness with `--scenario relu`.
The linear case remains the default and was rerun with the final shared
harness; the saved query and proof are identical to this first capture, while
its report/log/provenance now record the refreshed execution.

## Assurance and next target

This is the first replay of **solver-produced** evidence in this project.
Its unconditional HOL theorem excludes every real valuation of the explicit
processed query. The C++ execution, capture program, JSON decoder, provenance
hashes, and relation to the original `InputQuery` are not themselves verified.
All numbers in this example are exactly representable dyadics; that observation
does not establish a general serialization theorem. No correctness theorem
about Marabou, simplex, preprocessing, or a neural-network input is claimed.

The proposed ReLU propagation integration is now completed in
[SOLVER_RELU_CAPTURE.md](SOLVER_RELU_CAPTURE.md), using an unedited certificate
with a nonempty linear explanation and a necessary nonlinear inference.
Solver-produced binary splitting and the original-query bridge, starting with
verified auxiliary introduction, remain separate targets.
