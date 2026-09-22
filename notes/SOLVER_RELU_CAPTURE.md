# Solver-produced ReLU propagation, captured and replayed

Completed on 2026-09-22 with Isabelle2025-2 and unchanged Marabou revision
`1c2f4788c32e2f4e407c356b763a8025c5578722`.
[Imported_Marabou_Solver_Relu.thy](../Isabelle/Imported_Marabou_Solver_Relu.thy)
proves UNSAT of an explicit processed query using evidence produced by an
actual proof-enabled `Engine::solve` execution. The native certificate contains
one ReLU propagation lemma with a nonempty tableau explanation, followed by
one linear contradiction. The entire writer output is imported unchanged.
No mathematical checker rule or adapter acceptance condition was changed.

## Input and observed execution

The external [capture harness](../Isabelle/tools/solver_capture/capture.cpp)
supplies five variables, `b=x0, f=x1, z=x2, w=x3, a=x4`, with:

```text
b - z = 0
f - b - a = 0
f - w = 0
f = ReLU(b)

-1 ≤ b ≤ 2       0 ≤ f ≤ 2
-1 ≤ z ≤ -1/2    1/4 ≤ w ≤ 2
 0 ≤ a ≤ 1
```

The ReLU is supplied in Marabou's auxiliary form using
`ReluConstraint("relu,1,0,4")` and the displayed auxiliary equation. These are
query data, not proof evidence. The original input already includes this
auxiliary; automatic ReLU auxiliary introduction is not tested.

Proof production is enabled before engine construction. The native LP solver
is selected; preprocessing and DeepSoI are disabled. Initialization succeeds,
and the harness checks that the ReLU phase is still unfixed and the proof root
has no lemmas, children, or contradiction before calling `solve(10)`.

Native initialization appends three scalar-fixed tableau variables `s0=x5`,
`s1=x6`, `s2=x7`, all zero. The processed rows, in order, are:

```text
A0: b - z - s0 = 0
A1: -b + f - a - s1 = 0
A2: f - w - s2 = 0
```

The independently serialized pre-solve snapshot is compared with every entry
of the native tableau and every initial ground bound. The ReLU metadata in
the native JSON is `[0,1,4,6]`. The solver returns `UNSAT`, with one explained,
nondelegated leaf and exactly one PLC lemma. It records one explicit-basis
tightening call and zero simplex steps. There is no binary proof-tree split.
The main-loop counter is 2; as in the linear capture, it also counts the
pre-loop call to `mainLoopStatistics`.

The query bounds and row order matter for this narrow supported capture.
Exploratory versions with wider auxiliary bounds or `f=w` before the auxiliary
row also emitted an auxiliary-upper-bound lemma from
`ReluConstraint::notifyLowerBound`. At this milestone the importer rejected that
unsupported pattern. Selecting the displayed input isolates the supported
rule; the harness neither filters nor replaces solver evidence. This is a
known coverage limitation, not an observed incorrect solver answer.

The later [auxiliary extension](RELU_AUX_BOUND_PROPAGATION.md) now replays that
broader variant without changing its query or proof, and checks the necessary
auxiliary equation explicitly.

## Native evidence and exact reconstruction

The complete native lemma is:

```json
{"affVar":1, "affBound":"U", "bound":0.0,
 "causVar":0, "causBound":"U", "constraint":0,
 "expl":[{"var":0, "val":-1.0}]}
```

The explanation gives `e_b - A0 = e_z + e_s0`. Its ground-bound upper sum is
`-1/2 + 0 = -1/2`. The adapter reconstructs a checked linear implication:

```text
(b - z - s0) + (z + 1/2) + s0 = b + 1/2 ≤ 0.
```

The root only explicitly bounds `b ≤ 2`, so the explanation is necessary.
The ensuing checked ReLU step derives `f ≤ max(0,-1/2) = 0`.
The native terminal contradiction is row weight `1` on `A2`. Reconstruction
uses its negative equality row, the derived output bound, `w ≥ 1/4`, and
`s2 ≥ 0`:

```text
(-f + w + s2) + f + (1/4 - w) + (-s2) = 1/4 ≤ 0.
```

The resulting HOL certificate has this shape:

```isabelle
Linear_Bound (RatUpper 0 (-1/2)) premise_weights
  (Relu_Upper 0 1 (-1/2) 0 (Linear_Unsat leaf_weights))
```

`imported_certificate_checked` is proved by proof-producing `code_simp`.
`Imported_Marabou_Solver_Relu.imported_query_unsatisfiable` then follows from
`check_certificate_sound` over the existing real semantics.

[Solver_ReLU_Examples.thy](../Isabelle/Solver_ReLU_Examples.thy) separately
proves that the linear relaxation has the real witness
`(b,f,z,w,a,s0,s1,s2)=(-1/2,1/4,-1/2,1/4,3/4,0,0,0)`.
`captured_query_requires_nonlinear_evidence` proves that **no** linear-leaf
certificate can certify this root query. Thus the nonlinear step is essential,
not merely an unused lemma in an already inconsistent linear query.

## Source correspondence

All paths below are relative to `upstream/Marabou/`.

| Source and function | Role in this capture |
| --- | --- |
| `src/engine/ReluConstraint.cpp::ReluConstraint(String)` | Reads the supplied output/input/auxiliary variable indices. |
| `src/engine/Engine.cpp::processInputQuery`, `invokePreprocessor` | Initializes the supplied query with preprocessing disabled. |
| `Engine.cpp::selectInitialVariablesForBasis`, `addAuxiliaryVariables`, `initializeTableau` | Selects the native initial basis and appends scalar-fixed tableau variables. No formal correctness claim is made for these transformations. |
| `Engine.cpp::solve`, `explicitBasisBoundTightening`; `src/engine/RowBoundTightener.cpp::examineInvertedBasisMatrix`, `tightenOnSingleInvertedBasisRow` | Performs the native linear bound-tightening pass. |
| `src/engine/BoundManager.cpp::propagateTightenings` | Notifies variables in index order, lower bound before upper bound. |
| `ReluConstraint.cpp::notifyUpperBound`, negative input case | Generates the `b`-upper to `f`-upper lemma and fixes the inactive phase. |
| `BoundManager.cpp::addLemmaExplanationAndTightenBound`; `src/proofs/BoundExplainer.cpp::updateBoundExplanation/getExplanation` | Records the PLC conclusion and the native explanation of its linear premise. |
| `Engine.cpp::explainSimplexFailure`, `computeContradiction`, `writeContradictionToCertificate` | Produces the terminal row contradiction; this function name does not imply a simplex step occurred. |
| `src/proofs/JsonWriter.cpp::writeProofToJson/writePLCLemmas` | Serializes the engine-owned proof root directly. |

The exact interpretation of `e_x + wᵀA` and its comparison with
`UNSATCertificateUtils::computeBound` are documented in
[RATIONAL_LINEAR_IMPLICATION.md](RATIONAL_LINEAR_IMPLICATION.md).
The capture does not call Marabou's floating-point `Checker` or prune lemmas.

## Reproduction, artifacts, and validation

Use the local dependencies documented in [SOLVER_CAPTURE.md](SOLVER_CAPTURE.md).
From the project root, with a new or empty output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output /tmp/marabou-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-relu-capture
```

The driver checks the clean pinned source revision, builds the native embedding,
runs the scenario, and emits `Captured_Solver_Relu.thy` and a standalone ROOT.
The default `--scenario linear` preserves the earlier linear example.
No upstream source changes or automatic dependency downloads are performed.

Saved artifacts in [tests/fixtures/marabou](../Isabelle/tests/fixtures/marabou):

| File | Meaning |
| --- | --- |
| `solver_relu_query.json` | Independent processed-query snapshot written before solving. |
| `solver_relu.json` | Unmodified JSON writer output from the solver-owned proof. |
| `solver_relu_run.json` | Options, outcome, dimensions, pre/post lemma counts, phase check, and native counters. |
| `solver_relu.log` | Captured stdout/stderr. |
| `solver_relu_provenance.json` | Revision, source/script/library/binary hashes, compiler details, and artifact hashes. |

The query and proof matched byte-for-byte between exploratory successful
execution and final driver capture. The earlier linear scenario was rerun with
the final harness too: its query and proof were unchanged, and its saved
report/log/provenance now describe that new execution.

At this milestone the importer suite passed 68 tests, including eleven theory-regeneration
checks, both captures' provenance, removal/corruption of this lemma or its
explanation, an output bound too strong by `1/10^20`, a corrupted terminal
contradiction, and a relaxed satisfiable query. The main 28-theory session
and the standalone ReLU replay both build. See
[BUILD_RESULT.md](BUILD_RESULT.md) for exact commands and outputs.
The mathematical kernel, adapter, and exported checker definitions were
unchanged by this capture milestone.

## Assurance and next target

The new unconditional HOL theorem excludes every **real** valuation satisfying
the explicit decoded processed query. Evidence originated in a real solver
execution and its nonlinear inference is necessary for this query.
The capture program, JSON decoder, C++ execution, preprocessing, auxiliary
introduction, and original-query correspondence are not formally verified.
All serialized numbers used here are exact dyadics; this example does not
prove a general floating-point serialization property.

The smallest coverage extension suggested by the experiment was the auxiliary
rule `b ≥ l ⇒ a ≤ max(0,-l)`, under checked `f=ReLU(b)` and `f-b-a=0` premises.
That rule is now verified and imported in
[RELU_AUX_BOUND_PROPAGATION.md](RELU_AUX_BOUND_PROPAGATION.md), including replay
of the broader input variant with its extra native lemma. A solver-produced binary split
with both children replayed, and the bridge to original inputs, remain separate
targets.
