# Solver-produced binary ReLU split

This capture uses the unchanged Marabou checkout at
`1c2f4788c32e2f4e407c356b763a8025c5578722`. A real proof-enabled
`Engine::solve` execution creates one binary ReLU split and closes both
children. Its complete native JSON proof replays through the existing importer
and Isabelle checker. No checker rule or import rule was added for this capture.

## Input and processed query

The `relu_split` scenario in
[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) supplies nine variables:

| Index | Name | Bounds |
| --- | --- | --- |
| 0 | b | -1 ≤ b ≤ 1 |
| 1 | f | 0 ≤ f ≤ 1 |
| 2 | a | 0 ≤ a ≤ 1 |
| 3, 4 | t, u | -1 ≤ t,u ≤ 1 |
| 5, 6, 7, 8 | p, q, r, s | 0 ≤ p,q,r,s ≤ 2 |

The five input equations, in order, are

```text
f - t - p = 1/4
f + t - q = 1/4
a - u - r = 1/4
a + u - s = 1/4
f - b - a = 0
```

with `f = ReLU(b)`. The auxiliary-form constraint is supplied explicitly using
`ReluConstraint(String("relu,1,0,2"))`, together with its defining equation;
this experiment does not test ReLU auxiliary introduction by preprocessing.
The first pair of equations implies `f ≥ |t|+1/4`, excluding the inactive
phase; the second pair implies `a ≥ |u|+1/4`, excluding the active phase.
The initial interval bounds alone do not fix the phase.

`processInputQuery(input, false)` succeeds with the phase still unfixed.
Although preprocessing is disabled, `Engine::addAuxiliaryVariables` appends
five tableau variables `h0=x9,…,h4=x13`. The first four are fixed at `1/4`
and `h4` at zero. The pre-solve snapshot has these homogeneous rows:

```text
A0 = f - t - p - h0 = 0
A1 = f + t - q - h1 = 0
A2 = a - u - r - h2 = 0
A3 = a + u - s - h3 = 0
A4 = -b + f - a - h4 = 0
```

The ReLU metadata is `[0,1,2,13]`. The harness independently writes the
initialized query before solving and compares every row, finite bound, and
dimension with `Engine::storeState/getGroundBound`. The theorem is about
this explicit fourteen-variable processed query.

## Native search and captured evidence

Settings are native LP, proof production on, preprocessing off, DeepSoI off,
seed 1, and a ten-second solve limit. The existing
`Options::CONSTRAINT_VIOLATION_THRESHOLD` is set to 1 for this scenario.
`Engine::performConstraintFixingStep` reports the violation before attempting
repair; `SearchTreeHandler::reportViolatedConstraint` then requests splitting.
The harness does not call `performSplit` or construct/modify a proof node,
contradiction, or PLC lemma.

Source paths below are relative to `upstream/Marabou/`:

| Observed operation | Source correspondence |
| --- | --- |
| Violation reporting and main search | `src/engine/Engine.cpp::performConstraintFixingStep/reportPlViolation/solve`; `src/engine/SearchTreeHandler.cpp::reportViolatedConstraint` |
| Threshold configuration | `src/configuration/Options.cpp`; `SearchTreeHandler::SearchTreeHandler` reads the configured threshold |
| Native phase choices | `src/engine/ReluConstraint.cpp::getCaseSplits/getActiveSplit/getInactiveSplit` |
| Child creation, first branch, and state save | `src/engine/SearchTreeHandler.cpp::performSplit` constructs `UnsatCertificateNode` children, stores engine state, and calls `Engine::applySplit` |
| Backtracking to the remaining child | `SearchTreeHandler::popSplit`; `Engine::restoreState` and context hooks |
| Terminal explanations | `src/engine/Engine.cpp::explainSimplexFailure`; `src/proofs/Contradiction` and `UnsatCertificateNode` |
| Pivot counter | `src/engine/Tableau.cpp::performPivot/performDegeneratePivot`; `src/common/Statistics.h::NUM_TABLEAU_PIVOTS` |
| Serialization | `src/proofs/JsonWriter.cpp::writeProofToJson/writeUnsatCertificateNode/writeHeadSplit/writeContradiction` |

The saved [run report](../Isabelle/tests/fixtures/marabou/solver_relu_split_run.json)
records:

| Observation | Value |
| --- | --- |
| `solve(10)` / exit code | false / UNSAT |
| Main-loop iterations / simplex-step calls | 12 / 9 |
| Tableau pivots | 3 |
| Explicit-basis tightening calls | 3 |
| Search splits / pops / maximum depth | 1 / 2 / 1 |
| Root children / explained leaves / delegated leaves | 2 / 2 / 0 |
| PLC lemmas before solving / in final tree | 0 / 0 |

Simplex-step calls are not pivot counts. These counters and native-state
observations are provenance, not premises of any HOL theorem.
The harness checks that both children were visited, have no SAT/delegation
flag, contain no children or PLC lemmas, and have terminal contradictions.
It also checks exactly one native active split and one native inactive split.

The writer emits inactive first:

```text
root
  inactive: b ≤ 0, f ≤ 0
    native contradiction: 1*A0 + 1*A1
  active:   b ≥ 0, a ≤ 0
    native contradiction: 1*A2 + 1*A3
```

Each exact contradiction has margin `1/2`. For example, the inactive
combination is
`-(A0+A1) + 2f - p - q + (1/4-h0) + (1/4-h1) = 1/2`.
Every summand is nonpositive under its phase and root constraints. The
active calculation replaces `f,p,q,h0,h1` by `a,r,s,h2,h3`.

## Exact replay and assurance

HOL uses canonical phases: active `b≥0, f-b=0` and inactive `b≤0, f=0`,
removing the selected ReLU and retaining the other root constraints.
The importer identifies phases from their bounds, then stores active before
inactive in `Relu_Split`. It reconstructs native `a≤0` from the active
equality, `A4=0`, and `h4≥0`: `a = -h4 ≤ 0`. This bound is not admitted
as an extra assumption merely because it appears in the native split.
Both final nonnegative row combinations are checked over the canonical
child queries.

[Imported_Marabou_Solver_Relu_Split.thy](../Isabelle/Imported_Marabou_Solver_Relu_Split.thy)
contains the generated query and `Relu_Split 0 1 (Linear_Unsat …) (Linear_Unsat …)`.
`imported_certificate_checked` uses proof-producing `code_simp`;
`imported_query_unsatisfiable` applies `check_certificate_sound`.
[Solver_ReLU_Split_Examples.thy](../Isabelle/Solver_ReLU_Split_Examples.thy)
separately checks and proves UNSAT for each canonical child.

That examples theory also proves the linear relaxation satisfiable using
`b=0, f=a=1/2, t=u=0, p=q=r=s=1/4, h0=h1=h2=h3=1/4, h4=0`.
Consequently `captured_split_requires_nonlinear_evidence` excludes every
linear-leaf certificate of the unsplit root.

The resulting unconditional theorems exclude every real valuation of the
explicit rational queries. They do not verify the C++ execution, pivoting,
backtracking, capture program, JSON decoder, or correspondence with an
original network input. All numbers in this capture are exact dyadics;
no general claim about decimal/binary serialization follows.
No solver soundness failure was observed in this experiment.

## Artifacts and reproduction

The five saved files under `Isabelle/tests/fixtures/marabou/` are
`solver_relu_split_query.json`, `solver_relu_split.json`,
`solver_relu_split_run.json`, `solver_relu_split.log`, and
`solver_relu_split_provenance.json`. Query and proof SHA-256:

```text
query: df27a42e43fb65767777bef0387d056e340afbce25f371f75e516153d7b1cfcb
proof: 0d5c334f385d725ea28430bb756dc3546ccd4b50459d7bb5cb562fc7d6ecac19
```

The provenance records the pinned revision, compiler, linked libraries,
compiled source hashes, capture/import scripts, binary, and saved outputs.
All four earlier solver scenarios were rerun with the final shared harness;
their query/proof bytes stayed identical, and their reports and provenance
were refreshed from those actual executions.

From the project root, use a new output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_split --output /tmp/marabou-relu-split
isabelle build -d Isabelle -D /tmp/marabou-relu-split
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
isabelle build -D Isabelle
```

At this milestone there were 34 project theories, 14 imported certificates, and five actual
solver captures. The 96 importer tests include missing/corrupted children,
duplicated phases, swapped contradictions, stronger phase assumptions, and
removing the auxiliary tableau premise. Relaxing either phase's positive
offsets admits an explicit exact model and causes rejection even though the
other phase remains inconsistent. Reversing native child order preserves the
reconstructed certificate. See [BUILD_RESULT.md](BUILD_RESULT.md) for builds.

## Next smallest semantic target

The proposed single-step target is now proved in
[TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md): replace `e=b` by `e-s=0` and
`s=b` with checked global freshness, model extension/projection, and an exact
connection for the earlier linear capture.
[TABLEAU_AUXILIARY_SEQUENCE.md](TABLEAU_AUXILIARY_SEQUENCE.md) now composes
the five steps for this capture and proves its explicit pre-tableau query
UNSAT, including a proved term-order equivalence.
[SOURCE_QUERY_CAPTURE.md](SOURCE_QUERY_CAPTURE.md) now captures and imports
that source and step list automatically alongside the processed query and
native proof. Generated HOL proves the complete bridge and source UNSAT.
[One fresh ReLU auxiliary introduction](RELU_AUXILIARY.md) is now proved
separately and applied to the earlier auxiliary-propagation capture.
Its [native capture/import](NATIVE_RELU_INTRO_CAPTURE.md) now records and
checks one actual transformation call.
[Finite composition and a two-ReLU capture](RELU_AUXILIARY_SEQUENCE.md) are
now completed too; other preprocessing steps remain separate.
