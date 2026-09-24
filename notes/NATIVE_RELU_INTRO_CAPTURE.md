# Capturing and replaying a native ReLU auxiliary introduction

The `relu_intro` scenario runs the actual upstream
`ReluConstraint::transformToUseAuxVariables` method on a query without a ReLU
auxiliary. It captures the query before and after the call, initializes the
engine, and captures its processed query and complete UNSAT proof.
[Imported_Marabou_Native_Relu_Intro.thy](../Isabelle/Imported_Marabou_Native_Relu_Intro.thy)
checks the introduction and proves that the explicit query captured **before**
the call is UNSAT over real valuations.

This uses the existing [verified ReLU introduction](RELU_AUXILIARY.md),
scalar-fixed sequence, and recursive proof checker. No new logical rule or
soundness assumption was added. The C++ extractor and JSON decoder remain
unverified.

## Actual native execution

Marabou revision: `1c2f4788c32e2f4e407c356b763a8025c5578722`.
Both upstream repositories remain unmodified.

The input has variables `b=x0, f=x1, z=x2, w=x3`:

```text
b - z = 0              f - w = 0              f = ReLU(b)
-2 <= b <= 2           0 <= f <= 2
-2 <= z <= -1/2        1/4 <= w <= 2
```

The external harness
[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) performs these steps:

1. Construct `ReluConstraint(0,1)`, with no pre-existing auxiliary, and obtain
   an owned `Query` through `InputQuery::generateQuery`.
2. `snapshot_source` writes the entire four-variable query before bound
   notifications or introduction. `IQuery::generateQuery` supplies an owned
   copy for readout; no source equations are inferred from the later tableau.
3. Call `Preprocessor::informConstraintsOfInitialBounds`, then call
   `ReluConstraint::transformToUseAuxVariables` exactly once. The native method
   creates `a=x4`, appends `f-b-a=0`, and sets `0<=a<=2`. The harness does not
   construct that row or those bounds in this scenario.
4. Save the introduction record and independently snapshot the entire result.
   Pass that five-variable query to `Engine::processInputQuery(query,false)`.
5. Capture the eight-variable processed query and the proposed scalar-fixed
   sequence `[(0,5),(1,6),(2,7)]` before solving. Compare the query snapshot
   with the native tableau and ground bounds.
6. Run `Engine::solve(10)` and serialize the unchanged native proof root with
   `JsonWriter::writeProofToJson`.

Relevant upstream source:

| Source/function | Role |
| --- | --- |
| `src/engine/ReluConstraint.{h,cpp}::ReluConstraint/auxVariableInUse/getB/getF/getAux` | Plain constraint construction and public introduction metadata. |
| `src/engine/ReluConstraint.cpp::transformToUseAuxVariables`, lines 936–978 | Native allocation, defining equation, lower bound and input-dependent upper cap. |
| `src/engine/Preprocessor.cpp::informConstraintsOfInitialBounds`, line 1121 | Populate constraint bound caches from the query before transformation. |
| `src/engine/InputQuery.cpp::generateQuery` and `Query.cpp::generateQuery` | Owned query copies used for transformation/readout. |
| `src/engine/Engine.cpp::processInputQuery/addAuxiliaryVariables/solve` | Initialization, scalar-fixed tableau columns, and solving. |
| `src/proofs/JsonWriter.cpp::writeProofToJson` | Native proof serialization after solving. |

This is a direct public-API call to the transformation, preceded by its normal
bound-notification helper. The general preprocessing pipeline is disabled.
The native method reads a constraint cache, while the HOL checker requires an
explicit query bound. Complete before/after matching checks the observed
result; no theorem about cache synchronization is assumed.

The saved report records 4 → 5 → 8 variables, successful initialization,
proof production enabled, DeepSoI disabled, two main-loop iterations, zero
simplex steps/pivots, zero PLC lemmas before solving, two afterwards, one
explained leaf and no delegation. The two native lemmas propagate an input
lower bound to an auxiliary upper bound and an input upper bound to an output
upper bound; both have nonempty tableau explanations.

The after-query, scalar steps, processed query and proof happen to be
byte-identical to the older `relu_aux` scenario. Their provenance here is a
new execution that began without the ReLU auxiliary. There are now fifteen
saved native-writer proof files, six actual solver scenarios, and twenty
generated replay theories; this does not mean fifteen distinct proof contents.

## Six independently supplied artifacts

The files use prefix `Isabelle/tests/fixtures/marabou/solver_relu_intro`.

| Suffix | Format and content |
| --- | --- |
| `_before_relu.json` | `marabou-plain-relu-query-v1`: four variables, equality rows, full finite bound arrays, and plain ReLU metadata `[b,f]`. |
| `_relu_step.json` | `marabou-relu-aux-introduction-v1`: exactly `input`, `output`, `auxiliary`, and finite `lower`, besides `format`. This capture records `0,1,4,-2`. |
| `_source.json` | Existing `marabou-source-query-v1`: independent five-variable result, with `[b,f,a]` metadata. |
| `_steps.json` | Existing `marabou-fixed-aux-sequence-v1`: proposed scalar-fixed steps. |
| `_query.json` | Independent processed tableau snapshot with `[b,f,a,h]` metadata. |
| `.json` | Complete native `JsonWriter` output, including processed-query header. |

The ReLU record describes a call actually made by the harness; it is not an
upstream proof-format extension. The scalar-fixed list is still a harness
proposal recovered from added columns. Neither record is trusted as a logical
premise. `_run.json`, `.log`, and `_provenance.json` record observations and
hashes of all six inputs, the importers, capture code, compiled sources,
binary, and libraries. Hashes provide traceability, not a proof of execution.

[import_marabou_relu_intro.py](../Isabelle/tools/import_marabou_relu_intro.py)
accepts exactly one plain ReLU, an explicit finite input lower bound, a fresh
auxiliary at the old variable count, equality rows, and full finite bound
arrays. It reconstructs the new row, nonnegative bound, and cap `max(0,-l)`.
It requires the entire reconstructed query to match the independent after
snapshot, including unchanged old atoms and ReLU metadata. It then invokes
the existing source/step/proof importer. No supplied cap or metadata equation
is accepted on trust.

Malformed/unknown fields, unsupported operations, inconsistent dimensions,
changed old atoms, invalid premises, freshness collisions, incorrect results,
and unsupported/invalid proof evidence reject. The shared bounded strict JSON
parser decodes decimals as exact rationals. These query values are dyadic;
the proof token `1.750002` is checked as `875001/500000`, a weaker auxiliary
upper bound than `7/4`, without claiming equality to its C++ binary double.

## Isabelle guarantees

The generated theory retains the after-source and processed-query obligations
from the [source importer](SOURCE_QUERY_CAPTURE.md), and adds:

| Theorem | Guarantee |
| --- | --- |
| `imported_relu_introduction_matches_source` | The guarded rational introduction on the explicit before-query produces exactly the independently captured after-source record; proved by `code_simp`. |
| `imported_relu_introduction_equisatisfiable` | The before/after queries have equivalent existence of real models, by the existing introduction theorem. |
| `imported_before_relu_processed_equisatisfiable` | The original four-variable and final eight-variable queries are equisatisfiable. |
| `imported_before_relu_certificate_checked` | The composed ReLU introduction, three tableau introductions and recursive proof checker accept; proved by `code_simp`. |
| `imported_before_relu_query_unsatisfiable` | No real valuation satisfies the explicit before-query, by `check_after_relu_aux_sound`. |

All guards are discharged by computation. There is no solver-correctness
hypothesis. At this milestone the main session had 48 theories; all proofs
were checked with `quick_and_dirty=false`. The 146 Python tests included 24 new introduction
tests, regeneration of all twenty imported theories, and provenance for all
six scenarios. One coherent relaxation has an explicit rational model of
before, after and processed queries; replay rejects its old proof at an
overstrong PLC conclusion. These deliberately altered inputs are negative
controls, not observed solver failures.

## Reproduction and remaining scope

From the project root, using a fresh output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_intro --output /tmp/marabou-native-relu-intro
isabelle build -d Isabelle -D /tmp/marabou-native-relu-intro
```

Replay the saved artifacts without running C++:

```sh
python3 Isabelle/tools/import_marabou_relu_intro.py \
  --before-relu Isabelle/tests/fixtures/marabou/solver_relu_intro_before_relu.json \
  --relu-step Isabelle/tests/fixtures/marabou/solver_relu_intro_relu_step.json \
  --source Isabelle/tests/fixtures/marabou/solver_relu_intro_source.json \
  --steps Isabelle/tests/fixtures/marabou/solver_relu_intro_steps.json \
  --query Isabelle/tests/fixtures/marabou/solver_relu_intro_query.json \
  --certificate Isabelle/tests/fixtures/marabou/solver_relu_intro.json \
  --output /tmp/marabou-native-relu-replay/Imported_Native_ReLU.thy --session
isabelle build -d Isabelle -D /tmp/marabou-native-relu-replay
```

The assurance concerns explicit embedded HOL queries. C++ execution,
extraction, JSON decoding, general preprocessing, floating-point refinement
and correspondence to network files remain unverified. The HOL introduction
also supports absence of a finite lower bound, but this importer does not.
This capture exercises a negative lower bound and one fresh ReLU; the positive,
zero and missing-bound cases have HOL examples, not native captures here.

[Finite checked composition](RELU_AUXILIARY_SEQUENCE.md) and the native
two-ReLU capture are now completed. That extension adds a separate sequence
importer, preserves this single-call interface, and proves both ReLUs necessary
for its new example. The subsequently
[verified positive-output rule](RELU_OUTPUT_BOUND_PROPAGATION.md) also enables
complete replay of the preserved chained trial and a fresh matching capture.
