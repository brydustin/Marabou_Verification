# Captured source queries and checked auxiliary introductions

The capture harness now saves the pre-initialization query and a proposed
finite introduction list alongside its independent processed snapshot and
native proof. The new importer emits HOL data for all four artifacts.
Isabelle proves source/processed equisatisfiability and source-query UNSAT.
The five existing solver scenarios have all been executed again with this
capture path; their processed-query and proof bytes remain unchanged.

This replaces the hand-written HOL source and step inputs used in the earlier
[sequence example](TABLEAU_AUXILIARY_SEQUENCE.md). The C++ harness still
constructs small test queries explicitly. These are actual solver executions,
not neural-network file imports.

## Capture and source correspondence

The unchanged upstream checkout is Marabou
`1c2f4788c32e2f4e407c356b763a8025c5578722`.
[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) uses this order:

1. Construct the test `InputQuery`.
2. Before constructing the engine, `snapshot_source` obtains an owned copy
   using `src/engine/InputQuery.cpp::generateQuery`. That implementation copies
   the equations and bounds and duplicates constraints without preprocessing.
   The snapshot preserves addend order and nonzero equation scalars.
3. Call `Engine::processInputQuery(input, false)`. Require proof production,
   successful initialization, disabled preprocessing, and an empty proof root.
4. `snapshot` records the processed query independently of the proof header.
   Compare it with `Engine::storeState` and `Engine::getGroundBound`.
5. `snapshot_steps` finds each row's newly added variable: one distinct new
   column with coefficient `-1` per source row, with unchanged row count and
   the expected dimension increase. Write the proposed `(row, variable)` list.
6. Call `Engine::solve` and pass its unmodified proof root to
   `src/proofs/JsonWriter.cpp::writeProofToJson`. Preserve both split children.

The introduction list is recovered from observed added columns by our harness.
It is **not a native transformation event log**. No scalar or intermediate
query is supplied by the list. The verified transformation computes those
from the source query. Exact agreement with the entire processed record is
a separate HOL proof obligation.

The intended transformation is the one in
`src/engine/Engine.cpp::addAuxiliaryVariables`: replace `e=b` by `e-s=0` and
fix both bounds of fresh `s` to `b`. The initialization path can perform other
operations, including redundant-row removal. No theorem about those operations
is assumed; a changed result that cannot be produced by the checked list is
rejected. `Query::getEquations/getPiecewiseLinearConstraints` provide the copied
data. `Engine::createConstraintMatrix` and `JsonWriter::writeInitialTableau`
use matrix column order, motivating the explicitly proved term permutation.

Both upstream repositories remain unmodified. The external harness creates
no certificate nodes, PLC lemmas, or contradictions.

## Four input artifacts

For every `solver_<scenario>` prefix in
[the fixture directory](../Isabelle/tests/fixtures/marabou):

| Suffix | Contents |
| --- | --- |
| `_source.json` | Version `marabou-source-query-v1`, variable count, typed equality rows with ordered addends and scalar, finite lower/upper bounds, and existing ReLU metadata `[b,f,a]`. Written before initialization. |
| `_steps.json` | Version `marabou-fixed-aux-sequence-v1` and ordered objects `{"equation": i, "variable": s}`. Written before solving. |
| `_query.json` | Independent processed tableau, bounds, and ReLU metadata `[b,f,a,h]`. Written before solving. |
| `.json` | Complete native JSON proof, including its processed-query header. Written after solving. |

The `_run.json` report records capture timing flags and introduction count.
The `_provenance.json` adds hashes of the source, steps, and new importer to
the existing build, source, binary, query, proof, report, and log hashes.
These hashes identify artifacts; they are not logical premises or a verified
attestation of execution.

The source schema currently supports only equalities, full finite bound
arrays, and existing auxiliary-form ReLUs (or no ReLUs). It rejects unsupported
fields, types and activations. The source's ReLU auxiliary `a`, its equation,
and its bounds are already supplied by the test input. This milestone
introduces only scalar-fixed tableau auxiliaries `h`.

All source and processed numbers in these five captures are exact dyadics.
In general, import interprets decimal tokens as exact rationals, not as their
nearest binary doubles. The existing auxiliary-proof token `1.750002` retains
its exact rational interpretation. No general floating-point serialization
theorem is claimed.

## Import and HOL obligations

[import_marabou_source.py](../Isabelle/tools/import_marabou_source.py) reuses
the strict numeric parser and proof reconstruction in
[import_marabou_json.py](../Isabelle/tools/import_marabou_json.py).
It retains the original source and also proposes a column-ordered copy.
It checks each introduction against the current query, requires the complete
constructed query to equal the independent processed query, and then invokes
the existing recursive proof adapter. It also checks matching ReLU metadata;
that metadata supplies no unproved linear equation.

The same file-size and numeric-token limits apply as in the existing adapter:
4,000,000 bytes per JSON file, at most 256 variables and 512 rows; this adapter
also limits the proposed list to 256 steps. These are import limits, not
restrictions of the HOL sequence theorem. No duplicate sparse indices,
missing bounds, failed steps, or approximate matches are accepted.

Each generated `Imported_Marabou_Source_*` theory proves:

| Theorem | Guarantee |
| --- | --- |
| `imported_source_term_order` | The original and reordered source have identical satisfaction under every real valuation, proved by algebraic simplification. |
| `imported_steps_match_query` | Executing the checked sequence yields exactly the independent processed query record, proved by `code_simp`. |
| `imported_certificate_checked` | The existing recursive checker accepts the processed query and certificate, proved by `code_simp`. |
| `imported_source_certificate_checked` | The composed introduction/certificate checker accepts the reordered source. |
| `imported_source_equisatisfiable` | The captured source and processed query are equisatisfiable over real valuations. |
| `imported_query_unsatisfiable` / `imported_source_query_unsatisfiable` | Neither explicit embedded query has a real model. The latter uses `check_after_fixed_aux_sequence_sound` and the proved reordering equivalence. |

No new trusted primitive, axiom, unchecked transformation, or solver-correctness
assumption was added. The existing logical checker and soundness theorems are
unchanged. Python acceptance only prepares proof obligations; a successful
Isabelle build establishes them. JSON decoding and C++ extraction remain
unverified, so the unconditional theorems concern the explicit generated HOL
data. They do not certify arbitrary original files or all Marabou executions.

## Captures and reproduction

| Scenario | Source variables | Introductions | Processed variables | Native nonlinear evidence |
| --- | ---: | ---: | ---: | --- |
| `linear` | 2 | 1 | 3 | None; one linear leaf. |
| `relu` | 5 | 3 | 8 | One explained output-upper lemma. |
| `relu_aux` | 5 | 3 | 8 | Auxiliary-upper and output-upper lemmas. |
| `relu_aux_active` | 5 | 3 | 8 | One explained auxiliary-upper lemma. |
| `relu_split` | 9 | 5 | 14 | One binary split; both linear children replay. |

The split list is `[(0,9),(1,10),(2,11),(3,12),(4,13)]`. Its source has the
four nonzero scalars `1/4` and final scalar zero, with the last row recorded
in original order `f-b-a`. Its source theorem is
`Imported_Marabou_Source_Relu_Split.imported_source_query_unsatisfiable`.
At this milestone there were fourteen saved proof files; five additional
source replay theories reuse the five native certificates. The subsequent
[native ReLU introduction capture](NATIVE_RELU_INTRO_CAPTURE.md) adds a sixth
solver scenario and one combined replay theory.

Run a fresh capture into a new directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_split --output /tmp/marabou-source-capture
isabelle build -d Isabelle -D /tmp/marabou-source-capture
```

Or import the four saved files without rebuilding or running C++:

```sh
python3 Isabelle/tools/import_marabou_source.py \
  --source Isabelle/tests/fixtures/marabou/solver_relu_split_source.json \
  --steps Isabelle/tests/fixtures/marabou/solver_relu_split_steps.json \
  --query Isabelle/tests/fixtures/marabou/solver_relu_split_query.json \
  --certificate Isabelle/tests/fixtures/marabou/solver_relu_split.json \
  --output /tmp/marabou-source-replay/Imported_Source.thy --session
isabelle build -d Isabelle -D /tmp/marabou-source-replay
```

The main session contains all five generated source replays. This milestone's
122-test importer suite included byte-for-byte regeneration of all nineteen
generated theories, provenance checks, source/step substitution, late failure
and freshness collisions, corrupted children, and a coherently relaxed
satisfiable source/processed query that rejects the old certificate.
See [BUILD_RESULT.md](BUILD_RESULT.md) for actual commands and build results.

The proposed semantic target is now proved in
[RELU_AUXILIARY.md](RELU_AUXILIARY.md): one checked fresh ReLU auxiliary,
its optional upper cap, model extension/projection, and SAT/UNSAT equivalence.
For `relu_aux`, it connects an explicit earlier four-variable HOL query to the
saved source and existing native proof. The subsequent
[six-artifact capture/import](NATIVE_RELU_INTRO_CAPTURE.md) now records the
before-query and actual native ReLU introduction as well as these four
artifacts. The base source format above continues to describe the query after
the ReLU auxiliary exists. General preprocessing and verified byte decoding
remain separate tasks.

[Finite ReLU introductions](RELU_AUXILIARY_SEQUENCE.md) now extend that
capture path to two plain ReLUs, retaining these same four downstream
artifacts. All source/processed transformation and proof obligations remain
checked; native extraction and the full preprocessing loop remain unverified.
