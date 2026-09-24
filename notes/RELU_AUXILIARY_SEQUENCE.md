# Finite checked ReLU introductions and a native two-ReLU replay

[ReLU_Auxiliary_Sequence.thy](../Isabelle/ReLU_Auxiliary_Sequence.thy)
composes finitely many [checked ReLU introductions](RELU_AUXILIARY.md).
An actual native capture now starts with two plain ReLUs and no auxiliary
rows. The generated
[Imported_Marabou_Native_Relu_Sequence.thy](../Isabelle/Imported_Marabou_Native_Relu_Sequence.thy)
proves its six-variable before-query UNSAT through two ReLU introductions,
five scalar-fixed tableau introductions, and the complete native proof.

This is a theorem about explicit rational data embedded into the existing
real semantics. It does not verify the C++ loop, extraction, JSON decoding
or general preprocessing.

## Checked finite composition

```isabelle
datatype relu_aux_step = ReLU_Aux_Step var var var "rat option"

rat_introduce_relu_aux_sequence ::
  "rat_query ⇒ relu_aux_step list ⇒ rat_query option"

check_after_relu_aux_sequence ::
  "rat_query ⇒ relu_aux_step list ⇒ fixed_aux_step list ⇒ certificate ⇒ bool"
```

The empty sequence returns the original query. Each nonempty step invokes
`rat_introduce_relu_aux` on the current query, then continues on its result.
ReLU membership, complete syntactic freshness, and any selected finite
lower-bound atom are checked again at each step. The defining equation and
bounds are constructed, never supplied by a purported result. A failure
returns `None` for the entire sequence.

| Theorem | Guarantee |
| --- | --- |
| `relu_aux_sequence_singleton` | A one-element sequence equals the existing single introduction. |
| `relu_aux_sequence_append` | Concatenation equals sequential composition through the successful intermediate query. |
| `relu_aux_sequence_failed_prefix` | Appending steps cannot repair a failed prefix. |
| `relu_aux_sequence_satisfiable_iff` | A successful sequence preserves existence of real models in both directions. The induction uses the single-step model-extension theorem. |
| `relu_aux_sequence_unsatisfiable_iff` | The corresponding UNSAT equivalence. |
| `check_after_relu_aux_sequence_empty/singleton` | Compatibility with the existing tableau-only and single-ReLU interfaces. |
| `check_after_relu_aux_sequence_sound` | Acceptance of ReLU steps, tableau steps and recursive certificate implies `unsatisfiable (embed_query Q)` for the original query. |
| `check_after_relu_aux_sequence_rejects_model` | A source with a real model cannot pass any combined sequence/certificate check. |

The soundness statement needs no external freshness, bound-validity or
solver-correctness assumption. It concerns real valuations; rational
certificate arithmetic does not restrict the valuation domain. No equality
of full model sets across new coordinates is asserted.

Both public sequence functions pass `export_code ... checking SML`.
The existing proof-tree datatype, inference rules, single-ReLU interface and
scalar-fixed sequence remain unchanged.

[ReLU_Auxiliary_Sequence_Examples.thy](../Isabelle/ReLU_Auxiliary_Sequence_Examples.thy)
checks a satisfiable sequence with negative and positive input lower bounds,
real source/result witnesses, late reuse of a previously fresh variable,
late false premises and wrong ReLU selection, and failure persistence.
It also checks a second fresh auxiliary for the same ReLU with no finite cap.
That last case is mathematically sound, although the native importer below
deliberately permits only one introduction per initially plain ReLU.

## Native query, calls and evidence

The accepted `relu_sequence` scenario has `b=x0, f=x1, c=x2, g=x3, z=x4, w=x5`:

```text
b - z = 0              c - z = 0              f + g - w = 0
f = ReLU(b)            g = ReLU(c)
-2 <= b,c <= 2         0 <= f,g <= 2
-2 <= z <= -1/2        1/4 <= w <= 2
```

Neither ReLU alone suffices for UNSAT. If the first is removed, the valuation
`b=c=z=-1/2, f=w=1/4, g=0` satisfies the remaining query. If the second is
removed, use `b=c=z=-1/2, g=w=1/4, f=0`. These models and the full query's
UNSAT are proved in `native_source_needs_both_relus`.

[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) constructs two
`ReluConstraint` objects without auxiliaries. Its
`introduce_native_relu_aux_sequence`:

1. Independently snapshots the complete six-variable query.
2. Calls `Preprocessor::informConstraintsOfInitialBounds` once.
3. Iterates over the two constraints and calls the actual
   `ReluConstraint::transformToUseAuxVariables` method for each, recording
   each successful allocation and its finite input lower bound.
4. Independently snapshots the complete eight-variable query after both calls.

The native calls create `a=x6` and `d=x7`, equations `f-b-a=0` and `g-c-d=0`,
and bounds `0<=a,d<=2`. The harness constructs none of those added atoms.
The source query then enters `Engine::processInputQuery(query,false)`.
The five proposed tableau steps are
`[(0,8),(1,9),(2,10),(3,11),(4,12)]`, producing thirteen variables.
The independent processed query and the proposed list are saved before
`Engine::solve(10)`.

The native proof has two explained PLC lemmas:

* Row 0 and existing bounds imply `b<=-1/2`, so `f<=0`.
* Row 1 and existing bounds imply `c<=-1/2`, so `g<=0`.

Its linear leaf uses row 2 and the output bounds to contradict `w>=1/4`.
The importer reconstructs exact linear premises and checks both output-upper
rules and the terminal contradiction. No lemma is filtered out.
All numbers in this accepted capture, including proof values, are dyadic.

The saved report records two native introductions, successful initialization,
both phases unfixed before solving, zero PLC lemmas before solving and two
afterwards, two main-loop iterations, one simplex step, zero tableau pivots,
one explained leaf, and no delegation or split. Proof production is enabled;
general preprocessing and DeepSoI are disabled. These runtime observations
are provenance, not verified C++ transitions.

Source correspondence, at Marabou revision
`1c2f4788c32e2f4e407c356b763a8025c5578722`:

| Source | Relation |
| --- | --- |
| `src/engine/Preprocessor.cpp::transformConstraintsIfNeeded`, lines 212–216 | Native loop invokes each constraint's transformation. The harness exercises the individual calls without invoking the full preprocessor. |
| `src/engine/Preprocessor.cpp::informConstraintsOfInitialBounds`, line 1121 | Supplies the constraint bound caches before both introductions. |
| `src/engine/ReluConstraint.cpp::transformToUseAuxVariables`, lines 936–978 | Allocates and appends each auxiliary equation and its bounds. |
| `src/engine/Engine.cpp::addAuxiliaryVariables/processInputQuery/solve` | Scalar-fixed columns, initialization, and native proof-producing solve. |
| `src/engine/ReluConstraint.cpp::notifyUpperBound`, input-to-output branch | Both accepted native ReLU lemmas. |
| `src/proofs/JsonWriter.cpp::writeProofToJson` | Serializes the complete solver-owned proof and header. |

## Import, artifacts and assurance

The accepted files have prefix
`Isabelle/tests/fixtures/marabou/solver_relu_sequence`:

| Suffix | Content |
| --- | --- |
| `_before_relu.json` | Existing `marabou-plain-relu-query-v1` with both plain ReLUs. |
| `_relu_steps.json` | New `marabou-relu-aux-sequence-v1` with ordered `steps`. Each has exactly `input`, `output`, `auxiliary` and finite `lower`. |
| `_source.json` | Independent result of both native calls, in existing source format. |
| `_steps.json` | Proposed scalar-fixed tableau sequence. |
| `_query.json` | Independent pre-solve processed query. |
| `.json` | Complete native writer proof. |

`_run.json`, `.log` and `_provenance.json` record observations and hashes of
all six data inputs, importers, capture code, compiled sources, binary and
libraries. Hashes are traceability data, not logical premises.

[import_marabou_relu_sequence.py](../Isabelle/tools/import_marabou_relu_sequence.py)
requires one introduction for every distinct plain ReLU, with a finite input
lower bound and allocation at the current variable count. It updates metadata
in the original constraint order, constructs all added atoms in execution
order, and compares the complete final result with the independent after-query.
Different execution order is supported when the allocations and result agree.
The parser uses exact rational decimal decoding and the existing resource
limits, with at most 256 introduction entries.

The generated HOL theory independently checks
`imported_relu_introductions_match_source` by `code_simp`, proves
`imported_relu_introductions_equisatisfiable` and
`imported_before_relu_processed_equisatisfiable`, and computes acceptance of
the full sequence/certificate combination.
`imported_before_relu_query_unsatisfiable` then follows from
`check_after_relu_aux_sequence_sound`. The old source/processed-query
obligations remain present, including the proved term-order equivalence.

At this milestone there were 51 project theories, 174 importer tests, 21 generated import
theories and sixteen accepted writer certificate files from nine component
fixtures and seven fully replayed native scenarios. All six earlier native
scenarios were rerun with the final shared harness: all their data artifacts
are unchanged, and their saved provenance describes those refreshed runs.
See [BUILD_RESULT.md](BUILD_RESULT.md).

## Previously rejected trial

An earlier exploratory query used `b=z, c=f-1/4, g=w` with the same variable
bounds. It produced an additional output-lower-to-auxiliary-upper PLC lemma
in `ReluConstraint::notifyLowerBound`. That rule was unsupported, so the whole
import was initially rejected. The unchanged seven JSON artifacts remain in
[rejected_relu_chain](../Isabelle/tests/fixtures/marabou/rejected_relu_chain/README.md)
with the historical directory name retained. The later
[positive-output milestone](RELU_OUTPUT_BOUND_PROPAGATION.md) verifies this
rule and replays the entire unchanged proof. A fresh `relu_chain` native run
reproduces its six data artifacts byte-for-byte and adds full provenance.
The original exploratory run used the binary directly; no full build/run
provenance is retroactively claimed for that earlier execution.

The checked rule is `0<l<=f` together with `f=ReLU(b)` and `a=f-b`
implies `a<=0`. Its linear premise and auxiliary equation are checked exactly.
Strict positivity matters: `f>=0` alone does not force `a=0`.
Other propagation rules, absent/infinite native bounds, full preprocessing,
verified extraction/decoding, and network-file correspondence remain separate.
UAT's existing sigmoid definition remains the documented future reuse point;
no sigmoid dependency or definition is added.

## Reproduction

Use a fresh output directory from the project root:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sequence --output /tmp/marabou-two-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-two-relu-capture
```

Replay the saved accepted evidence without C++:

```sh
python3 Isabelle/tools/import_marabou_relu_sequence.py \
  --before-relu Isabelle/tests/fixtures/marabou/solver_relu_sequence_before_relu.json \
  --relu-steps Isabelle/tests/fixtures/marabou/solver_relu_sequence_relu_steps.json \
  --source Isabelle/tests/fixtures/marabou/solver_relu_sequence_source.json \
  --steps Isabelle/tests/fixtures/marabou/solver_relu_sequence_steps.json \
  --query Isabelle/tests/fixtures/marabou/solver_relu_sequence_query.json \
  --certificate Isabelle/tests/fixtures/marabou/solver_relu_sequence.json \
  --output /tmp/marabou-two-relu-replay/Imported_Two_ReLUs.thy --session
isabelle build -d Isabelle -D /tmp/marabou-two-relu-replay
```
