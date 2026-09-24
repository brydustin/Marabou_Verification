# From a query file to an Isabelle theorem

Completed on 2026-09-23. This is roadmap item E of
[CLAUDE_HANDOFF.md](../CLAUDE_HANDOFF.md): one documented invocation takes a
supported exact query file, runs the unmodified native Marabou engine on the
query it reads, and ends with an Isabelle/HOL theorem about **the decoded
bytes of that file**, or with a stated rejection reason and no claim.

## Quick start

Prerequisites are those of [SOLVER_CAPTURE.md](SOLVER_CAPTURE.md) (CMake, a
C++17 compiler, GMP and Boost for the native harness) and Isabelle2025-2 with
the `Marabou_Verification` session buildable. From the project root:

```sh
python3 Isabelle/tools/verify_query_file.py Isabelle/examples/relu_chain_unsat.mqx /tmp/mqx-chain
```

On success it prints, for an UNSAT result,

```text
Isabelle checked Query_File_Theorem.query_file_unsatisfiable:
  decode_query query_file = Some Q ==> unsatisfiable (embed_query Q)
```

and for a SAT result `Query_File_Theorem.query_file_model`, stating that the
exactly reconstructed native assignment is a real model of the decoded query.
`query_file` is the exact byte content of `query.mqx` in the output directory,
a copy of the input file. The output directory must be new or empty.

The two steps can also be run separately:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --query-file Isabelle/examples/relu_sat.mqx --output /tmp/mqx-sat
isabelle build -d Isabelle -D /tmp/mqx-sat
```

With `--preprocess`, the run uses Marabou's own preprocessing; see
[NATIVE_PREPROCESSING.md](NATIVE_PREPROCESSING.md). Then `le`/`ge`
statements go to the native conversion, bounds may be missing, and a query
refuted inside preprocessing is still proved from an exact re-derivation.

```sh
python3 Isabelle/tools/verify_query_file.py --preprocess Isabelle/examples/preprocess_eliminate_unsat.mqx /tmp/mqx-pre
```

## What the theorem says and relies on

The theorem concerns `decode_query` applied to the file's bytes; its meaning
is fixed by [the exact text format](EXACT_QUERY_FORMAT.md). It does **not**
concern a neural-network file, a different number representation, or what the
C++ engine believed.

The chain of checks is:

1. `Exact_Query_Text.check_file` (build-time) fails unless the HOL byte list
   equals `query.mqx`; `external_file` makes Isabelle rebuild if it changes.
2. `query_file_decodes_like_capture` is proved by `code_simp`: the file's
   decoding has exactly the constraints (as sets) of the starting query the
   native run captured. Statement order, repetition and number spelling in
   the file may differ from the capture.
3. The replay theory proves, with the existing checked introductions and the
   exact certificate checker, UNSAT of that captured starting query, or, for
   SAT, that the exact assignment is a real model of it.
4. `decodes_like_unsatisfiable`/`decodes_like_model` transfer the result.

Trusted: the Isabelle/HOL kernel and the build-time file comparison (an ML
check that can only fail a build, never produce a theorem). Not trusted for
the theorem: the C++ `.mqx` reader, the native solver and its floating-point
arithmetic, the capture harness, the JSON import and the Python mirror checks.
A defect there can only cause a rejection.

## Supported inputs and rejection reasons

Beyond the format itself, the current pipeline requires:

| Requirement | Rejection message |
| --- | --- |
| `le`/`ge` statements are translated before the native run (see below); the native harness itself reads equalities only | `inequalities remain in the native input`, `missing finite bound for xK`, `no exact linear implication for the opposite slack bound` |
| At least one linear constraint | `at least one linear constraint is needed` |
| Every variable `x0 … x(n-1)` has exactly one finite `lower` and `upper` | `variable xK needs finite lower and upper bounds`, `each variable needs exactly one lower and one upper bound` |
| Every number is exactly a binary double, so the solver sees it unchanged | `number … is not exactly a binary double` |
| No variable repeated within an equation; distinct ReLU input and output | `repeated variable in an equation`, `a ReLU needs distinct input and output` |
| Every ReLU phase that the initial bounds fix must follow exactly from the query (see [RELU_PHASE_FIXING.md](RELU_PHASE_FIXING.md)) | `no exact justification for the … phase fixed before solving` |
| A result within 10 seconds | `solve returned neither SAT nor UNSAT within 10 seconds` |
| No delegated proof leaves | `native proof has delegated leaves (unsupported evidence)` |
| Evidence within the four supported ReLU lemma patterns and exact reconstruction | importer messages, e.g. `unsupported PLC lemma`, `no exact linear implication`, `exact constant` |
| For SAT, the reported doubles (or a bounded small-denominator repair) must be an exact model | `native assignment is not an exact model of the processed query, …` |

The Python pre-check reports the format and bound requirements before
anything is built; the C++ reader repeats them as a second line. Examples are
in [Isabelle/examples](../Isabelle/examples): `rejected_not_double.mqx`
(`0.1`) and `rejected_unbounded.mqx`.
A rejection says only that this pipeline produced no theorem.

**Inequalities.** A file with `le`/`ge` statements is first translated by the
untrusted [prepare_inequalities.py](../Isabelle/tools/prepare_inequalities.py)
into an equality-only *prepared* file. Each inequality gets a fresh signed
slack, as `Preprocessor::makeAllEquationsEqualities` would add, plus a finite
opposite bound (the *cap*) with an exact witness. The harness solves the
prepared file. The theorem theory proves by `code_simp` that the checked
steps turn the original file's decoding into the captured query, so the
theorem is still about the original bytes. See
[the inequality note](INEQUALITY_AUXILIARY.md#finite-slack-caps-and-the-file-workflow).
The earlier `rejected_inequality.mqx` is now accepted and was renamed
`inequality_linear_sat.mqx`.

## Examples and durable evidence

| File | Result | Main-session theory |
| --- | --- | --- |
| `relu_chain_unsat.mqx` — the chained two-ReLU query, statements reordered, decimals such as `-0.25` | UNSAT | `Imported_Marabou_Example_Relu_Chain_Unsat.query_file_unsatisfiable` |
| `relu_sat.mqx` — one ReLU forced active, one inactive | SAT | `Imported_Marabou_Example_Relu_Sat.query_file_model` |
| `linear_unsat.mqx` — no ReLU | UNSAT | `Imported_Marabou_Example_Linear_Unsat.query_file_unsatisfiable` |
| `inequality_relu_unsat.mqx` — one `le`, one `ge`, one ReLU | UNSAT | `Imported_Marabou_Example_Inequality_Relu_Unsat.query_file_unsatisfiable` |
| `inequality_relu_sat.mqx` — one `le`, one `ge`, one ReLU | SAT | `Imported_Marabou_Example_Inequality_Relu_Sat.query_file_model` |
| `inequality_linear_sat.mqx` — one `le`, no ReLU | SAT | `Imported_Marabou_Example_Inequality_Linear_Sat.query_file_model` |
| `phase_active_unsat.mqx` — ReLU phase fixed active by the initial bounds | UNSAT | `Imported_Marabou_Example_Phase_Active_Unsat.query_file_unsatisfiable` |
| `phase_inactive_unsat.mqx` — ReLU phase fixed inactive by the initial bounds | UNSAT | `Imported_Marabou_Example_Phase_Inactive_Unsat.query_file_unsatisfiable` |
| `phase_chain_unsat.mqx` — one fixed phase feeding two later native lemmas | UNSAT | `Imported_Marabou_Example_Phase_Chain_Unsat.query_file_unsatisfiable` |
| `phase_fixed_sat.mqx` — fixed active phase, satisfiable | SAT | `Imported_Marabou_Example_Phase_Fixed_Sat.query_file_model` |
| `preprocess_split_unsat.mqx` — `--preprocess`: tightened bounds, then a native split | UNSAT | `Imported_Marabou_Example_Preprocess_Split_Unsat.query_file_unsatisfiable` |
| `preprocess_eliminate_unsat.mqx` — `--preprocess`: merge, fixed variable, renumbering | UNSAT | `Imported_Marabou_Example_Preprocess_Eliminate_Unsat.query_file_unsatisfiable` |
| `preprocess_inequality_unsat.mqx` — `--preprocess`: `le`/`ge`, missing bounds, refuted inside preprocessing | UNSAT | `Imported_Marabou_Example_Preprocess_Inequality_Unsat.query_file_unsatisfiable` |
| `preprocess_mixed_sat.mqx` — `--preprocess`: `eq`/`le`/`ge`, fixed variable, missing bounds | SAT | `Imported_Marabou_Example_Preprocess_Mixed_Sat.query_file_model` |

Final runs of the first three files through the driver exited 0 and their
generated sessions built. Every snapshot, proof and assignment these file runs
produced is byte-identical to the corresponding hard-coded scenario fixture
(`relu_chain`, `relu_sat`, `linear`), which cross-checks the C++ reader. The
main session therefore reuses those replay theories and adds one theorem
theory per file, reading `Isabelle/examples/<file>.mqx` directly. Each file
run's report, log and provenance are kept as
`tests/fixtures/marabou/file_<example>_*`; tests check that the provenance
names the file's SHA-256 and the scenario artifacts' hashes.
The other files have no hard-coded counterpart. Their complete artifact sets
are saved, and the main session contains a generated replay theory for each.

[refresh_native_fixtures.py](../Isabelle/tools/refresh_native_fixtures.py)
reruns every native scenario and every example file. By default it requires
each rerun to reproduce every saved data artifact byte for byte. It then
replaces only the run reports, logs and provenance records. Provenance is
never edited by hand.

Adversarial checks:

* `Exact_Query_Format_Examples` proves that the reordered chain text matches
  the capture, while a changed bound, a dropped ReLU and an extra constraint
  do not.
* Python tests reject mutated files, mismatched artifact sets, tampered
  certificates and processed queries, bad theory names and file references,
  and unsupported files before any build.
* In scratch copies of a generated session, changing only `query.mqx` failed
  the build at the file check, and changing the file and the HOL byte list
  together failed the `decodes_like` proof.

## Reproduction

Pinned upstream: Marabou `1c2f4788c32e2f4e407c356b763a8025c5578722`
(unmodified). Regenerate the main-session example theories with
`python3 Isabelle/tools/import_marabou_query_file.py --examples Isabelle`.
A standalone session can be rebuilt from saved artifacts with
`python3 Isabelle/tools/import_marabou_query_file.py --query-file F.mqx
--artifacts DIR/solver_file --output NEWDIR`.
