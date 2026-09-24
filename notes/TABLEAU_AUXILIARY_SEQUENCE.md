# Finite sequences of checked tableau auxiliaries

The single-step transformation now composes over any finite list of proposed
introductions. Successful composition preserves satisfiability and
unsatisfiability over the existing real semantics. Each step checks the query
produced by the preceding step; any failure rejects the whole sequence.

The five introductions for the existing binary ReLU split capture produce
exactly its saved processed query. Replaying the existing native certificate
therefore proves UNSAT of an explicit nine-variable pre-tableau query.
That first example uses hand-written HOL source and step data. The subsequent
[source capture/import milestone](SOURCE_QUERY_CAPTURE.md) now obtains both
automatically from fresh executions and replays the bridge in generated theories.

## Executable interface and theorems

[Tableau_Auxiliary_Sequence.thy](../Isabelle/Tableau_Auxiliary_Sequence.thy)
adds:

```text
fixed_aux_step = nat × var
rat_introduce_fixed_aux_sequence ::
  rat_query ⇒ fixed_aux_step list ⇒ rat_query option
check_after_fixed_aux_sequence ::
  rat_query ⇒ fixed_aux_step list ⇒ certificate ⇒ bool
```

A pair `(i,s)` selects an equality by its zero-based list index and proposes
the new variable. The empty list returns the original query. A nonempty list
calls `rat_introduce_fixed_aux`, then continues on its returned query. Thus
each index, equality type, scalar, and freshness check uses the current query.
Every intermediate query is constructed by verified definitions.

A new variable must be absent from every component of the current query,
including auxiliaries added by earlier steps. Repeating an equation index
with a different fresh variable is permitted: that is a valid mathematical
transformation, although the native loop processes each equation once.
The later step reads the already transformed equation's scalar, which is zero.

| Theorem | Guarantee |
| --- | --- |
| `fixed_aux_sequence_singleton` | A singleton sequence is exactly the earlier checked single-step function. |
| `fixed_aux_sequence_append` | Running concatenated lists equals running the first list and then the second on its successful result; failure propagates. |
| `fixed_aux_sequence_failed_prefix` | No suffix can turn a failed prefix into a successful sequence. |
| `fixed_aux_sequence_satisfiable_iff` | If a sequence returns `Some P`, `embed_query P` and `embed_query Q` are equisatisfiable. Proof: induction using the single-step theorem. |
| `fixed_aux_sequence_unsatisfiable_iff` | Successful sequences preserve UNSAT in both directions. |
| `check_after_fixed_aux_sequence_empty/singleton` | The composed checker agrees with the existing certificate checker on an empty list and the single-step wrapper on a singleton. |
| `check_after_fixed_aux_sequence_sound` | Acceptance implies `unsatisfiable (embed_query Q)` for the source query. |
| `check_after_fixed_aux_sequence_rejects_model` | A source query with a real model admits no accepted sequence/certificate pair. |

The wrapper checks the terminal certificate only after every transformation
succeeds. Its soundness theorem has no caller-supplied freshness, scalar, or
solver-correctness premise. The existing certificate datatype and recursive
checker are unchanged. Both new functions pass Isabelle's Standard ML
compilation check; concrete computations use proof-producing `code_simp`.

## Five-step connection to the binary-split capture

[Tableau_Auxiliary_Sequence_Examples.thy](../Isabelle/Tableau_Auxiliary_Sequence_Examples.thy)
defines `solver_split_input_query` with the actual term order from the
`relu_split` branch of
[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp). Writing
`x0,…,x8 = b,f,a,t,u,p,q,r,s`, its equations are:

```text
f - t - p = 1/4
f + t - q = 1/4
a - u - r = 1/4
a + u - s = 1/4
f - b - a = 0
```

It also contains `f=ReLU(b)` and the nine variables' original finite bounds,
as recorded in [SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md).
The ReLU auxiliary `a=x2` and its equation are already part of this input.
This sequence introduces only the scalar-fixed tableau variables:

| Equality index | New variable | Fixed scalar |
| --- | --- | --- |
| 0 | 9 | 1/4 |
| 1 | 10 | 1/4 |
| 2 | 11 | 1/4 |
| 3 | 12 | 1/4 |
| 4 | 13 | 0 |

The snapshot writes terms in variable-index order. Its last row therefore
uses `-b+f-a`, while the supplied input uses `f-b-a`.
`solver_split_column_query` makes that one ordering change, and
`solver_split_term_order_semantics` proves pointwise real-semantic
equivalence. No unproved reordering is hidden in the auxiliary checker.

The explicit step list is:

```text
[(0,9), (1,10), (2,11), (3,12), (4,13)]
```

`solver_split_sequence_matches_snapshot` checks that applying it to
`solver_split_column_query` returns exactly
`Imported_Marabou_Solver_Relu_Split.imported_query`. This is equality of the
entire query record, including all equations, bounds, ReLUs, and list order.
`solver_split_source_equisatisfiable` combines that equality, sequence
preservation, and the term-order proof.

`solver_split_before_aux_checked` replays the existing `Relu_Split`
certificate, with both native linear children, after the five introductions.
`solver_split_before_aux_unsatisfiable` applies the composed checker's
soundness theorem and the term-order equivalence to prove UNSAT of the
originally ordered nine-variable HOL query.

## Inspected source and assurance boundary

Marabou remains pinned at `1c2f4788c32e2f4e407c356b763a8025c5578722`:

* `upstream/Marabou/src/engine/Engine.cpp::addAuxiliaryVariables`, line 1290,
  assigns new variable `originalN+count` to each equation in order. For this
  query, `originalN=9` and there are five equations. It appends coefficient
  `-1`, fixes both bounds to the old scalar, then sets the scalar to zero.
* `Isabelle/tools/solver_capture/capture.cpp::main`, `relu_split` branch,
  supplies the input equations and bounds. Its `snapshot` function writes
  tableau coefficients by increasing column index before solving.
* `upstream/Marabou/src/proofs/JsonWriter.cpp::writeProofToJson` writes the
  saved native tableau and solver-owned tree. These existing proof/query
  files and their provenance were not changed.

The mathematical composition is verified. C++ loop refinement, allocation,
floating-point execution, preprocessing, row removal, snapshot extraction,
and JSON decoding are not. The full source query and step list are explicitly
reviewable HOL definitions, not automatically extracted input evidence.
This theorem does not yet certify an original neural-network file.

## Validation and next target

Examples check the exact five-step result, reuse of a newly introduced
variable, a late out-of-range index, collision with an original variable,
failure propagation, and rejection of the saved certificate after an empty
or incomplete introduction list. Replacing either terminal child with an
empty linear certificate is rejected after a successful five-step sequence.

A satisfiable example processes the same equation twice with different
fresh variables. The second variable is correctly fixed to the current
scalar zero, while the first remains fixed to `3/4`. Both the source and
result have explicit real models. The general model-rejection corollary
excludes every purported UNSAT certificate/sequence for that source.

At the sequence milestone the session had 39 theories and all 96 importer
tests passed. The subsequent capture/import extension has 44 theories and
122 tests, retaining the same fourteen certificate files. Run:

```sh
isabelle build -D Isabelle
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

Exact outputs are in [BUILD_RESULT.md](BUILD_RESULT.md).
The proposed integration target is now completed in
[SOURCE_QUERY_CAPTURE.md](SOURCE_QUERY_CAPTURE.md). Five fresh native runs
emit source queries and proposed introduction lists alongside their independent
processed snapshots and proofs. Generated HOL checks the complete constructed
result and proves each source UNSAT.
[One fresh ReLU auxiliary](RELU_AUXILIARY.md) is now also verified and composed
with this sequence and the existing native proof. Capturing/importing that
native ReLU step is the next small integration target; general preprocessing
and verified decoding remain open.
