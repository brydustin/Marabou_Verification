# Checked inequality-to-equality conversion

This milestone verifies one fresh signed slack introduction and finite
sequences of those introductions. It composes them with the existing ReLU
and scalar-fixed introductions and the UNSAT certificate checker. A checked
assignment to the transformed query also gives a real model of the original.

The examples in this milestone are hand-written HOL data. A later step,
described [below](#finite-slack-caps-and-the-file-workflow), checks the other
finite slack bound as well and connects `le`/`ge` files to the native file
workflow. That route uses a local, checked translation. It does not run
Marabou's own preprocessing.

## Source correspondence and sign convention

Inspected Marabou revision:
`1c2f4788c32e2f4e407c356b763a8025c5578722`.

`src/engine/Preprocessor.cpp::makeAllEquationsEqualities`, lines 224–244,
iterates over non-equality equations, allocates a new variable, changes the
equation type to equality and appends coefficient **+1**. For `GE` it sets
the auxiliary upper bound to zero; otherwise it sets its lower bound to zero.
`Preprocessor::preprocess` invokes this before subsequent bound tightening
and elimination. The method is private in `Preprocessor.h`.

Thus the mathematical steps are:

| Original atom | Replacement and new bound | Extension value |
| --- | --- | --- |
| `e ≤ b` | `e + s = b`, `s ≥ 0` | `s = b − e` |
| `e ≥ b` | `e + s = b`, `s ≤ 0` | `s = b − e` |

The GE convention differs from using a nonnegative slack with coefficient
`−1`. We follow the actual native convention. Neither direction supplies
a finite bound on the slack's other side.

The HOL expressions may contain an affine constant and repeated or zero
coefficients; the native equation has no separate affine constant. Selection
is by list index, preserving other atoms and duplicate occurrences. Global
freshness includes all syntactic variable occurrences, even zero coefficients,
unrelated bounds and ReLU-only variables. C++ allocation and mutations are
not verified by these theorems.

## Definitions and guarantees

| Theory / theorem | Guarantee |
| --- | --- |
| [Inequality_Auxiliary.thy](../Isabelle/Inequality_Auxiliary.thy), `introduce_inequality_aux` | Replace one selected inequality with its equality and signed zero bound. |
| `satisfies_introduce_inequality_aux_iff` | The transformed models are exactly the original models additionally satisfying `s=b−eval(e)`. Requires correct index/selection; this characterization does not require freshness. |
| `inequality_aux_model_extension` | With freshness, assigning the slack its residual extends every original real model. |
| `inequality_aux_model_projection` | A transformed model projects back, with arbitrary reset of the fresh variable. |
| `satisfiable_introduce_inequality_aux_iff` and its UNSAT counterpart | With checked selection and freshness, SAT and UNSAT are preserved in both directions. |
| [Rational_Inequality_Auxiliary.thy](../Isabelle/Rational_Inequality_Auxiliary.thy), `rat_introduce_inequality_aux` | Check index, inequality type and freshness. Read the direction/expression/scalar from the query and construct the result; only index and proposed fresh name come from evidence. |
| `embed_rat_inequality_aux_query` | The rational operation embeds exactly into the original real transformation. |
| `rat_introduce_inequality_aux_model` / `rat_introduce_inequality_aux_satisfiable_iff` | Successful exact steps imply model projection and real equisatisfiability. |
| [Inequality_Auxiliary_Sequence.thy](../Isabelle/Inequality_Auxiliary_Sequence.thy) | Finite lists of proposals check each intermediate query; failed prefixes remain failures. |
| `inequality_aux_sequence_model` / `inequality_aux_sequence_satisfiable_iff` | Finite checked composition preserves projection and real satisfiability. |
| `check_after_inequality_aux_sequence_sound` | Checked inequalities, ReLU introductions, scalar-fixed tableau steps and an accepted certificate imply real-semantic UNSAT of the original query. |
| `check_assignment_after_inequality_aux_sequence_sound` | An exact assignment accepted after checked inequality steps is a real model of the original query. |
| `inequality_relu_fixed_assignment_satisfiable` | An exact model after all three introduction stages implies SAT of the original query. |

The input interface is:

```isabelle
rat_introduce_inequality_aux Q atom_index fresh_variable
rat_introduce_inequality_aux_sequence Q [(atom_index, fresh_variable), ...]
check_after_inequality_aux_sequence Q inequality_steps relu_steps tableau_steps cert
check_assignment_after_inequality_aux_sequence Q inequality_steps assignment
```

There is no separate certificate constructor for this transformation inside
the proof tree. As with the earlier introductions, it is a checked step before
the tree is interpreted. Failed or malformed introductions cannot be bypassed
by a successful certificate for some other query.

## Examples and negative checks

[Inequality_Auxiliary_Examples.thy](../Isabelle/Inequality_Auxiliary_Examples.thy)
contains:

* Affine rational expressions, repeated terms, a zero coefficient, a repeated
  inequality and an unrelated equality and ReLU.
* Both signed directions, exact transformed-query equality, a SAT witness and
  a zero-slack boundary witness.
* Invalid indices, equality proposals, collisions across every query component,
  reused slacks and repeated/already-transformed indices.
* A satisfiable query made inconsistent by an unchecked bound-only name
  collision; the checked interface rejects the collision.
* A satisfiable GE query that an incorrect nonnegative slack would refute;
  the constructed correct sign rejects that false refutation.
* Two checked inequalities closing with an exact linear contradiction.
* A ReLU query refuted after two inequality steps, one ReLU introduction and
  three fixed tableau introductions, followed by a checked linear premise,
  ReLU propagation and a linear leaf. Its linear relaxation has a proved
  real model, so nonlinear evidence is necessary.
* A theorem about a hand-written `le`/`ge` byte string decoded with the
  existing HOL decoder. This is not a native file-run theorem.

The generated module `Marabou_Inequality_Preprocessor.ML` includes the
executable interfaces. Its separate
[smoke script](../Isabelle/tests/inequality_auxiliary_smoke.ML) checks signs,
freshness, late failures, exact SAT witnesses and UNSAT composition.
These runtime checks supplement the HOL proofs; they are not proof premises.
Poly/ML reports three non-exhaustive-match warnings for generated library
helpers (`nth`, `image` and set union). The exported functions guard every
indexed selection and construct their variable sets from finite lists.
The helpers and set constructors are not exported; review found no reachable
missing case through this interface. Invalid indices and fresh-name collisions
are also exercised by the smoke tests. The generated file is not hand-edited.

## Review of the inherited development

Claude's milestones 17–20 were already complete when continuation resumed:
positive-auxiliary propagation, exact SAT witnesses, the HOL text decoder
and the restricted file-to-theorem command. The inherited baseline built
successfully with 67 theories and all 262 Python tests passed.

Review covered the new propagation proof, assignment evaluation/embedding
and lifting, the decoder and round-trip structure, constraint-set transfer,
the ML file comparison and its `external_file` dependency, the query-file
adapter and CLI, and the continuation/build records. No soundness defect was
identified in those examined parts; this is not an exhaustive independent
audit of every line. The decoder's meaning is the HOL definition. Connecting
that byte list to a disk file still uses the documented build-time file check.

At the time, the pre-check error message could name a log directory that
did not yet exist. That has since been fixed: the driver names the directory
only if a build log exists, and `DriverTests` checks this. No shared
capture/importer code or saved provenance was altered during this
mathematical milestone.

See [BUILD_RESULT.md](BUILD_RESULT.md) for final build, execution and audit
results, and [CONTINUATION_LOG.md](CONTINUATION_LOG.md) for continuation state.

## Finite slack caps and the file workflow

With general preprocessing disabled, the native engine rejects any variable
without finite bounds, and the fresh slack from the table above has only one
signed zero bound. [Bounded_Inequality_Auxiliary.thy](../Isabelle/Bounded_Inequality_Auxiliary.thy)
therefore adds a *cap*: after the introduction it adds the opposite bound
(`s ≤ c` for LE, `s ≥ c` for GE). The cap is kept only if an exact linear
implication from the transformed query proves it. The witness is checked by
`check_linear_bound` before the bound is added.

| Theorem | Guarantee |
| --- | --- |
| `bounded_inequality_step_model`, `bounded_inequality_step_satisfiable_iff` | A checked step (introduction plus proved cap) preserves real models backwards and real satisfiability in both directions. |
| `bounded_inequality_sequence_*` | The same for finite checked sequences; a failed prefix fails the whole sequence. |
| `bounded_decodes_like`, `bounded_decodes_like_unsatisfiable`, `bounded_decodes_like_model` | If a file's decoded query, after the checked steps, has the constraints of a captured query, then UNSAT or an exact model of the captured query transfers to the decoded file. |

[Bounded_Inequality_Examples.thy](../Isabelle/Bounded_Inequality_Examples.thy)
accepts exact and weaker caps. It rejects unjustified caps, bad variables or
indices, missing or negative weights and late sequence failures. It also shows
a satisfiable query that an unchecked cap `s ≤ 0` would falsely refute; no
checked sequence can make that query unsatisfiable.

[prepare_inequalities.py](../Isabelle/tools/prepare_inequalities.py) is an
untrusted proposer. For each inequality, in order, it picks the next unused
variable as the slack. It computes the cap by interval arithmetic over the
variables' finite bounds and writes the matching witness. If the interval
already contradicts the inequality, it weakens the cap to include zero. It
then encodes the equality-only *prepared* file. The capture driver runs this
before the native harness, which reads only the prepared file. The generated
theorem theory reads the original bytes:

```text
bounded_decodes_like query_file inequality_steps captured_starting_query
```

This is proved by `code_simp`, so HOL rechecks each slack, cap and witness.
The prepared file is not trusted; the importer also refuses one that
differs from the checked steps.

| Example | Result | Main-session theories |
| --- | --- | --- |
| `inequality_relu_unsat.mqx`: `x0 ≤ −1`, `x1 ≥ 1`, `x1 = ReLU(x0)` | UNSAT | `Imported_Marabou_Prepared_Inequality_Relu_Unsat`, `Imported_Marabou_Example_Inequality_Relu_Unsat` |
| `inequality_relu_sat.mqx`: `x0 ≤ 1`, `x1 ≥ 1/2`, `x1 = ReLU(x0)` | SAT | `Imported_Marabou_Prepared_Inequality_Relu_Sat`, `Imported_Marabou_Example_Inequality_Relu_Sat` |
| `inequality_linear_sat.mqx`: `x0 − x1 ≤ 0`, no ReLU | SAT | `Imported_Marabou_Prepared_Inequality_Linear_Sat`, `Imported_Marabou_Example_Inequality_Linear_Sat` |

The third file was the workflow's earlier `rejected_inequality.mqx`. It is
now accepted, so it was renamed. Each example's complete native artifact
set is saved as `Isabelle/tests/fixtures/marabou/file_<example>_*`.
[test_bounded_inequality.py](../Isabelle/tests/test_bounded_inequality.py) and
[test_marabou_query_file.py](../Isabelle/tests/test_marabou_query_file.py)
check that preparation is deterministic, the evidence schema is strict and
mutated files, prepared files, caps and witnesses are rejected. They also
check that the saved evidence is bound together, the theories regenerate
exactly and provenance matches the saved runs and current tools.

Assurance: the theorems concern the original file bytes. The Python
preparation, the C++ reader, the solver and the JSON import are all untrusted.
Native `Preprocessor::makeAllEquationsEqualities` is *not* executed on this
route. The later [native preprocessing mode](NATIVE_PREPROCESSING.md) runs
the real conversion inside Marabou's preprocessor. It reuses the checked
introductions above, with the native slack numbers, and checks the rest of
the preprocessing result independently.
