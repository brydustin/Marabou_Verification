# One verified scalar-fixed tableau auxiliary

This milestone proves one conservative extension over the existing real query
semantics. A selected equality `e=b` is replaced by `e-s=0`, with bounds
`b≤s` and `s≤b`. If `s` occurs nowhere in the original query, every original
model extends by assigning `s=b`, and every resulting model projects back.
SAT and UNSAT are therefore preserved.

The executable rational interface checks the index, equality constructor, and
freshness. It constructs the result itself. Composing it with the existing
certificate checker now proves UNSAT of an explicit source query before this
one transformation.

## Source correspondence

Audited Marabou revision: `1c2f4788c32e2f4e407c356b763a8025c5578722`.
Paths below are relative to `upstream/Marabou/`:

| Source | Observed implementation | Formal counterpart / limit |
| --- | --- | --- |
| `src/engine/Engine.cpp::addAuxiliaryVariables`, line 1290 | Reserves `m` variables after `originalN`, assigns `auxVar=originalN+count` to each equation, appends `(-1,auxVar)`, fixes both bounds to the old scalar, then sets the scalar to zero. | `introduce_fixed_aux` formalizes one selected equation. The finite loop, variable-count allocation, unsigned arithmetic, and C++ mutation are not verified. |
| `Engine.cpp::createConstraintMatrix`, line 1061 | Rejects remaining non-equalities with `NON_EQUALITY_INPUT_EQUATION_DISCOVERED`. | The checked step accepts only `RatEq`; inequalities elsewhere in the query are retained. |
| `Engine.cpp` native initialization, around line 1470 | Creates the matrix, removes redundant equations, selects initial basis variables, calls `addAuxiliaryVariables`, and initializes the tableau. | This theorem covers only the auxiliary step, not preceding row removal or subsequent tableau construction. |
| `src/engine/Query.cpp::setLowerBound/setUpperBound`, lines 56/70 | Checks the variable-count range, then assigns entries in bound maps. | HOL adds two bound atoms. Freshness ensures there are no old bounds on the new variable. Bound-map storage and serialization order are outside the theorem. |
| `src/engine/Equation.{h,cpp}::addAddend/setScalar` | Stores coefficient/variable terms and the right-hand scalar as doubles. | Exact real arithmetic in the semantic theorem; exact rational data in the executable interface. No floating-point refinement is assumed. |

In proof mode `addAuxiliaryVariables` also updates `_lastAddendToAux`.
This bookkeeping is not modeled or treated as evidence. The selected equality
and complete query are explicit HOL data.

The HOL expression language allows an affine constant, repeated variables,
and zero coefficients. The theorem covers these cases. Marabou's `Equation`
has no separate left-hand constant; the direct counterpart has constant zero.
With an affine constant, the transformed HOL row has right-hand side zero but
need not be homogeneous. No normalization of arbitrary C++ containers is claimed.

## Definitions and proved contract

[Tableau_Auxiliary.thy](../Isabelle/Tableau_Auxiliary.thy) defines syntactic
variable sets for expressions, linear constraints, bounds, ReLUs, and queries.
`query_vars` includes every mentioned variable, including zero-coefficient
terms. This is a sufficient, deliberately conservative freshness test.
Congruence lemmas prove that query satisfaction depends only on these variables.

`introduce_fixed_aux Q i s e b` replaces the atom at zero-based index `i`
with `LinearEq (e-s) 0` and appends `Lower s b, Upper s b`. It retains all
other atoms and their order, including duplicate copies of the selected
equation. Its theorems explicitly require `i < length (linear_atoms Q)` and
`linear_atoms Q ! i = LinearEq e b`. The raw function is not a checked API.

| Theorem | Guarantee |
| --- | --- |
| `satisfies_introduce_fixed_aux_iff` | Under valid selection, `v` satisfies the result iff it satisfies `Q` and `v s=b`. This pointwise fact does not require freshness. |
| `models_introduce_fixed_aux` | The result's full valuation set is `{v∈models Q. v s=b}`. It is not asserted equal to the original full valuation set. |
| `fixed_aux_model_extension` | Under freshness, `v(s:=b)` satisfies the result iff `v` satisfies `Q`. Every other variable retains its value. |
| `fixed_aux_model_projection` | Under freshness, a result model gives an original model even after resetting `s` to any real value. |
| `satisfiable_introduce_fixed_aux_iff` | Under valid selection and freshness, original and result are equisatisfiable. |
| `unsatisfiable_introduce_fixed_aux_iff` | Under the same conditions, UNSAT of either query implies UNSAT of the other. |

[Rational_Tableau_Auxiliary.thy](../Isabelle/Rational_Tableau_Auxiliary.thy)
provides:

```text
rat_introduce_fixed_aux :: rat_query ⇒ nat ⇒ var ⇒ rat_query option
check_after_fixed_aux :: rat_query ⇒ nat ⇒ var ⇒ certificate ⇒ bool
```

The first returns `None` for an out-of-range index, a non-equality at that
index, or any variable collision anywhere in the query. Otherwise it reads
the selected equality's expression and scalar and constructs the result.
An externally supplied transformed query, scalar, or freshness flag is not
trusted. `rat_introduce_fixed_aux_Some_iff` characterizes success exactly.
`query_vars_embed` and `embed_rat_fixed_aux_query` prove correspondence with
the real definitions. Success implies real-semantic SAT/UNSAT equivalence.

The second function applies this checked step and then `check_certificate`
to the constructed query. Its central theorem is:

```text
check_after_fixed_aux Q i s cert
  ⟹ unsatisfiable (embed_query Q)
```

`check_after_fixed_aux_sound` has no unchecked freshness or solver-correctness
premise. It follows from the step's equivalence and `check_certificate_sound`.
The existing certificate datatype and recursive checker are unchanged.
The new executable interface compiles to Standard ML via `export_code …
checking SML`; concrete acceptance proofs use kernel-checked `code_simp`.

## Connection to the existing linear capture

[Tableau_Auxiliary_Examples.thy](../Isabelle/Tableau_Auxiliary_Examples.thy)
defines `solver_linear_before_aux`:

```text
x0 - x1 = 0
-2 ≤ x0 ≤ 1/4
1/2 ≤ x1 ≤ 2
```

These exact literals match the `linear` scenario in
[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp). This is a
hand-written HOL description of that input, not a verified C++ decoder.
`solver_linear_aux_matches_snapshot` computes:

```text
rat_introduce_fixed_aux solver_linear_before_aux 0 2
  = Some Imported_Marabou_Solver_Linear.imported_query
```

The equality checks the full result record, including atom and bound order.
It introduces `x2=0` into the single equation, giving exactly the earlier
captured processed query. `solver_linear_before_aux_checked` accepts its
existing solver-produced certificate `Linear_Unsat [0,1,0,1,1,0,1,0]`
through the new wrapper. `solver_linear_before_aux_unsatisfiable` then proves
UNSAT of the explicit two-variable source query.

This is a verified connection between these two explicit HOL queries. It
does not establish a general correspondence between network bytes, C++ input
objects, and HOL queries. No new solver execution or fixture is claimed;
the saved evidence and its provenance are unchanged.

## Boundary examples and validation

The examples prove extension of a real model for an affine equation with
scalar `3/4`, repeated variable terms, a zero coefficient, a duplicate equation,
an unrelated inequality and bound, and a ReLU. The original witness assigns
the unused new variable `17`; extension changes it to `3/4`. The unextended
witness does not satisfy the result, illustrating why full model-set equality
would be wrong.

Proof-producing computations also cover a negative scalar, the zero-scalar
capture, invalid indices, both inequality constructors, variable occurrences
in every query component, a variable appearing only with zero coefficient,
reusing an already introduced auxiliary, and a malformed terminal certificate.

A hand-written counterexample shows the need for global freshness:
`x0=1, x1≤0` is satisfiable, but choosing `s=x1` would add `x1=1` and make
the result inconsistent. Both facts are proved. A valid certificate of that
inconsistent result is rejected by `check_after_fixed_aux` because the
transformation's freshness check fails. This is a negative control, not an
observed Marabou failure.

At this milestone there were 37 project theories. Run:

```sh
isabelle build -D Isabelle
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

The main session checks all the new proofs and compilation of the rational
interface. All 96 existing importer tests still pass, including regeneration
of the fourteen imported theories and provenance checks on five saved solver
executions. See [BUILD_RESULT.md](BUILD_RESULT.md) for exact build results.

## Remaining scope and next target

The decoder, capture, native auxiliary-allocation loop, redundant-row removal,
other preprocessing, and floating-point execution remain unverified. ReLU
auxiliary introduction is a different transformation and is not covered here.
The later [source capture/import extension](SOURCE_QUERY_CAPTURE.md) adds
restricted automatic extraction of the actual supplied `InputQuery`; that
extraction and its decoder remain unverified.

The finite-sequence target is now completed in
[TABLEAU_AUXILIARY_SEQUENCE.md](TABLEAU_AUXILIARY_SEQUENCE.md), including the
five equations of the binary-split capture. Its explicit nine-variable source
query is linked to the fourteen-variable processed query and replayed proof.
Capture/import of the source query and step list alongside that proof is now
completed in [SOURCE_QUERY_CAPTURE.md](SOURCE_QUERY_CAPTURE.md), with generated
source-query UNSAT theorems for all five native scenarios.
