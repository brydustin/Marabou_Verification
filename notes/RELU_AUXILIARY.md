# One checked fresh ReLU auxiliary

One ReLU auxiliary introduction is now proved sound over the existing real
query semantics. Given a present `ReLU x y` and a globally fresh variable `a`,
the transformation retains the ReLU and all original constraints and appends:

```text
y - x - a = 0
0 <= a
a <= max(0, -l)     if the selected input lower bound l <= x is present
```

The executable interface checks those premises and constructs the new row
and bounds. It can then run the existing finite scalar-fixed tableau sequence
and recursive certificate checker. Acceptance proves the original source
query UNSAT over real valuations.

This is distinct from both [scalar-fixed tableau introduction](TABLEAU_AUXILIARY.md)
and [propagation on an existing ReLU auxiliary](RELU_AUX_BOUND_PROPAGATION.md).
The new auxiliary is a function of the valuation, `a = y-x = max(0,-x)`.
It is generally not fixed to a scalar.

## Actual source and deliberate abstraction

The audited Marabou revision remains
`1c2f4788c32e2f4e407c356b763a8025c5578722`. No upstream files were changed.

| Source | Actual behavior / relation to the model |
| --- | --- |
| `src/engine/ReluConstraint.cpp::transformToUseAuxVariables`, lines 936–978 | If `_auxVarInUse` is true, return unchanged. Otherwise allocate `_aux` at the current variable count, increment the count, append `f-b-aux=0`, set its lower bound to zero, set its upper bound from the input lower bound, and enable the metadata flag. |
| Same function, lines 968–974 | Read the constraint's lower bound if it exists, otherwise use negative infinity. Compute `0` if the lower bound is positive and its negation otherwise: the exact real counterpart is `max(0,-l)`. |
| `src/engine/PiecewiseLinearConstraint.h::existsLowerBound/getLowerBound`, lines 593–615 | Read either the registered bound manager or the constraint's local bound map. This is not a direct query-list lookup. |
| `src/engine/Preprocessor.cpp::preprocess` and `informConstraintsOfInitialBounds`, lines 61 and 1121 | Notify constraints of query bounds before transformations. Other preprocessing operations also occur; they are not assumed correct by this rule. |
| `Preprocessor::transformConstraintsIfNeeded`, lines 212–216 | Invoke each piecewise-linear constraint's auxiliary transformation. |
| `src/engine/Query.cpp::addEquation/setLowerBound/setUpperBound` | Store the added equation and bounds. The HOL representation instead appends atoms to finite conjunction lists. |

The HOL operation always requests a new mathematical auxiliary. It has no
`_auxVarInUse` state and does not implement the C++ no-op branch. It accepts
any natural-number name absent from all query components, rather than
assuming a C++ allocation invariant. A second introduction with the same
name is rejected; a different fresh copy remains a valid mathematical
extension even where the native flag would cause a no-op.

A supplied finite lower bound must occur explicitly in the query. We do not
trust cached native bounds. If it is only implied, a separate verified
inference is needed to make it available. An upper bound or a lower bound
on another variable does not satisfy this check.

`None` requests no finite upper bound on the auxiliary. It represents the
unbounded native case without treating infinity as a real number. It is also
a sound weaker presentation when a finite input bound is present: the old
query, ReLU, and new equality still imply the omitted cap. The rule does not
claim that the native implementation would omit that finite cap.

The logical ReLU is retained. The new equality and bounds alone are not a
replacement for `y=max(0,x)`. C++ state changes, bound synchronization,
metadata, numerical comparisons, and preprocessing are not verified.

## Definitions and theorems

[ReLU_Auxiliary.thy](../Isabelle/ReLU_Auxiliary.thy) defines the real operation
`introduce_relu_aux`, the optional auxiliary bounds, and the explicit
finite-lower-bound premise. It reuses the existing proved identities
`relu_aux_identity` and `relu_aux_upper_bound`.

| Theorem | Guarantee |
| --- | --- |
| `satisfies_introduce_relu_aux_iff` | Under ReLU membership and the selected lower-bound premise, a valuation satisfies the result iff it satisfies the source and `v a = v y - v x`. Freshness is not needed for this pointwise characterization. |
| `models_introduce_relu_aux` | The result's full model set is `{v in models Q. v a = v y-v x}`. No incorrect equality of full valuation sets is asserted. |
| `relu_aux_model_extension` | With freshness, updating `a` to `v y-v x` satisfies the result iff the original valuation satisfies the source. |
| `relu_aux_model_projection` | A result model, with the fresh coordinate reset arbitrarily, satisfies the source. All original atoms were retained. |
| `satisfiable_introduce_relu_aux_iff` / `unsatisfiable_introduce_relu_aux_iff` | SAT and UNSAT are preserved in both directions under the checked mathematical premises. |

[Rational_ReLU_Auxiliary.thy](../Isabelle/Rational_ReLU_Auxiliary.thy) adds:

```text
rat_introduce_relu_aux ::
  rat_query => var => var => var => rat option => rat_query option

check_after_relu_aux ::
  rat_query => var => var => var => rat option =>
  fixed_aux_step list => certificate => bool
```

`rat_introduce_relu_aux Q x y a lower` returns `None` unless the selected ReLU
is present, `a` is absent from the complete syntactic support of `Q`, and any
`Some l` lower bound occurs in `Q`. On success it returns the constructed
query. Zero-coefficient variable occurrences count towards support.

`embed_rat_relu_aux_query` proves exact correspondence with the real
transformation, including the optional cap under `of_rat`.
`rat_introduce_relu_aux_real` establishes all real-theorem premises from a
successful computation. Rational model extension/projection and
`rat_introduce_relu_aux_satisfiable_iff` follow from those real proofs.
The UNSAT equivalence is a corollary.

`check_after_relu_aux` first introduces the ReLU auxiliary, then invokes
`check_after_fixed_aux_sequence` with the supplied tableau-introduction list
and certificate. An empty list checks the result directly. Every failure
rejects the combined check.
`check_after_relu_aux_sound` proves:

```text
check_after_relu_aux Q x y a lower steps cert
  ==> unsatisfiable (embed_query Q)
```

It has no caller-supplied freshness, lower-bound validity, or solver-correctness
assumption. `check_after_relu_aux_rejects_model` excludes every accepted
combination for a source with a real model. Both new public functions pass
`export_code ... checking SML`; examples use proof-producing `code_simp`.
No certificate constructor or existing generic checker was changed.

## Exact connection to existing solver evidence

[ReLU_Auxiliary_Examples.thy](../Isabelle/ReLU_Auxiliary_Examples.thy) defines
the four-variable `solver_before_relu_aux`, with `x0,x1,x2,x3 = b,f,z,w`:

```text
b - z = 0              f - w = 0              f = ReLU(b)
-2 <= b <= 2           0 <= f <= 2
-2 <= z <= -1/2        1/4 <= w <= 2
```

Introducing `a=x4` with `Some(-2)` adds `f-b-a=0` and `0<=a<=2`.
`solver_relu_aux_matches_captured_source` computes equality with the entire
existing `Imported_Marabou_Source_Relu_Aux.imported_source_query` record.
It retains that snapshot's original `f,b,a` addend order.

`solver_before_relu_aux_checked` then checks the captured scalar-fixed steps
`[(0,5),(1,6),(2,7)]` and the existing native propagation/linear-leaf proof.
The certificate's linear combinations are checked directly on the constructed
rows; their arithmetic does not depend on column order.
`solver_before_relu_aux_unsatisfiable` derives UNSAT of the four-variable
source using the new composed soundness theorem.

This example's four-variable starting query is hand-written HOL data. The older saved actual
solver execution began with the five-variable query and an already supplied
ReLU auxiliary. That example alone makes no native introduction capture claim.
A subsequent [native capture and import](NATIVE_RELU_INTRO_CAPTURE.md) now
records this four-variable input and the actual transformation call, then
replays both alongside the solver proof in a separate generated theory.

## Validation and remaining target

HOL examples cover negative, zero and positive lower bounds; no finite lower
bound; a coinciding ReLU input/output; model extension from an arbitrary old
auxiliary value; and all syntactic freshness locations. They reject reuse,
reversed/missing ReLUs, bounds on the wrong variable or in the wrong direction,
unjustified stronger and absent weaker bounds, incomplete subsequent tableau
steps, and a malformed terminal certificate.

Two designed negative controls show why the guards matter: raw introduction
with a reused variable, or without a ReLU, can make a satisfiable source
inconsistent. Both raw results have checked linear UNSAT certificates.
The guarded interface rejects both attempted lifts to the source.
These are mathematical counterexamples to weakened rules, not solver failures.

Run:

```sh
isabelle build -D Isabelle
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

At the mathematical-rule milestone the session contained 47 theories and
122 importer tests. The subsequent native integration adds one generated
theory and 24 importer tests, for 48 theories and 146 tests.
See [BUILD_RESULT.md](BUILD_RESULT.md) for exact results.

The native single-introduction integration target is now completed in
[NATIVE_RELU_INTRO_CAPTURE.md](NATIVE_RELU_INTRO_CAPTURE.md). Its separate
importer accepts one plain ReLU and a finite lower bound.
[Finite composition and a two-ReLU capture](RELU_AUXILIARY_SEQUENCE.md) are
now completed too; that milestone had 51 theories and 174 importer tests.
The later [positive-output extension](RELU_OUTPUT_BOUND_PROPAGATION.md)
brings the project to 54 theories and 197 importer tests.
General preprocessing and verified byte decoding remain separate targets.
