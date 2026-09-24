# Exact linear implications and explained ReLU premises

Implemented on 2026-09-22 against Marabou
`1c2f4788c32e2f4e407c356b763a8025c5578722`. This extends the existing rational
checker without changing its real query semantics or trusting C++ arithmetic.

## Verified contract

[Rational_Linear_Implication.thy](../Isabelle/Rational_Linear_Implication.thy)
defines an executable sufficient test for `target ≤ 0`:

1. Form `s = Σ w_i * row_i` over `normalize_query Q`.
2. Require exactly one nonnegative rational weight per row.
3. Collect repeated coefficients in `target - s`; require every variable
   coefficient to be zero and the remaining constant to be **nonpositive**.

Every row is nonpositive in a model of the query. Therefore `s ≤ 0`, and the
residual check proves `target ≤ s ≤ 0`. A zero residual is accepted. A negative
residual permits a weaker conclusion; a positive one is rejected. Unlike a
linear UNSAT leaf, an implication need not have a strict contradiction margin.
This is a sufficient checker, with no completeness claim.

```isabelle
check_linear_implication :: "rat_query ⇒ rat_linexpr ⇒ rat list ⇒ bool"
check_linear_bound :: "rat_query ⇒ rat_bound ⇒ rat list ⇒ bool"

check_linear_implication Q target ws
  ⟹ satisfies_query v (embed_query Q)
  ⟹ eval_rat_expr v target ≤ 0

check_linear_bound Q bound ws
  ⟹ satisfies_query v (embed_query Q)
  ⟹ satisfies_bound v (embed_bound bound)
```

The displayed implications are `check_linear_implication_sound` and
`check_linear_bound_sound`. Both upper and lower bounds are supported by the
HOL checker. `rat_linear_bound_preserves_models` proves that adding an accepted
bound leaves all real models unchanged. `unsatisfiable_linear_bound` transfers
UNSAT of the extended query back to the parent.

The recursive datatype adds `Linear_Bound bound weights child`. It checks the
implication against the **current** query before inserting the bound; only
then does it check the continuation. The additional induction case in
`check_certificate_sound` uses model preservation. A claimed bound, an
unverified continuation, or a later premise cannot be assumed as evidence.
The SML module exports both implication checks and the new constructor.

## Actual native explanation and reconstruction

All paths are relative to `upstream/Marabou/`:

| Source | Relevant behavior |
| --- | --- |
| `src/proofs/BoundExplainer.cpp::updateBoundExplanation`, `extractRowCoefficients`, `getExplanation` | Constructs signed weights over original tableau rows, using existing explanations and coefficients of the final tableau slack variables. |
| `src/proofs/UnsatCertificateUtils.cpp::getExplanationRowCombination(unsigned var, ...)` | Forms `c = e_var + wᵀA`, including the unit coefficient for the selected variable. |
| `UnsatCertificateUtils.cpp::computeBound`, `computeCombinationUpperBound` | Uses upper ground bounds for positive `c_j`, lower ground bounds for negative `c_j`. Empty/all-near-zero explanations use the selected ground bound directly. |
| `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound` | Records the causing variable's explanation and promotes the PLC conclusion to a ground bound; the linear premise is not itself promoted. |
| `src/proofs/Checker.cpp::checkReluLemma`, `checkAllPLCExplanations` | Checks explanations and PLC lemmas in order, with floating-point tolerances. |
| `src/proofs/JsonWriter.cpp::writePLCLemmas` | Writes `expl` as sparse `{"var": row_index, "val": signed_weight}` entries for a single-cause lemma. |

The importer supports the single-cause `U` to `U` ReLU output rule and now
also the `L` to `U` input/auxiliary rule documented in
[RELU_AUX_BOUND_PROPAGATION.md](RELU_AUX_BOUND_PROPAGATION.md).
It parses nonempty `expl` with strict original-row indices and exact decimal
rationals. For an upper premise on the selected input `x`, it computes

```text
c = e_x + wᵀA
U = Σ(c_j > 0) c_j u_j + Σ(c_j < 0) c_j l_j.
```

On `A*v = 0`, `c*v = v(x)`. The adapter reconstructs this normalized inequality:

```text
v(x) - U =
  -(wᵀA)*v
  + Σ(c_j > 0) c_j (v(j) - u_j)
  + Σ(c_j < 0) (-c_j) (l_j - v(j)) ≤ 0.
```

Signed equality weights select the appropriate positive/negative normalized
row. Every used ground bound must have an exact reconstruction from the current
canonical HOL query. The existing equality-span procedure handles explicit
bounds, equality consequences, and equality consequences plus one bound; it
rejects failures rather than supplying assumptions. Explanations continue to
index the original tableau even when earlier phase splits have prepended
canonical equalities.

For an upper premise, the candidate tree is

```text
Linear_Bound (RatUpper x U) weights
  (Relu_Upper x y U outputBound continuation).
```

The ReLU node still requires `max(0,U) ≤ outputBound` exactly. An all-exact-zero
nonempty vector derives the original ground bound. No nonzero rational
coefficient, however tiny, is treated as zero. Thus tolerance-accepted native
evidence can fail reconstruction or the exact conclusion guard.

Empty explanations keep the old direct path when the current ground bound is
explicit. Otherwise the adapter may emit a checked linear step reconstructing
that native bound from the canonical phase constraints.

Only the PLC **conclusion** updates the adapter's native ground-bound state.
The checked input premise is added to the HOL query but does not replace a
native ground bound for later explanations. This preserves the source meaning
of an empty explanation. Lemma order and separate branch states are retained.
Resource accounting conservatively charges two unary nodes per native lemma,
even when an explicit input premise makes one unnecessary.

The auxiliary extension reconstructs a lower premise with the same
`c=e_x+wᵀA`, using lower ground bounds for positive coefficients and upper
ground bounds for negative coefficients. Its normalized target is `L-x≤0`,
so the equality weights have the opposite signs. The existing
`check_linear_bound` verifies those weights. It also supplies two separate
`check_linear_implication` witnesses for the auxiliary equation before that
nonlinear rule is applied. Full formulas and actual captures are in
[the auxiliary contract](RELU_AUX_BOUND_PROPAGATION.md).

The adapter is still unverified. Its local arithmetic checks provide early
rejection, not logical assumptions: generated acceptance is proved with
`code_simp`, followed by `check_certificate_sound`. The result concerns the
explicit decoded processed query, not the JSON bytes, original binary doubles,
preprocessing, or an earlier network input.

## Examples and native component fixtures

[Rational_Linear_Implication_Examples.thy](../Isabelle/Rational_Linear_Implication_Examples.thy)
checks upper and lower implications, duplicate terms, a general linear target,
weaker bounds, exact-zero residuals, bad signs/lengths/cancellation, and a bound
too strong by `1/10^20`. A real model proves that a satisfiable example rejects
every UNSAT certificate. A second query requires a linear implication followed
by ReLU propagation; its linear relaxation has a real model.

Two new native-writer fixtures use

```text
-b + f - aux - t = 0
 b - 2*z + p - s = 0
f = ReLU(b),  p ≥ 1/2,  s = t = 0,  b ≤ 2.
```

* `explained_positive`: `z ≤ 1/2` implies `b ≤ 1/2`, then `f ≤ 1/2`,
  contradicting `f ≥ 3/4`.
* `explained_negative`: `z ≤ 0` implies `b ≤ -1/2`, then `f ≤ 0`,
  contradicting `f ≥ 1/4`.

The harness actually calls unchanged `BoundExplainer::updateBoundExplanation`
on the supplied row `b = 2*z - p + s`, obtains weight `-1` on original row 1,
and calls `UNSATCertificateUtils::computeBound`. It checks the computed values
before serializing the constructed `PLCLemma` and tree with `JsonWriter`.
Both imported theories prove acceptance and UNSAT in HOL.

**The query, tableau row, PLC object, and terminal contradiction are assembled
by the harness.** This runs the explanation and bound-computation components;
it does not run `ReluConstraint::notifyUpperBound`, the bound manager's
lemma-recording callback, preprocessing, or `Engine::solve`. These component
fixtures do not certify an actual solver result, and no theorem verifies
those C++ components.

At this milestone the importer suite passed 57 tests; the exported recursive
checker passed 23 SML tests. The original seven writer fixtures were unchanged. See
[BUILD_RESULT.md](BUILD_RESULT.md) for commands and exact build results.

## Next target

Both proposed captures are now complete: a linear query in
[SOLVER_CAPTURE.md](SOLVER_CAPTURE.md) and a necessary ReLU propagation with a
nonempty linear explanation in [SOLVER_RELU_CAPTURE.md](SOLVER_RELU_CAPTURE.md).
The latter uses the unchanged implication checker and adapter, on a premise
generated during `Engine::solve`. The separate semantic obligation remains to
connect processed queries to original queries through verified preprocessing
and auxiliary introductions.
The auxiliary extension now also replays two real solver-produced lower
explanations, including the broader negative variant that was previously
rejected. A native binary split with both children replayed is now captured in
[SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md), using the existing
checker. A scalar-fixed tableau auxiliary introduction is now verified in
[TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md), with an exact source-query
connection for the linear capture.
[Finite composition](TABLEAU_AUXILIARY_SEQUENCE.md) now covers the five
introductions of the binary-split capture. Capturing/importing its source
query and proposed step list remains the next small integration target.
Other nonlinear rules, Alethe, infinite bounds, and general reconstruction
remain outside this extension.
