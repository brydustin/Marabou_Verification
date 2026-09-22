# Exact rational linear-leaf checker

Implemented in the second milestone on 2026-09-22. The theory files are
[Rational_Linear_Constraints.thy](../Isabelle/Rational_Linear_Constraints.thy),
[Rational_Linear_Certificates.thy](../Isabelle/Rational_Linear_Certificates.thy),
and [Rational_Linear_Examples.thy](../Isabelle/Rational_Linear_Examples.thy).

## Verified contract

```isabelle
check_linear_leaf :: "rat_query ⇒ rat list ⇒ bool"

theorem check_linear_leaf_sound:
  assumes "check_linear_leaf Q ws"
  shows "unsatisfiable (embed_query Q)"
```

`embed_query` produces a query of the **existing** `query` type. Coefficients,
constants and bounds are embedded using `of_rat`; the valuation type remains
`nat ⇒ real`. Therefore acceptance excludes all real solutions, including
irrational ones. There is no assumption that Marabou returned UNSAT, that a
numerical tolerance was met, or that the weights came from a correct solver.

The equivalent `check_linear_leaf_no_model` conclusion is
`¬ (∃v. satisfies_query v (embed_query Q))`.
`check_linear_leaf_rejects_model` states that a query with a real model cannot
have an accepted certificate.

**False means that this certificate did not establish UNSAT. It does not mean
SAT.** The checker neither searches for weights nor claims certificate
completeness. It may close a query with unsplit ReLUs because an inconsistent
linear relaxation has no model of the full query.

## Rational data and row order

`RatExpr c ts` contains a rational constant and a finite list of rational
coefficient/natural-variable pairs. `RatEq`, `RatLe`, and `RatGe` compare an
expression with a rational scalar. Bounds are `RatLower x l` and `RatUpper x u`.
The record `rat_query` has `rat_linear_atoms`, `rat_query_bounds`, and
`rat_relu_atoms`; the last field uses the existing ReLU atom type.

Each normalized row represents an expression constrained to be **≤ 0**:

| Original atom | Normalized rows, in order |
| --- | --- |
| `RatEq e b` | `e - b`, then `-(e - b)` |
| `RatLe e b` | `e - b` |
| `RatGe e b` | `-(e - b)` |
| `RatLower x l` | `l - x` |
| `RatUpper x u` | `x - u` |

`normalize_query` concatenates the normalized linear atoms in input order,
then appends one normalized row per bound in input order. ReLUs do not
contribute linear rows. The theorems `normalize_linear_correct`,
`normalize_bound_correct`, `normalize_query_correct`, and
`embed_query_normalization` prove these semantic equivalences.

The certificate contains **one weight for every normalized row**, including
unused rows, whose weight is zero. It contains no separately supplied row
contents or row indices that could replace the query's constraints. Equalities
can contribute with either sign by selecting their two opposite rows with
nonnegative weights.

## Algorithm and proof

1. `weighted_sum` recursively matches the weight and row lists. It returns
   `None` on either length mismatch or any negative weight. Otherwise it adds
   the weighted rational expressions. `weighted_sum_wellformed` proves these
   checks; no truncated `zip` is used.
2. `collect_terms` merges occurrences of the same variable using rational
   addition. Zero coefficients are retained harmlessly. `eval_collect_terms`
   proves that this preserves evaluation for every real valuation, including
   for duplicate and nonadjacent variable occurrences.
3. `constant_contradiction` requires every collected coefficient to be exactly
   zero and the combined constant to be **strictly positive**. This means the
   weighted inequality would be `k ≤ 0` with `k > 0`.

Any model makes all normalized rows nonpositive. Nonnegative weighting and
addition preserve that fact (`weighted_sum_nonpositive`). But an accepted
constant contradiction evaluates positively for every valuation
(`constant_contradiction_positive`). Combining the two proves
`check_linear_leaf_sound`.

All computation in the checker uses rationals, natural-variable equality,
lists and Booleans. It does not execute real arithmetic or compare real
values. The simple list-based collection algorithm is intended for the first
verified kernel; no scalability claim is made.

## Checked examples

Acceptance and rejection facts are proved with `code_simp`, using proof-producing
rewriting of code equations:

* Bounds `1/2 ≤ x ≤ 1/3`, with weights `[1/3, 1/3]`.
* An affine equality with fractional coefficients, interleaved duplicate
  variables and a zero coefficient, plus an incompatible inequality; weights
  `[0, 2, 1]`.
* The constant-only equality `1/2 = 1/3`, with weights `[1, 0]`.
* An inconsistent linear query that still contains a ReLU.
* Rejection of too few or too many weights and of all-zero weights.
* Rejection of `[1, -1]` for the satisfiable pair `x ≤ 0, x ≤ 1`.
* Rejection of a row `1 + x/1000000 ≤ 0` whose variable coefficient does not
  cancel. The explicit real witness `x = -1000000` is also proved to satisfy it.
* Rejection of a zero contradiction margin and of the empty query.

The theorem `unsat_example_via_leaf_certificates` connects this checker to the
first milestone: the active child uses weights `[1, 0, 1, 0, 1]`, the inactive
child `[1, 0, 1, 0, 0]`. Theorems identify their embedded queries with
`active_split unsat_example 0 1` and `inactive_split unsat_example 0 1`.
The existing `unsatisfiable_relu_split` rule then closes the original real
query. This composition is explicit in that proof. The subsequent
[tree-checker milestone](CERTIFICATE_IMPORT.md) also proves the example through
the general recursive checker.

## Generated executable

Every session build includes `export_code ... checking SML`, so Isabelle checks
compilation with its installed SML compiler. To extract the generated module:

```sh
isabelle build -e -D Isabelle
```

This writes `Isabelle/generated/Marabou_Linear_Leaf.ML`. It exports
`Marabou_Linear_Leaf.check_linear_leaf`, the rational query constructors,
`make` for queries, and the standard HOL rational/integer/natural construction
functions. Its arithmetic is exact; the generated checker uses no floats.

From the project root, run the public-interface smoke tests with Poly/ML:

```sh
poly --script Isabelle/tests/linear_leaf_smoke.ML
```

On the audited installation, the executable used was
`/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly`.
The run reported `8 exported SML checker tests passed` and exited with status 0.
The tests exercise fractional acceptance and rejection of bad signs, residuals,
length mismatches, zero margins and an empty query, plus constant acceptance.

The exported construction functions follow HOL's total-operation conventions:
`fract n 0` represents zero, and `nat_of_integer` maps negative integers to
zero. They are not an external-data validator. A future importer must reject
zero-denominator fraction syntax and negative variable indices before using
these functions if it is to preserve such input syntax. The subsequent JSON
adapter accepts finite numeric JSON tokens and checked integer indices; it
emits rational HOL terms with strictly positive denominators.

The soundness theorem is a result in Isabelle/HOL. A standalone SML run also
depends on code generation, the compiler and runtime; its Boolean output does
not on its own construct an Isabelle theorem. The example UNSAT theorems use
kernel-checked acceptance facts and the soundness theorem inside Isabelle.

## Relation to Marabou and next step

This certificate interface is a choice for our mathematical kernel. Marabou's
`src/proofs/Contradiction`, `BoundExplainer`, and `UnsatCertificateUtils` use
row-combination/bound evidence; `AletheProofWriter::linearCombinationMpq` uses
rational recomputation. A separate restricted JSON adapter now reconstructs
their row/bound evidence as candidate normalized weights; it does not assert
correctness equivalence with the C++ components. See [the source
investigation](LINEAR_CERTIFICATES.md) for the exact pinned revision and
preprocessing/serialization issues.

Rational ReLU splits, their embedding equalities, and a recursive checker with
a soundness proof are now implemented; see [CERTIFICATE_IMPORT.md](CERTIFICATE_IMPORT.md).
The same weighted-sum infrastructure also checks [linear
implications](RATIONAL_LINEAR_IMPLICATION.md) that supply ReLU propagation
premises, with a nonpositive residual instead of a positive contradiction.
Original-query decoding and the justification of preprocessing remain separate
obligations. Neither upstream repository was modified.
