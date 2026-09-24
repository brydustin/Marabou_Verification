# Positive-output-bound propagation and the preserved chained proof

The previously unsupported output-based auxiliary rule is now verified in
[ReLU_Output_Bound_Propagation.thy](../Isabelle/ReLU_Output_Bound_Propagation.thy).
The complete preserved proof replays, including its fourth PLC lemma.
A fresh `relu_chain` native execution reproduced all six preserved data
artifacts byte-for-byte and added full build/run provenance.

[Imported_Marabou_Native_Relu_Chain.thy](../Isabelle/Imported_Marabou_Native_Relu_Chain.thy)
proves the captured six-variable before-query UNSAT over real valuations,
through both ReLU introductions, five tableau introductions and all four
native propagation lemmas. Extraction, JSON decoding, floating-point
refinement and the general C++ implementation remain unverified.

## Mathematical rule and exact checker

For real values:

```text
y = ReLU(x),   0 < l <= y,   y - x - a = 0
                         imply
                       a = 0.
```

The lemma `relu_positive_output_aux_zero` proves this: positive output
forces `y=x`, then the checked auxiliary equation forces `a=0`.
It is distinct from the existing input-lower rule. Nonnegative output is
insufficient: `x=-1, y=0, a=1` is a counterexample at the zero boundary.

`check_relu_output_aux_upper_bound Q x y a l u pos neg` checks:

1. `ReLU x y` is present.
2. The **output** bound `RatLower y l` is present and `0<l` exactly.
3. Two exact linear implication witnesses prove `y-x-a<=0` and
   `-(y-x-a)<=0` from the current query.
4. `0<=u`, permitting the zero cap or a weaker auxiliary upper bound.

The checker does not trust auxiliary metadata as an equation. Missing
premises, wrong directions or variables, zero/negative lower premises,
negative proposed caps, and bad equation witnesses reject.

| Theorem | Guarantee |
| --- | --- |
| `check_relu_output_aux_upper_bound_sound` | Every real model of the current embedded query satisfies the accepted auxiliary upper bound. |
| `rat_relu_output_aux_upper_preserves_models` | Adding that bound preserves the entire real model set. |
| `unsatisfiable_relu_output_aux_upper_bound` | UNSAT after adding a checked bound implies UNSAT before it. |
| `check_certificate_sound`, extended | The new recursive constructor composes with every existing rule and a checked continuation. Acceptance still implies real-semantic UNSAT. |

The new constructor in [Rational_Proof_Trees.thy](../Isabelle/Rational_Proof_Trees.thy)
is `Relu_Output_Aux_Upper x y a l u pos neg child`. Its field `l` names an
output lower bound; the existing `Relu_Aux_Upper` still names an input lower
bound. The proof-tree soundness induction has a separate case for the new
rule. Both the helper and constructor are included in the SML export.

The [HOL examples](../Isabelle/ReLU_Output_Bound_Examples.thy) check positive
and tiny-positive rational premises, weaker conclusions, malformed evidence,
and all important guards. They prove real models for a satisfiable positive
case and the zero-boundary counterexample. Unsoundly adding `a<=0` to that
zero-boundary example creates a checked linear contradiction, while the
guarded rule rejects the attempted lift. A relaxed chained source with
`w>=0` has a proved real model and rejects every composed certificate.

## Actual source correspondence

Marabou remains pinned at `1c2f4788c32e2f4e407c356b763a8025c5578722`.
Neither upstream repository was modified.

| Source | Observed behavior / comparison |
| --- | --- |
| `src/engine/ReluConstraint.cpp::notifyLowerBound`, positive-bound branch around lines 177–196 | For a positive lower bound on `_f` or `_b`, emit auxiliary upper bound zero when proof production and an auxiliary are present. This milestone adds the `_f` case. |
| `src/proofs/Checker.cpp::checkReluLemma`, lines 674–678 | Recognizes `causingVar==f`, LB, `affectedVar==aux`, UB; tests positivity of the explained bound plus epsilon and returns zero. Our rule instead requires strict positivity of the exact reconstructed rational premise. |
| `src/proofs/UnsatCertificateUtils.cpp`, `UNSATCertificateUtils::computeBound/getExplanationRowCombination` | Native row explanations identify the causing variable's bound. The adapter recomputes and validates an exact linear implication. |
| `src/proofs/JsonWriter.cpp::writePLCLemmas` | Serializes `causVar/causBound` and `affVar/affBound`, the claimed bound, activation type and explanation. |
| `src/engine/ReluConstraint.cpp::transformToUseAuxVariables` | Supplies the native auxiliary equation, whose real meaning is separately justified by checked introduction and later linear witnesses. |

Exact arithmetic may reject a
tolerance-accepted native lemma near zero. No theorem transfers the native
epsilon policy into real arithmetic, and no observed solver failure is claimed.

## Import and the complete native chain

[import_marabou_json.py](../Isabelle/tools/import_marabou_json.py) now
distinguishes `OutputAuxUpperLemma` from `AuxUpperLemma`. Matching requires
a unique cause/affected pair across the ReLU metadata, including possible
input/output role ambiguity. Explanation reconstruction receives the actual
causing variable explicitly. Thus the new rule uses the output's bounds,
not the input's bounds.

The exact linear premise is added as checked HOL evidence, but is not
silently treated as a native ground-bound update. Only the validated PLC
conclusion updates that state. Tests cover this distinction, recursion under
both children of an independent split, and rejection of sibling leakage.

The captured source, with `b=x0, f=x1, c=x2, g=x3, z=x4, w=x5`, is:

```text
b = z,   c = f - 1/4,   g = w
f = ReLU(b),            g = ReLU(c)
b,c in [-2,2]; f,g in [0,2]; z in [-2,-1/2]; w in [1/4,2]
```

Native ReLU introductions add `a=x6` and `d=x7` with upper bounds 2.
Five scalar-fixed steps add `x8..x12`; `x9=-1/4` carries the second equation's
nonzero scalar. All six independent replay inputs are retained.

| Native lemma | Exact replay |
| --- | --- |
| Input `b` upper → output `f` upper | Row 0 proves `b<=-1/2`; add `f<=0`. |
| Input `c` lower → auxiliary `d` upper | Row 1 proves `c>=-1/4`; accept the weaker serialized cap `0.250001 = 250001/1000000`. |
| Input `c` upper → output `g` upper | With the first lemma, row 1 proves `c<=-1/4`. The serialized cap `1.750001 = 1750001/1000000` is a valid weaker conclusion than zero. |
| Output `g` lower → auxiliary `d` upper | Row 2 proves `g>=1/4`, which is strictly positive. Two witnesses prove `g-c-d=0`, then the new rule adds `d<=0`. |

The native linear contradiction follows. The fourth lemma is not necessary
for every possible refutation of this query: a regression test also checks
that the recorded earlier lemmas can close the leaf without it. Nevertheless
the actual saved proof includes it, and the full replay validates it.
Replacing its explanation with an unjustified zero premise rejects the
complete import; an inconsistent prefix does not cause a node to be skipped.

The old seven JSON files remain unchanged in
[rejected_relu_chain](../Isabelle/tests/fixtures/marabou/rejected_relu_chain/README.md).
That directory name records their earlier rejection, not their current
logical status. Its original trial still lacks full build provenance.
The new `solver_relu_chain*` files record a fresh execution with complete
provenance, and all six data artifacts match the historical copies exactly.
The native report has 6 → 8 → 13 variables, four PLC lemmas, three main-loop
iterations, one simplex step, one explained leaf, and no split or delegation.
General preprocessing and DeepSoI remain disabled.

## Validation and reproduction

The session has 54 theories, all checked without admissions or added axioms.
All 197 importer tests pass, including 23 new tests for this rule.
The regenerated exports pass 8 linear-leaf and 47 proof-tree SML checks.
All 22 generated theories match regeneration. There are seventeen canonical
accepted writer fixtures: nine component fixtures and eight replayed native
scenarios, plus the retained duplicate historical chain artifacts.
The seven earlier native scenarios were rerun with the final sources; their
data stayed byte-identical and provenance was refreshed from actual runs.
See [BUILD_RESULT.md](BUILD_RESULT.md).

From the project root, using a fresh output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_chain --output /tmp/marabou-output-bound-capture
isabelle build -d Isabelle -D /tmp/marabou-output-bound-capture
```

Replay saved evidence without running C++:

```sh
python3 Isabelle/tools/import_marabou_relu_sequence.py \
  --before-relu Isabelle/tests/fixtures/marabou/solver_relu_chain_before_relu.json \
  --relu-steps Isabelle/tests/fixtures/marabou/solver_relu_chain_relu_steps.json \
  --source Isabelle/tests/fixtures/marabou/solver_relu_chain_source.json \
  --steps Isabelle/tests/fixtures/marabou/solver_relu_chain_steps.json \
  --query Isabelle/tests/fixtures/marabou/solver_relu_chain_query.json \
  --certificate Isabelle/tests/fixtures/marabou/solver_relu_chain.json \
  --output /tmp/marabou-output-bound-replay/Imported_Output_Bound.thy --session
isabelle build -d Isabelle -D /tmp/marabou-output-bound-replay
```

The next small rule target is the dual native branch: a strictly positive
auxiliary lower bound forces the ReLU output to zero. That requires its own
checked premise, auxiliary equation and native evidence capture. Other
propagation directions, general preprocessing, verified decoding and
network-file correspondence remain outside this milestone.

Update, 2026-09-23: that dual rule is now verified and replayed from a new
native capture; see [RELU_AUX_LOWER_BOUND_PROPAGATION.md](RELU_AUX_LOWER_BOUND_PROPAGATION.md).
