# Verified ReLU upper-bound propagation

Implemented on 2026-09-22, using the existing real semantics and Marabou revision
`1c2f4788c32e2f4e407c356b763a8025c5578722`. This milestone adds **one** propagation
rule. The subsequent [linear implication extension](RATIONAL_LINEAR_IMPLICATION.md)
now imports both explicit ground premises and nonempty tableau explanations.
The later [auxiliary rule](RELU_AUX_BOUND_PROPAGATION.md) additionally supports
input lower bounds, with its defining auxiliary equation checked separately.

## The rule and its assurance

For real values:

```text
x ≤ u     y = max(0,x)     max(0,u) ≤ b
-------------------------------------
                y ≤ b
```

This covers negative, zero, and positive input upper bounds. The output may
use any weaker bound `b ≥ max(0,u)`. A negative output upper bound is never
accepted by this rule. No numerical tolerance is used.

[ReLU_Bound_Propagation.thy](../Isabelle/ReLU_Bound_Propagation.thy) defines:

```isabelle
check_relu_upper_bound Q x y u b ⟷
  ReLU x y ∈ set (rat_relu_atoms Q) ∧
  RatUpper x u ∈ set (rat_query_bounds Q) ∧ max 0 u ≤ b
```

`rat_add_bound Q (RatUpper y b)` prepends the verified bound and preserves
all linear and ReLU atoms. It does not replace or delete existing bounds.

| Theorem | Assurance |
| --- | --- |
| `relu_upper_bound` | If a real `x ≤ u`, then `relu x ≤ max 0 u`. |
| `check_relu_upper_bound_sound` | Under an accepted rule check, every real model of `embed_query Q` satisfies the proposed bound on `y`. |
| `rat_relu_upper_preserves_models` | Under that same check, adding the bound leaves the entire real model set unchanged. |
| `unsatisfiable_relu_upper_bound` | UNSAT after this checked addition implies UNSAT of the original query. |

The certificate datatype in
[Rational_Proof_Trees.thy](../Isabelle/Rational_Proof_Trees.thy) now also has:

```isabelle
Relu_Upper var var rat rat certificate
```

`Relu_Upper x y u b child` checks the rule above, then checks `child` against
the query with `RatUpper y b` added. The extended induction proof retains the
same central theorem:

```isabelle
check_certificate Q cert ⟹ unsatisfiable (embed_query Q)
```

The input bound must be present **before** the propagation step. It may come
from the root query, a canonical branch bound, or an earlier checked lemma.
An implied bound must first be added by `Linear_Bound bound weights child`,
which proves it by an exact nonnegative combination of normalized query rows.
`Relu_Upper` itself still requires explicit membership. The selected ReLU
must also still be present; splitting that
ReLU removes it from the canonical query. These restrictions trade coverage
for a small, explicit kernel. The model-preservation theorem permits redundant
bound additions, whereas the C++ bound manager records successful tightenings.

## Source audit and choice of rule

All source paths below are relative to `upstream/Marabou/`.

| Source | Actual behavior relevant to this milestone |
| --- | --- |
| `src/engine/ReluConstraint.cpp:258`, `notifyUpperBound`, input-variable branch at lines 310–352 | In proof mode, a negative input upper bound records an output upper bound of zero. The remaining phase-unknown case records the input upper bound on the output. The source also has linear propagation paths when a phase is already fixed. |
| `src/engine/BoundManager.cpp:414`, `addLemmaExplanationAndTightenBound` | On a successful tightening, records one causing variable and its explanation in a `PLCLemma`, appends it to the current node, and registers the resulting ground bound. |
| `src/proofs/PlcLemma.{h,cpp}` | Carries the affected/causing variables, bound directions, proposed value, activation type, and explanation list. |
| `src/proofs/UnsatCertificateUtils.cpp:17`, `computeBound` | An empty explanation refers to the current ground bound of the causing variable. A nonempty explanation may derive a bound from tableau rows. |
| `src/proofs/Checker.cpp:621`, `checkReluLemma`, especially lines 702–721 | Checks the two input-to-output upper-bound cases using tolerance-adjusted comparisons. Our exact guard is a mathematical rule, not a verification of those comparisons. |
| `src/proofs/Checker.cpp:207`, `checkAllPLCExplanations` | Processes the node's lemma list in order and updates ground bounds. |
| `src/proofs/JsonWriter.cpp:257`, `writePLCLemmas` | Serializes the single-cause/single-explanation fields used below. The `constraint` field is the activation type, not a constraint index. |

Output nonnegativity was the earlier suggested example. Inspection showed that
`ReluConstraint::notifyLowerBound` at lines 250–254 performs the direct repair
of a negative output lower bound only with `!proofs`. `getEntailedTightenings`
does provide output nonnegativity, and `Checker::checkReluLemma` contains a
related case, but that is not evidence of an emitted proof-mode lemma on this
path. We chose the explicit proof-producing upper-bound calls instead. The
existing mathematical theorem `relu_nonnegative` remains available.

## Imported evidence and scope

The adapter now accepts this additional node entry, as emitted by the real
`JsonWriter` for a hand-constructed `PLCLemma`:

```json
"lemmas": [{
  "affVar": 1, "affBound": "U", "bound": 0.0,
  "causVar": 0, "causBound": "U", "constraint": 0, "expl": []
}]
```

It identifies `ReLU 0 1`. With a current explicit input upper bound of `-1/2`,
the adapter emits `Relu_Upper 0 1 (-1/2) 0 ...`. The native `bound` field is the
**output** value; the input value is read from the current checked query state.

This output-upper pattern requires both directions to be `U`, `constraint = 0`,
the exact input/output pair of a remaining ReLU, and an empty or sparse `expl`.
Empty explanations use the strongest current native ground input upper bound.
Nonempty explanations form `e_x + wᵀA` and a sign-selected ground-bound sum;
the importer emits a checked `Linear_Bound` before the ReLU step.
All ground bounds used must be reconstructed from the current canonical query.
The output value must satisfy the exact rational guard. Exact-zero vectors
derive the existing ground bound; tiny nonzero coefficients are never dropped.
Unknown fields, other patterns, and failed exact reconstruction are rejected.
Multiple-cause `causVars` and multiple-explanation `expls` forms remain outside
this rule.

Lemmas are reconstructed in file order before the node's leaf or split.
Each accepted step becomes one or two unary HOL certificate nodes. The PLC
output becomes a native ground bound; a linear input premise is added only
to the HOL query, preserving the meaning of later native explanations.
Branch reconstruction uses separate query/bound
states, so one child cannot borrow its sibling's derived bounds. Lemma nodes
count toward the existing size and depth limits of the reconstructed tree.

The Python adapter remains untrusted. Its checks produce candidate data;
`code_simp` proves acceptance in Isabelle, and the central soundness theorem
gives UNSAT over real valuations. An erroneous parser could change which
explicit query is stated, so correspondence to input bytes remains outside
the HOL proof. Decimal tokens retain the exact rational interpretation stated
in [CERTIFICATE_IMPORT.md](CERTIFICATE_IMPORT.md).

## Examples and tests

[ReLU_Bound_Examples.thy](../Isabelle/ReLU_Bound_Examples.thy) proves negative,
zero, and positive propagation examples; a weaker output conclusion; an
ordered two-step chain; and rejection of missing premises, absent/reversed
ReLUs, an overly strong bound, and an unchecked continuation. A satisfiable
query has an explicit real model and therefore rejects every certificate.
The negative/positive examples' linear relaxations also have explicit real
models, showing why the ReLU inference is needed.

Four new C++-writer fixtures and corresponding `Imported_Marabou_*.thy` files
exercise imported evidence:

* `propagation`: `b ≤ -1/2` implies `f ≤ 0`, contradicting `f ≥ 1/4`.
* `propagation_positive`: `b ≤ 1/2` implies `f ≤ 1/2`, contradicting `f ≥ 3/4`.
* `propagation_chain`: two ReLUs propagate `1/2` in order before a linear leaf.
* `propagation_tree`: each child of an independent ReLU split proves its own
  propagation step before closing; sibling state is not shared.

These four files use the unchanged upstream `PLCLemma` and `JsonWriter` classes.
Their evidence is constructed by hand; the harness does **not** execute
`notifyUpperBound`, `BoundManager::addLemmaExplanationAndTightenBound`, or
`Engine::solve`. It validates native serialization compatibility and exact
HOL replay, not the correctness of C++ propagation or proof production.
Two additional `explained_negative/positive` fixtures call
`BoundExplainer::updateBoundExplanation` and `UNSATCertificateUtils::computeBound`
on supplied tableau rows. They replay nonempty evidence through the linear
implication checker. Their query and tree assembly is still hand constructed;
they provide component evidence. See [the explanation contract](RATIONAL_LINEAR_IMPLICATION.md).

Separately, [SOLVER_RELU_CAPTURE.md](SOLVER_RELU_CAPTURE.md) now captures this
rule during an actual `Engine::solve` execution, including a nonempty linear
explanation. The unedited native proof replays in
`Imported_Marabou_Solver_Relu`. Its linear relaxation has a proved real model,
so the nonlinear step is necessary. This does not change the provenance of
the six earlier component fixtures.

The current importer suite passes 96 tests, including deleting/reordering lemmas,
removing one sibling's evidence, and rejecting claimed bounds stronger by
`1/10^20`. New tests check original-row indices under splits, mixed coefficient
signs, tiny nonzero weights, and the separation of linear premises from native
ground updates. The exported tree checker passes 35 SML tests. See the exact
commands and build output in [BUILD_RESULT.md](BUILD_RESULT.md).

To replay the chain in a fresh standalone session:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/propagation_chain_query.json \
  --certificate Isabelle/tests/fixtures/marabou/propagation_chain.json \
  --output /tmp/marabou-propagation/Imported_Propagation_Check.thy --session
isabelle build -d Isabelle -D /tmp/marabou-propagation
```

## Next smallest target

The proposed exact linear-implication checker and nonempty-explanation import
are now implemented in [RATIONAL_LINEAR_IMPLICATION.md](RATIONAL_LINEAR_IMPLICATION.md).
The [linear solver capture](SOLVER_CAPTURE.md) and
[ReLU propagation capture](SOLVER_RELU_CAPTURE.md) are now replayed.
The auxiliary-upper-bound rule suggested by the latter is now verified and
replayed in [RELU_AUX_BOUND_PROPAGATION.md](RELU_AUX_BOUND_PROPAGATION.md):
`b ≥ l ⇒ aux ≤ max(0,-l)`, with checked ReLU and auxiliary-equation premises.
Solver-produced binary splitting with both children replayed is now recorded
in [SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md).
One scalar-fixed tableau auxiliary introduction is now verified in
[TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md), and
[finite sequences](TABLEAU_AUXILIARY_SEQUENCE.md) now compose these steps for
the binary-split capture. Capturing/importing its pre-tableau query and step
list is the next small integration target. Alethe and the full bridge through
preprocessing to original queries remain separate obligations.
