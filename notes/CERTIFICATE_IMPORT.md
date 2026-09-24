# Recursive certificates and Marabou JSON import

Implemented on 2026-09-22 against Marabou commit
`1c2f4788c32e2f4e407c356b763a8025c5578722`. The upstream repositories remain
unchanged. This milestone has two distinct assurance boundaries: the HOL
checker theorem and an untrusted adapter that produces data for that checker.
The subsequent [ReLU propagation milestone](RELU_BOUND_PROPAGATION.md) extends
the same checker and import interface. The [linear implication
extension](RATIONAL_LINEAR_IMPLICATION.md) now supplies checked tableau-derived
premises for that rule.
The [auxiliary propagation extension](RELU_AUX_BOUND_PROPAGATION.md) adds
input-lower to auxiliary-upper lemmas, with checked auxiliary equations.
The [positive-output extension](RELU_OUTPUT_BOUND_PROPAGATION.md) adds
output-lower to auxiliary-upper zero, with a strictly positive exact premise.
The [positive-auxiliary extension](RELU_AUX_LOWER_BOUND_PROPAGATION.md) adds
its dual, auxiliary-lower to output-upper zero, also with a strictly positive
exact premise.

## Verified recursive checker

[Rational_Proof_Trees.thy](../Isabelle/Rational_Proof_Trees.thy) defines:

```isabelle
datatype certificate =
    Linear_Unsat "rat list"
  | Relu_Split var var certificate certificate
  | Relu_Upper var var rat rat certificate
  | Relu_Aux_Upper var var var rat rat "rat list" "rat list" certificate
  | Relu_Output_Aux_Upper var var var rat rat "rat list" "rat list" certificate
  | Relu_Aux_Lower_Output_Upper var var var rat rat "rat list" "rat list" certificate
  | Linear_Bound rat_bound "rat list" certificate
  | Relu_Fix_Active var var rat_bound "rat list" certificate
  | Relu_Fix_Inactive var var rat_bound "rat list" certificate

check_certificate :: "rat_query ⇒ certificate ⇒ bool"

theorem check_certificate_sound:
  assumes "check_certificate Q cert"
  shows "unsatisfiable (embed_query Q)"
```

`Linear_Unsat` uses the existing exact leaf checker. `Relu_Split x y active
inactive` first checks `ReLU x y ∈ set (rat_relu_atoms Q)`, then checks both
children against queries **constructed by the checker**. Certificate data
cannot substitute arbitrary child assumptions. There is no constructor for a
hole, a delegated leaf, a trusted lemma, or a claimed SAT result.
`Relu_Upper x y u b child` requires the selected ReLU and `RatUpper x u` in
the current query, checks `max(0,u) ≤ b` exactly, and checks the continuation
after adding `RatUpper y b`.
`Linear_Bound bound weights child` checks a nonnegative linear implication
before adding the bound and checking the continuation. This is how a
tableau-derived input bound becomes an explicit premise for `Relu_Upper`.
`Relu_Aux_Upper x y a l u pos neg child` requires a present ReLU, an explicit
input lower bound, two checked linear implications establishing `y-x-a=0`,
and `max(0,-l)≤u` before adding `a≤u` and checking the child.
`Relu_Output_Aux_Upper x y a l u pos neg child` instead requires the
**output** lower bound `RatLower y l`, strict `0<l`, the same two equation
witnesses, and `0≤u`. It adds `a≤u` and checks the continuation.
At output zero, this rule is invalid and the checker rejects it.
`Relu_Aux_Lower_Output_Upper x y a l u pos neg child` is the dual: it requires
the **auxiliary** lower bound `RatLower a l`, strict `0<l`, the same two
equation witnesses, and `0≤u`, then adds the output bound `y≤u`.
At auxiliary zero it is invalid (`x=y=1, a=0`), and the checker rejects it.
`Relu_Fix_Active x y b ws child` and `Relu_Fix_Inactive x y b ws child`
justify a ReLU phase that native Marabou fixed before search. The weights
must prove the phase-deciding bound `b` (`x ≥ l` with `0 ≤ l` or `y ≥ l` with
`0 < l`; resp. `x ≤ u` or `y ≤ u` with `u ≤ 0`) from the query plus `y ≥ 0`
and `y ≥ x`. The continuation is then checked against that phase's split
query only; see [RELU_PHASE_FIXING.md](RELU_PHASE_FIXING.md).

`rat_active_split` adds `x ≥ 0, y - x = 0`; `rat_inactive_split` adds
`x ≤ 0, y = 0`. Both remove all occurrences of the selected ReLU.
`embed_rat_active_split` and `embed_rat_inactive_split` prove that embedding
these operations agrees exactly with the earlier real split operations.
Structural induction on the finite certificate then combines
`check_linear_leaf_sound`, `unsatisfiable_relu_split`, and the proved
model-preserving rules `unsatisfiable_relu_upper_bound`,
`unsatisfiable_relu_aux_upper_bound`,
`unsatisfiable_relu_output_aux_upper_bound`,
`unsatisfiable_relu_aux_lower_output_upper_bound`,
`unsatisfiable_relu_fixed_active`, `unsatisfiable_relu_fixed_inactive`, and
`unsatisfiable_linear_bound`.

`check_certificate_no_model` gives the equivalent no-real-valuation statement.
`check_certificate_rejects_model` excludes every certificate for a query with
a real model. A false result says only that this certificate did not prove
UNSAT. Neither termination/completeness of Marabou search nor existence of a
certificate is assumed or proved.

The abstract examples include a two-level tree, the earlier ReLU UNSAT query,
and rejection of an absent ReLU, a repeated split, or one bad child. The
generated module `Marabou_Proof_Checker.ML` exports the datatype constructors,
exact rational construction functions, queries, and `check_certificate`.

## Actual source format

Paths and line numbers below refer to the pinned upstream checkout.

| Source | Evidence used by the adapter |
| --- | --- |
| `src/proofs/JsonWriter.cpp:48`, `writeProofToJson` | Top-level `tableau`, `upperBounds`, `lowerBounds`, `constraints`, `proof`. |
| `JsonWriter.cpp:119`, `writePiecewiseLinearConstraints` | `constraintType` and `vars`; participating variables followed by tableau auxiliary variables. |
| `src/engine/PiecewiseLinearFunctionType.h:20` | `RELU = 0`. |
| `src/engine/ReluConstraint.cpp:391`, `getParticipatingVariables` | Auxiliary-form order `[b, f, aux]`; `addTableauAuxVar` at line 1162 supplies the fourth writer variable. The serialized constructor uses a different order, `relu,f,b,aux`. |
| `JsonWriter.cpp:162`, `writeUnsatCertificateNode` | Nodes contain splits, optional PLC lemmas, then children or a contradiction. The writer reorders binary ReLU children to put inactive first. |
| `JsonWriter.cpp:217`, `writeHeadSplit` | Serializes bound tightenings (`var`, `val`, `bound`), **not equations** in the case split. |
| `ReluConstraint.cpp:674/683`, `getInactiveSplit/getActiveSplit` | Inactive: `b ≤ 0, f ≤ 0`. Auxiliary active: `b ≥ 0, aux ≤ 0`. |
| `JsonWriter.cpp:246`, `writeContradiction`; `Contradiction.{h,cpp}` | Either `[variable_index]` for inconsistent bounds or sparse `[{"var": row_index, "val": weight}, …]`. Here `var` denotes a **row index**, unlike its use in tableau entries. |
| `JsonWriter.cpp:257`, `writePLCLemmas`; `ReluConstraint.cpp:258`, `notifyUpperBound`; `BoundManager.cpp:414`, `addLemmaExplanationAndTightenBound` | The supported lemma propagates an input upper bound to the output: `constraint = 0`, both bound directions `U`, and empty or sparse row-combination `expl`. See the [detailed source audit](RELU_BOUND_PROPAGATION.md). |
| `ReluConstraint.cpp::notifyLowerBound`; `UnsatCertificateUtils.cpp::computeCombinationLowerBound` | The second supported pattern propagates an input lower bound to an auxiliary upper bound: `causBound=L`, `affBound=U`, `causVar=b`, `affVar=aux`. Lower explanations and the auxiliary equation are checked exactly; see [the auxiliary contract](RELU_AUX_BOUND_PROPAGATION.md). |
| `ReluConstraint.cpp::notifyLowerBound`, positive `_f` branch; `src/proofs/Checker.cpp::checkReluLemma`, lines 674–678 | The third pattern has `causVar=f` and `affVar=aux`, LB to UB. HOL requires the reconstructed output lower bound to be strictly positive, without the native epsilon relaxation; see [the positive-output contract](RELU_OUTPUT_BOUND_PROPAGATION.md). |
| `ReluConstraint.cpp::notifyLowerBound`, positive `_aux` branch, lines 207–226; `Checker.cpp::checkReluLemma`, lines 685–689 | The fourth pattern has `causVar=aux` and `affVar=f`, LB to UB, bound zero. HOL requires the reconstructed auxiliary lower bound to be strictly positive; see [the positive-auxiliary contract](RELU_AUX_LOWER_BOUND_PROPAGATION.md). |
| `src/proofs/UnsatCertificateUtils.cpp`, `getExplanationRowCombination(unsigned var, ...)`, `computeBound` | Bound explanations use `e_var + wᵀA`, unlike terminal contradictions' `wᵀA`. The exact reconstruction supplies a checked linear implication. |
| `src/proofs/UnsatCertificateUtils.cpp`, `computeCombinationUpperBound` | For `c = wᵀA`, select upper bounds when `c_j > 0`, lower bounds when `c_j < 0`; contradiction when the resulting upper bound is negative. The C++ implementation uses tolerances. |
| `src/engine/Engine.cpp:1290`, `addAuxiliaryVariables` | Converts equations to homogeneous tableau rows by introducing variables fixed to the scalars. The adapter interprets the exported rows as `A x = 0`; it does not prove this preprocessing step. |
| `JsonWriter.cpp:44/351`, `JSONWRITER_PRECISION/convertDoubleToString` | Fixed decimal precision derived from the comparison epsilon (10 decimal places at this revision), followed by zero trimming. This can lose information from binary doubles. |

A source search still finds no production call to `writeProofToJson`. The
ordinary CLI must not be described as emitting this JSON merely because the
writer exists. `AletheProofWriter` is a different, configurable export path;
its rules and `hole` records are **not** supported by this adapter.

## Explicit import contract

[import_marabou_json.py](../Isabelle/tools/import_marabou_json.py) accepts a
certificate JSON file and a **separate expected processed-query JSON file**.
The latter has precisely the four top-level query fields, without `proof`.
Both are decoded independently, and the query records must match, including
list order and auxiliary metadata. Integer and decimal spellings denoting the
same rational match. This is deliberately stricter than semantic equivalence.
The theorem statement uses the expected query; leaf weights cannot replace it.

Every finite JSON number denotes its exact serialized rational value, e.g.
`0.1 = 1/10`. Parsing uses `Decimal` followed by `Fraction`, with no conversion
through a Python float. JSON variable/row indices must be nonnegative integer
tokens and in range. Booleans are not accepted as numbers. Duplicate object
keys and sparse indices, strings masquerading as numbers, nonfinite values,
unknown fields, and malformed JSON are rejected. Invalid writer output is not
silently repaired; for example, some non-auxiliary constraint cases leave a
trailing comma in the writer's variable array.

Supported queries have nonempty homogeneous tableaux, finite lower and upper
bounds for every declared variable, and only ReLU metadata of the form
`[b, f, aux, tableauAux]`, with distinct indices. Each node is either a leaf
with one of the two native contradiction forms, or exactly two children
covering the active and inactive splits of one remaining ReLU. Either child
order is accepted. The root cannot introduce split assumptions.

Node `lemmas` lists may contain input-to-output-upper, input-lower-to-auxiliary-upper,
strictly-positive-output-lower-to-auxiliary-upper, or
strictly-positive-auxiliary-lower-to-output-upper ReLU propagation with empty
or nonempty `expl`. The cause/affected pair must select one ReLU and rule
unambiguously, across all lower-cause patterns and all ReLU metadata,
including input/output/auxiliary role ambiguity. An empty explanation
uses the current native ground bound of the actual causing variable.
A nonempty one computes a bound from `e_cause + wᵀA`; a
`Linear_Bound` node proves this premise before a ReLU rule uses it. Each used
ground bound must be reconstructed from the canonical query, and the output
conclusion must pass the exact ReLU rule. The three lemma patterns involving
the auxiliary also require two linear witnesses for `f-b-aux=0`, checked
before adding the conclusion.
The adapter processes lemmas in order.
Earlier PLC conclusions may supply later ground bounds; intermediate linear
premises do not update native ground state. Siblings do not share new bounds.

Other PLC patterns, explanations that fail exact reconstruction, other activations,
missing/infinite bounds, missing evidence, nonbinary branches, unknown node
flags, and other split forms are rejected. Empty `lemmas` and absent/empty root
`split` lists are permitted. Missing or delegated evidence cannot be turned
into a successful Boolean.

Resource limits for this first adapter are 4,000,000 input bytes, 256 variables,
512 rows, 4,095 nodes, depth 64, number tokens of at most 128 characters, and
decimal exponents of absolute value at most 256. Node/depth limits include the
unary nodes generated from lemmas, conservatively charging two per lemma.
These are engineering limits, not
restrictions in the HOL theorem.

## Reconstructing native evidence without trusting new assumptions

For a native row combination `c = wᵀA`, the adapter forms:

```text
-(wᵀA)x + Σ(c_j > 0) c_j (x_j - u_j)
         + Σ(c_j < 0) (-c_j) (l_j - x_j)  ≤ 0.
```

Its coefficients must cancel exactly and its constant must be strictly
positive. Signed equality weights become nonnegative weights on the two
normalized equality rows. The bounds used at a leaf are the tightest root,
recognized path, and checked propagation bounds. A variable-index contradiction
instead combines that variable's lower and upper bound rows.

The native path bounds are **not added to the HOL child query**. Each bound
used in reconstruction must itself be represented as a combination of the
current canonical query rows. Exact Gaussian elimination retains equality
combination witnesses. The present reconstruction procedure tries a direct
bound, an equality combination, or an equality combination plus one available
bound. It is intentionally incomplete: failure rejects the import.

For example, inactive `f ≤ 0` follows from the canonical `f = 0` equation.
For the fixture tableau `f - b - aux - t = 0`, active `f - b = 0` and the
ground bound `t ≥ 0` derive `aux ≤ 0`. The adapter produces the corresponding
row weights, and the HOL leaf checker checks their entire combination. It
does not trust metadata asserting that `aux = f - b`.

For an explained PLC input premise, the analogous calculation starts with
`c = e_x + wᵀA` and proves `x ≤ U`, where `U` is the sign-selected ground-bound
sum. A lower explanation uses the opposite ground-bound directions and proves
`x ≥ L`. The normalized weighted sum equals `x-U` or `L-x`; the linear-implication checker
checks cancellation and a nonpositive residual constant. It supports weaker
bounds as well. See [the exact contract](RATIONAL_LINEAR_IMPLICATION.md) for
the formula, zero-vector treatment, state handling, and source correspondence.

Python recomputes cancellations to reject obvious failures before writing a
theory. This is a convenience check, **not a proof premise**. The output contains
only rational query data, the tree, a `code_simp` acceptance proof, and an
application of `check_certificate_sound`. An incorrect combination cannot
establish an UNSAT theorem for a satisfiable decoded query: Isabelle rechecks
the candidate certificate without assuming these Python routines are correct.
A decoding error could change which explicit query the theorem concerns; the
result is not a formal theorem about the file's bytes or decoder correctness.

## Replay and fixture provenance

Nine component fixtures in [tests/fixtures/marabou](../Isabelle/tests/fixtures/marabou)
are generated using the unchanged upstream **C++ writer**:

```sh
python3 Isabelle/tests/build_marabou_fixtures.py Isabelle/tests/fixtures/marabou
```

This compiles the needed upstream source components with `g++ -std=c++17` and
links [marabou_json_fixture.cpp](../Isabelle/tests/marabou_json_fixture.cpp).
It uses real `ReluConstraint::getCaseSplit`, `UnsatCertificateNode`,
`Contradiction`, `PLCLemma`, and `JsonWriter::writeProofToJson`. No mocks replace these
components. An `IFile` adapter writes the output. Build products are confined
to the ignored `Isabelle/generated` directory; no downloads or full solver
build are needed. The ordinary Isabelle build uses the stored theories and
does not require a C++ compiler.

**The harness assembles queries and trees and does not call `Engine::solve`.**
Seven fixtures use hand-constructed evidence; two also execute the native
bound-explanation and bound-computation components. These test writer
compatibility and those component paths, not proof production by a solver run:

* `linear.json`: `x0 = x1`, `x0 ≤ 1/4`, `x1 ≥ 1/2`, with a native row weight
  `1/2`. This gives a strict contradiction margin `1/8`.
* `relu.json`: `f = ReLU(b)`, `b ≤ 0`, `f ≥ 1`, with a homogeneous auxiliary
  equation and finite bounds. The inactive child uses a variable-index
  contradiction; the active child uses a signed tableau-row combination.
* `nested.json`: adds an independent ReLU and splits it first; all four leaves
  are reconstructed against their proper canonical path queries.
* `propagation.json`, `propagation_positive.json`, `propagation_chain.json`,
  `propagation_tree.json`: input-to-output upper propagation with negative or
  positive input bounds, two ordered lemmas, and lemmas under a split. The
  [propagation note](RELU_BOUND_PROPAGATION.md) gives the exact queries and
  distinguishes the hand-built evidence from running C++ propagation.
* `explained_negative.json`, `explained_positive.json`: nonempty explanations
  computed by `BoundExplainer` on supplied rows, then interpreted by
  `UNSATCertificateUtils::computeBound` and serialized as PLC premises. The
  [linear implication note](RATIONAL_LINEAR_IMPLICATION.md) records the exact
  exercised methods and limits.

The corresponding nine `*_query.json` manifests are separately hand-written
descriptions of these processed queries.

A tenth fixture, `solver_linear.json`, now comes from an actual proof-enabled
`Engine::solve` run. Its separate `solver_linear_query.json` is a snapshot
written before solving, checked at runtime against the initial native tableau
and ground bounds. The harness does not construct this certificate. Its
processed query has `x - y - z = 0`, `z = 0`, `x ≤ 1/4`, and `y ≥ 1/2`;
the solver produces a single row-combination contradiction. Reproduction and
the captured logs/provenance are in [SOLVER_CAPTURE.md](SOLVER_CAPTURE.md).
The nine-fixture generator above does not regenerate this solver capture.

An eleventh fixture, `solver_relu.json`, also comes from a proof-enabled solver
execution. Its one native `U/U` lemma has explanation weight `-1` on original
row 0, deriving `b ≤ -1/2` and then `f ≤ 0`; row 2 closes the contradiction
with margin `1/4`. The full writer output is imported unchanged. The independent
snapshot and provenance use the same `solver_relu` prefix. A HOL witness shows
the root's linear relaxation is satisfiable. See
[SOLVER_RELU_CAPTURE.md](SOLVER_RELU_CAPTURE.md).

Two more captures, `solver_relu_aux.json` and `solver_relu_aux_active.json`,
replay actual auxiliary-upper lemmas. The negative case reproduces the earlier
rejected broader variant byte-for-byte, while the active case needs its sole
auxiliary lemma to close a linear contradiction. Both equation directions
are proved from the processed rows and fixed tableau bounds; metadata is not
treated as an extra premise. See
[RELU_AUX_BOUND_PROPAGATION.md](RELU_AUX_BOUND_PROPAGATION.md).

The fourteenth certificate, `solver_relu_split.json`, comes from native search
with one binary ReLU split and two closed linear children. Both canonical
child queries have exact contradiction margin `1/2`. The root's linear
relaxation has a HOL model, so a linear leaf alone cannot close it. See
[SOLVER_RELU_SPLIT_CAPTURE.md](SOLVER_RELU_SPLIT_CAPTURE.md).

All saved root-query numbers are exact dyadic rationals. The new negative
auxiliary lemma's `1.750002` is instead decoded as `875001/500000` and checked
as a weaker conclusion than `7/4`. No equality with a binary double is assumed.
A ninth native scenario, `solver_relu_aux_inactive.json`, contains the
positive-auxiliary lemma `aux≥1/4 ⇒ f≤0`; its root's linear relaxation has a
HOL model. See [RELU_AUX_LOWER_BOUND_PROPAGATION.md](RELU_AUX_LOWER_BOUND_PROPAGATION.md).

The fifteen processed-query replay theories in the main session are generated
by this adapter. Six further `Imported_Marabou_Source_*` theories are generated
by the [source adapter](SOURCE_QUERY_CAPTURE.md) from four artifacts each.
Three additional native-introduction replays, for
[one ReLU](NATIVE_RELU_INTRO_CAPTURE.md) and a
[finite sequence](RELU_AUXILIARY_SEQUENCE.md), plus the
[chained query](RELU_OUTPUT_BOUND_PROPAGATION.md), import six artifacts and
prove UNSAT before the ReLU auxiliaries exist.
Their acceptance and real UNSAT theorems are checked on every changed build.
Tests also compare them byte-for-byte with regenerated theories. SHA-256
comments identify the two source files but are not logical premises.

For a new supported pair, create a replay session in a **new directory**:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/nested_query.json \
  --certificate Isabelle/tests/fixtures/marabou/nested.json \
  --output /tmp/marabou-replay/Imported_Check.thy --session
isabelle build -d Isabelle -D /tmp/marabou-replay
```

`--session` writes a `ROOT` extending `Marabou_Verification` and refuses to
overwrite an existing `ROOT`. Subsequent regeneration in that directory omits
`--session`. The theorem after a successful build is
`Imported_Check.imported_query_unsatisfiable`. Without `--session`, a generated
theory can instead be included in the existing project's `ROOT`.

Validation commands from the project root:

```sh
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
isabelle build -e -D Isabelle
poly --script Isabelle/tests/linear_leaf_smoke.ML
poly --script Isabelle/tests/proof_tree_smoke.ML
poly --script Isabelle/tests/assignment_smoke.ML
isabelle build -D Isabelle
```

The audited Poly/ML executable is recorded in [BUILD_RESULT.md](BUILD_RESULT.md).
The tests cover 262 importer cases, 8 exported leaf-checker cases, 62 exported
tree-checker cases, and 11 exported assignment-checker cases. HOL examples use proof-producing `code_simp`; standalone
SML results have the additional code-generation/compiler/runtime boundary.

## Remaining obligations

This adapter's imported theorem is about a serialized **processed query**.
The source adapter additionally proves equisatisfiability and UNSAT for the
explicit captured source, using checked scalar-fixed introductions. There is no
verified decoder for original `InputQuery`/network files, proof of the native
preprocessing procedure (its results can now be [checked](NATIVE_PREPROCESSING.md)),
proof that decimal serialization preserves binary-double values, or theorem
relating a C++ return code to our semantics. Independently supplying a query
manifest prevents accidental certificate-header substitution but does not
prove where that manifest came from. Inspect the explicit theorem statement
when connecting it to an external claim.

Nine solver scenarios are now captured and replayed, including necessary
output-upper and auxiliary-upper inferences and a binary ReLU split with both
children checked. The encountered auxiliary rule is supported, with both
the lower premise and its defining equation checked; other unsupported
evidence is still rejected.
One scalar-fixed auxiliary introduction is now verified separately in
[TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md). Its checked result equals the
linear capture's processed query, so the existing certificate proves an
explicit two-variable source query UNSAT. The source is hand-written HOL data;
the decoder and native initialization remain unverified.
[Finite checked sequences](TABLEAU_AUXILIARY_SEQUENCE.md) now also connect the
binary-split capture to an explicit nine-variable source query. Those initial
examples used hand-written source/step data.
[Automatic capture/import](SOURCE_QUERY_CAPTURE.md) now saves and replays both
inputs for all five native scenarios, alongside the processed snapshot and
proof. Its complete query equality is checked in HOL; native extraction and
JSON decoding remain unverified.
[One fresh ReLU auxiliary introduction](RELU_AUXILIARY.md) is now verified
mathematically and composed with the existing scalar-fixed steps and checker.
Its explicit four-variable example maps exactly to the saved `relu_aux`
source and reuses that native proof.
[Native capture/import of that step](NATIVE_RELU_INTRO_CAPTURE.md) now starts
with a plain ReLU and proves UNSAT of its captured four-variable before-query.
It uses a separate strict importer and checks the entire independent result.
[Multiple ReLU introductions](RELU_AUXILIARY_SEQUENCE.md) now compose through
the same exact checks, with a native two-ReLU example requiring both constraints.
The exploratory chained example's
[output-lower-to-auxiliary-upper rule](RELU_OUTPUT_BOUND_PROPAGATION.md)
is now checked with a strictly positive exact premise. Its full preserved
bundle replays unchanged; a fresh native run reproduces all six data artifacts
and provides complete provenance. Its dual,
[positive-auxiliary-lower-to-output-upper-zero](RELU_AUX_LOWER_BOUND_PROPAGATION.md),
is now checked too, and an actual native proof using it replays to its
captured source query. ReLU phases that the initial bounds fix before search
are now [justified exactly](RELU_PHASE_FIXING.md) from a separate harness
record. Other PLC rules and verified extraction/decoding remain open. SAT results use a separate exact assignment
checker and importer; see [SAT_ASSIGNMENTS.md](SAT_ASSIGNMENTS.md). Starting
queries can also be stated as `.mqx` bytes whose meaning is a HOL decoder; see
[EXACT_QUERY_FORMAT.md](EXACT_QUERY_FORMAT.md).
