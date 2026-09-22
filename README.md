# Marabou verification in Isabelle/HOL

The development proves exact rational linear-leaf and recursive ReLU proof-tree
checkers sound over real query semantics. A strict adapter imports a subset of
Marabou's JSON certificate format and emits theories for Isabelle to replay.
The checker also verifies linear implications and two ReLU propagation rules:
input upper to output upper, and input lower to auxiliary upper. Both support
tableau explanations; the auxiliary rule also checks its defining equation.
Thirteen certificates serialized by the actual C++ writer have been checked in HOL.
Four come from real proof-enabled `Engine::solve` executions: one linear query,
one output-propagation query, and two auxiliary-propagation variants.
The other nine are hand-assembled/component fixtures.
**The solver-produced evidence proves UNSAT of the captured processed queries.
Marabou's implementation, preprocessing, decoder, and original-query
correspondence are not verified.**

## Build

Tested with `Isabelle2025-2`. From this project directory:

```sh
isabelle version
isabelle build -D Isabelle
```

The session is `Marabou_Verification`, based on `HOL`, with
`quick_and_dirty = false`. No additional packages or upstream C++ builds are
needed. See [the build record](notes/BUILD_RESULT.md) for the final result and
[the environment audit](notes/ENVIRONMENT_AUDIT.md) for installation details.

The session also checks that both checkers compile to Standard ML. To extract
`Marabou_Linear_Leaf.ML` and `Marabou_Proof_Checker.ML` under `Isabelle/generated/`, run:

```sh
isabelle build -e -D Isabelle
```

The generated directory is ignored by Git and can be regenerated from the
theories. See [the leaf checker interface](notes/RATIONAL_LINEAR_CHECKER.md) and
[certificate import and tree checking](notes/CERTIFICATE_IMPORT.md) for the
interfaces, execution instructions, and assurance boundary.

## Files and definitions

| File | Contents |
| --- | --- |
| [Isabelle/ROOT](Isabelle/ROOT) | HOL session and theory order. |
| [Marabou_Syntax.thy](Isabelle/Marabou_Syntax.thy) | `var = nat`, `valuation = var ⇒ real`; finite affine expressions, linear atoms, bounds, ReLU atoms, and the `query` record. |
| [Marabou_Semantics.thy](Isabelle/Marabou_Semantics.thy) | `eval_terms`, `eval_linexpr`, constant/variable expressions, expression addition and scaling. |
| [Linear_Constraints.thy](Isabelle/Linear_Constraints.thy) | Exact semantics of equality, both inequality directions, and lower/upper bounds; elementary inference rules. |
| [ReLU_Constraints.thy](Isabelle/ReLU_Constraints.thy) | `relu x = max 0 x`, ReLU satisfaction and phase decomposition. |
| [Query_Semantics.thy](Isabelle/Query_Semantics.thy) | `satisfies_query`, `models`, `satisfiable`, `unsatisfiable`, and a contradictory-bounds rule. |
| [ReLU_Splitting.thy](Isabelle/ReLU_Splitting.thy) | `active_split`, `inactive_split`, model coverage and the UNSAT inference rule. |
| [Marabou_Examples.thy](Isabelle/Marabou_Examples.thy) | Exact SAT witness, an UNSAT proof using two linear children, and the overlapping zero-input case. |
| [Rational_Linear_Constraints.thy](Isabelle/Rational_Linear_Constraints.thy) | Rational query data, exact embedding into real queries, and proved normalization of equalities, inequalities and bounds. |
| [Rational_Linear_Certificates.thy](Isabelle/Rational_Linear_Certificates.thy) | Exact coefficient collection, checked weighted sums, `check_linear_leaf`, its soundness theorem, and SML code generation. |
| [Rational_Linear_Examples.thy](Isabelle/Rational_Linear_Examples.thy) | Proved acceptance/rejection computations and a ReLU example closed with checked linear leaves. |
| [Rational_Linear_Implication.thy](Isabelle/Rational_Linear_Implication.thy) | `check_linear_implication`, `check_linear_bound`, real-semantic soundness, and preservation of models when adding a checked bound. |
| [Rational_Linear_Implication_Examples.thy](Isabelle/Rational_Linear_Implication_Examples.thy) | Upper/lower bounds, weaker conclusions, malformed evidence, SAT witnesses, and a linear-premise/ReLU/UNSAT chain. |
| [ReLU_Bound_Propagation.thy](Isabelle/ReLU_Bound_Propagation.thy) | Exact input-to-output upper-bound propagation, its checked premises, and a real-model-preservation theorem. |
| [ReLU_Aux_Bound_Propagation.thy](Isabelle/ReLU_Aux_Bound_Propagation.thy) | Input-lower to auxiliary-upper propagation, with two exact linear witnesses for the auxiliary equation, soundness, and model preservation. |
| [ReLU_Aux_Bound_Examples.thy](Isabelle/ReLU_Aux_Bound_Examples.thy) | Negative/zero/positive cases, premise/equation rejection checks, real counterexamples, and the active capture's satisfiable linear relaxation. |
| [Rational_Proof_Trees.thy](Isabelle/Rational_Proof_Trees.thy) | Rational splits, their real embedding theorems, recursive certificates, `check_certificate_sound`, and SML export. |
| [Rational_Proof_Tree_Examples.thy](Isabelle/Rational_Proof_Tree_Examples.thy) | Nested-tree acceptance, absent/repeated ReLU and bad-child rejection, and the earlier UNSAT example checked recursively. |
| [ReLU_Bound_Examples.thy](Isabelle/ReLU_Bound_Examples.thy) | Negative/zero/positive propagation, ordered chains, real witnesses, and rejection of forged premises or conclusions. |
| [Imported_Marabou_Linear.thy](Isabelle/Imported_Marabou_Linear.thy), [Imported_Marabou_Relu.thy](Isabelle/Imported_Marabou_Relu.thy), [Imported_Marabou_Nested.thy](Isabelle/Imported_Marabou_Nested.thy) | Generated data, kernel-checked acceptance, and real-semantic UNSAT theorems for three writer fixtures. |
| [Imported_Marabou_Propagation.thy](Isabelle/Imported_Marabou_Propagation.thy), [positive](Isabelle/Imported_Marabou_Propagation_Positive.thy), [chain](Isabelle/Imported_Marabou_Propagation_Chain.thy), [tree](Isabelle/Imported_Marabou_Propagation_Tree.thy) | Four imported `PLCLemma` examples, each replayed through the extended soundness theorem. |
| [Imported_Marabou_Explained_Negative.thy](Isabelle/Imported_Marabou_Explained_Negative.thy), [positive](Isabelle/Imported_Marabou_Explained_Positive.thy) | Nonempty tableau explanations become checked linear-bound premises, followed by ReLU propagation and exact contradiction. |
| [Imported_Marabou_Solver_Linear.thy](Isabelle/Imported_Marabou_Solver_Linear.thy) | Kernel-checked UNSAT for an actual solver execution's captured processed query. |
| [Imported_Marabou_Solver_Relu.thy](Isabelle/Imported_Marabou_Solver_Relu.thy) | Actual solver-produced linear premise, ReLU propagation, and terminal contradiction, replayed unchanged. |
| [Solver_ReLU_Examples.thy](Isabelle/Solver_ReLU_Examples.thy) | A real model of that capture's linear relaxation and proof that no linear leaf alone can certify its root query. |
| [Imported_Marabou_Solver_Relu_Aux.thy](Isabelle/Imported_Marabou_Solver_Relu_Aux.thy), [active](Isabelle/Imported_Marabou_Solver_Relu_Aux_Active.thy) | Actual solver-produced auxiliary lemmas, checked with their lower explanations and auxiliary equations, then composed with terminal contradictions. |
| [capture_marabou_solver.py](Isabelle/tools/capture_marabou_solver.py), [capture.cpp](Isabelle/tools/solver_capture/capture.cpp) | Reproducible native-engine build, pre-solve snapshot, solver-owned certificate export, provenance, and standalone replay generation. |
| [import_marabou_json.py](Isabelle/tools/import_marabou_json.py) | Untrusted strict JSON adapter; exact decimal decoding, independent query matching, and reconstruction of candidate weights. |

An expression `Linexpr c [(a1,x1), …]` evaluates as
`c + a1*v(x1) + …`. Lists are finite by construction and may contain duplicate
variables or zero coefficients. Coefficients, constants, bounds and valuations
are **mathematical reals** in the semantic core. The executable layer uses
separate rational data and `embed_query` to connect it to that same real
semantics; it does not restrict valuations to rational values.

A query conjoins its three finite lists: `linear_atoms`, `query_bounds`, and
`relu_atoms`. Missing bounds mean no restriction in that direction. Valuations
are total functions on natural numbers; only variables appearing in the query
are constrained. There is no C++ variable-count field in the abstract model.

## Assurance from the proved theorems

All project theory proofs are completed; there are no admitted proofs, aborted
proofs, or added axioms. The usual Isabelle/HOL foundations and proof kernel are
the basis of the result. Conditional theorems state their premises explicitly.

| Theorem(s) | Precisely what follows |
| --- | --- |
| `eval_terms_append`, `eval_add_linexpr`, `eval_scale_linexpr`, `eval_terms_cong` | Expression operations have the claimed real arithmetic meaning; evaluation depends only on mentioned variables. |
| `linear_eq_iff_two_inequalities`, `lower_bound_as_linear`, `upper_bound_as_linear` | Equality and bounds have the expected linear-constraint encodings. |
| `linear_le_add`, `linear_le_scale_nonnegative` | Adding valid inequalities, or scaling one by a nonnegative real, preserves truth. These are building blocks, not a complete certificate checker. |
| `inconsistent_bounds`, `query_inconsistent_bounds` | A lower bound strictly exceeding an upper bound excludes every valuation satisfying both. |
| `relu_phase_decomposition`, `satisfies_relu_phase_decomposition` | `y = max 0 x` is equivalent to `(x ≤ 0 ∧ y = 0) ∨ (0 ≤ x ∧ y = x)`. |
| `relu_phases_overlap_iff` | Both phase conditions hold exactly when input and output are zero. |
| `models_relu_split` | **If `ReLU x y` belongs to the query**, the parent model set equals the union of the two child model sets. All other constraints are retained. |
| `satisfiable_relu_split`, `unsatisfiable_relu_split` | Under that membership premise, SAT is equivalent to SAT of either child; UNSAT of both children implies UNSAT of the parent. |
| `satisfiable_iff_models_nonempty`, `unsatisfiable_iff_no_valuation`, `unsatisfiable_iff_models_empty` | Model-set and existential/universal definitions agree. |
| `normalize_linear_correct`, `normalize_bound_correct`, `embed_query_normalization` | Rational query normalization preserves the meaning of each constraint over real valuations, with ReLU atoms retained separately. |
| `weighted_sum_wellformed`, `weighted_sum_nonpositive` | Successful combination requires matching lengths and nonnegative weights; its value is nonpositive in every model of the normalized rows. |
| `eval_collect_terms`, `constant_contradiction_positive` | Combining repeated variable coefficients preserves evaluation; an accepted constant contradiction evaluates strictly positively for every real valuation. |
| `check_linear_leaf_sound` | `check_linear_leaf Q ws` implies `unsatisfiable (embed_query Q)`, including when the query still contains ReLUs. No assumptions on the solver are needed. |
| `check_linear_implication_sound`, `check_linear_bound_sound` | An accepted nonnegative row combination proves the proposed inequality or bound in every real model of `embed_query Q`. |
| `rat_linear_bound_preserves_models` | Adding an accepted linear bound preserves the entire real model set; the premise is checked before insertion. |
| `embed_rat_active_split`, `embed_rat_inactive_split` | Rational child-query operations embed to exactly the existing real splits. |
| `check_relu_upper_bound_sound`, `rat_relu_upper_preserves_models` | A present ReLU and an explicit input upper bound justify an output bound at least `max(0,u)`; adding it preserves the real model set. |
| `check_relu_aux_upper_bound_sound`, `rat_relu_aux_upper_preserves_models` | A present ReLU, an explicit input lower bound `l`, and two checked linear witnesses for `f-b-a=0` justify `a≤max(0,-l)` or a weaker bound, preserving all real models. |
| `check_certificate_sound`, `check_certificate_no_model` | An accepted finite tree excludes every real valuation of its embedded root query. Split nodes check membership and both phases; propagation nodes check the rule and their continuation. |
| `check_certificate_rejects_model` | A query with a real model has no accepted certificate of this datatype. Rejection of one certificate does not imply SAT. |
| `Imported_Marabou_*.imported_query_unsatisfiable` | The explicit processed rational queries in these theories have no real solutions. Hash comments record file provenance; byte decoding and preprocessing are not formalized. |

Each split replaces every copy of the selected ReLU atom with explicit linear
phase constraints. The active child adds `x ≥ 0, y - x = 0`; the inactive child
adds `x ≤ 0, y = 0`. The theorem allows duplicate atoms, zero input, and even
equal variable indices; it does not assume that the branches are disjoint.

The hand-written examples use variable 0 for `x` and variable 1 for `y`:

* `sat_example_satisfiable`: `x + y = 2`, `-1 ≤ x ≤ 1`, `y = ReLU(x)`.
  `sat_example_witness` proves that the valuation assigning 1 to every variable
  satisfies it.
* `unsat_example_unsatisfiable`: `x ≤ 0`, `y ≥ 1`, `y = ReLU(x)`.
  Both children contain only linear atoms and bounds. The active child would
  require `y = x ≤ 0`; the inactive child would require `y = 0`. Both contradict
  `y ≥ 1`, and the general splitting theorem closes the parent.
* `zero_in_both_children`: the zero valuation satisfies both children of a
  query containing a single ReLU.

The rational examples additionally prove acceptance of fractional contradictory
bounds, an affine equality with repeated variables, and a constant-only
contradiction. They prove rejection of negative weights, missing/extra weights,
zero weights, zero contradiction margin, an empty query, and a nonzero residual
coefficient of `1/1000000`. Two satisfiable counterexamples have explicit real
models. These computations use `code_simp` to produce HOL proofs.

`unsat_example_via_leaf_certificates` closes the earlier ReLU example using
two accepted leaf certificates and the existing splitting theorem. Explicit
equalities identify the embedded rational leaves with the original real child
queries. `unsat_example_via_recursive_certificate` now proves the same result
with the general tree checker, and `nested_query_unsatisfiable` exercises two
levels of splitting.

`Relu_Upper x y u b child` adds `y ≤ b` after checking the ReLU, the existing
bound `x ≤ u`, and `max(0,u) ≤ b`. The extended soundness theorem composes this
inference with linear leaves and splits. See the [propagation
contract](notes/RELU_BOUND_PROPAGATION.md) for source correspondence and examples.

`Linear_Bound bound weights child` first checks an exact linear implication,
then checks the continuation with the proved bound added. This supplies
non-ground input premises to `Relu_Upper`. The [linear implication
contract](notes/RATIONAL_LINEAR_IMPLICATION.md) explains the residual-constant
check and the native `e_x + wᵀA` explanation reconstruction.

`Relu_Aux_Upper b f a l u pos neg child` checks `f=ReLU(b)` membership,
`b≥l`, two linear witnesses for `f-b-a=0`, and `max(0,-l)≤u` before adding
`a≤u`. The [auxiliary propagation contract](notes/RELU_AUX_BOUND_PROPAGATION.md)
explains the lower-bound reconstruction and actual solver captures.

## Import and replay

The adapter accepts the pinned `JsonWriter::writeProofToJson` format for finite
homogeneous tableaux, finite bounds, auxiliary-form ReLUs, binary phase splits,
linear contradictions, and **input-to-output-upper or input-lower-to-auxiliary-upper
PLC lemmas with empty or nonempty tableau explanations reconstructed exactly**.
Auxiliary lemmas additionally require checked witnesses for their equation.
It requires a
separate expected processed-query file. Numbers mean the exact rational values
of their serialized decimal tokens; they do not silently mean the original
binary doubles or network-file numbers.

From the project root, create a replay session in a new directory:

```sh
python3 Isabelle/tools/import_marabou_json.py \
  --query Isabelle/tests/fixtures/marabou/nested_query.json \
  --certificate Isabelle/tests/fixtures/marabou/nested.json \
  --output /tmp/marabou-replay/Imported_Check.thy --session
isabelle build -d Isabelle -D /tmp/marabou-replay
```

The first command reconstructs candidate data. The successful Isabelle build
proves `Imported_Check.imported_query_unsatisfiable` by `code_simp` and
`check_certificate_sound`. The [import contract](notes/CERTIFICATE_IMPORT.md)
documents unsupported evidence, fixture provenance, and test commands.

The first [actual solver capture](notes/SOLVER_CAPTURE.md) uses the native
engine with proof production enabled and preprocessing/DeepSoI disabled.
Initialization succeeds, `solve` reports UNSAT, and its row certificate replays
unchanged through the existing importer. This run has no ReLUs or simplex
pivots; it tests the linear proof-production and capture path.

The subsequent [ReLU solver capture](notes/SOLVER_RELU_CAPTURE.md) produces
`b ≤ -1/2 ⇒ ReLU(b) ≤ 0` and a linear contradiction with margin `1/4`.
The entire native certificate replays through the existing checker. A separate
HOL witness proves its linear relaxation satisfiable, so nonlinear evidence is
essential. Reproduce it with:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu --output /tmp/marabou-relu-capture
isabelle build -d Isabelle -D /tmp/marabou-relu-capture
```

The [auxiliary captures](notes/RELU_AUX_BOUND_PROPAGATION.md) now replay the
previously unsupported broader variant without editing its proof. A second
run uses `b≥1/2 ⇒ aux≤0` as its sole nonlinear inference, followed by an exact
contradiction. Its linear relaxation also has a proved real model.

## Connection to source and remaining scope

The inspected upstream revisions are pinned by the existing submodules:

* Marabou: `1c2f4788c32e2f4e407c356b763a8025c5578722`.
* ReluplexCav2017: `60b482eec832c891cb59c0966c9821e40051c082`.

The sources were inspected without modifying either repository. Findings and
open questions are recorded in:

* [MARABOU_SOURCE_MAP.md](notes/MARABOU_SOURCE_MAP.md): C++ concepts and control flow.
* [FORMALIZATION_MAP.md](notes/FORMALIZATION_MAP.md): the relation between HOL concepts and source, including mismatches.
* [LINEAR_CERTIFICATES.md](notes/LINEAR_CERTIFICATES.md): exact leaf-certificate mathematics, existing evidence, papers, and the next step.
* [RATIONAL_LINEAR_CHECKER.md](notes/RATIONAL_LINEAR_CHECKER.md): the implemented checker and its verified contract.
* [CERTIFICATE_IMPORT.md](notes/CERTIFICATE_IMPORT.md): recursive checking, the native JSON adapter, numeric contract, and replay instructions.
* [RELU_BOUND_PROPAGATION.md](notes/RELU_BOUND_PROPAGATION.md): the checked propagation rule, native lemma fields, scope restrictions, and replay examples.
* [RATIONAL_LINEAR_IMPLICATION.md](notes/RATIONAL_LINEAR_IMPLICATION.md): exact linear premises, their recursive checking, and native explanation reconstruction.
* [SOLVER_CAPTURE.md](notes/SOLVER_CAPTURE.md): the first actual solver execution, saved artifacts, reproduction commands, and precise assurance boundary.
* [SOLVER_RELU_CAPTURE.md](notes/SOLVER_RELU_CAPTURE.md): solver-produced nonlinear evidence, exact reconstruction, coverage limitations, and replay.
* [RELU_AUX_BOUND_PROPAGATION.md](notes/RELU_AUX_BOUND_PROPAGATION.md): the auxiliary rule, checked defining equation, lower explanations, and two additional solver captures.
* [RELUPLEX_MARABOU_LINEAGE.md](notes/RELUPLEX_MARABOU_LINEAGE.md): historical comparison, with Marabou as the verification target.

No translator from the original `InputQuery`, SAT-assignment checker, Alethe
importer, or support for propagation rules beyond the two described above
is implemented. The model does not
establish the correctness of preprocessing,
tableau construction, simplex, pivoting, floating-point comparisons, search
termination, or C++ state updates. In particular, it does not prove that any
actual Marabou call satisfies the hypotheses of our split rule.

Network file parsing, ONNX/TensorFlow, other activations, DeepPoly, DeepSoI,
parallel search, Split-and-Conquer, and Gurobi integration remain outside the
initial fragment. A proof about an imported processed tableau still
needs a justified connection to the original query and its numeric interpretation.

## Next smallest meaningful target

Capture a solver-produced binary ReLU split and replay both children with
supported evidence. The connection to original inputs through verified
auxiliary introductions and preprocessing remains a separate semantic target.
No Farkas completeness or simplex theorem has been added.
