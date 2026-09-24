# Exact SAT assignments and a native SAT capture

Completed on 2026-09-23 against Marabou
`1c2f4788c32e2f4e407c356b763a8025c5578722`; neither upstream repository was
modified. This is roadmap item D of [CLAUDE_HANDOFF.md](../CLAUDE_HANDOFF.md).

[Rational_Assignment.thy](../Isabelle/Rational_Assignment.thy) adds an exact
checker for finite rational assignments. Acceptance proves that the
assignment is a real model of the explicit embedded query. A new actual
`Engine::solve` run, scenario `relu_sat`, returns SAT; its reported doubles are
reconstructed exactly and checked in Isabelle against the processed query,
the source query and the query before both native ReLU introductions.
Extraction, JSON decoding, floating-point refinement and the C++
implementation remain unverified.

## Checker and theorems

An assignment is `rat_assignment = (var × rat) list`. `assignment_value σ x`
is the value listed for `x`, or 0 if `x` is unlisted; `assignment_valuation σ`
embeds it into the real valuation `λx. of_rat (assignment_value σ x)`.

`check_rat_assignment Q σ` checks:

1. the listed variables are distinct (a duplicate rejects even if the first
   occurrence would be a model);
2. every linear atom `RatEq/RatLe/RatGe`, by exact rational evaluation;
3. every bound `RatLower/RatUpper`;
4. every ReLU atom, `σ(y) = max 0 (σ(x))` exactly.

| Theorem | Guarantee |
| --- | --- |
| `check_rat_linear_iff`, `check_rat_bound_iff`, `check_rat_relu_iff` | Each executable rational test agrees exactly with the real semantics of the embedded atom at the embedded valuation. |
| `check_rat_assignment_iff` | For distinct variables, acceptance is equivalent to `satisfies_query (assignment_valuation σ) (embed_query Q)`; the checker is complete for rational assignments. |
| `check_rat_assignment_sound`, `check_rat_assignment_satisfiable` | Acceptance gives a concrete real model and hence SAT of the explicit query. |
| `check_rat_assignment_excludes_certificate`, `unsatisfiable_rejects_assignment` | An accepted assignment excludes every accepted UNSAT certificate, and an UNSAT query admits no accepted assignment. |
| `fixed_aux_sequence_assignment_satisfiable`, `relu_aux_sequence_assignment_satisfiable` | An assignment accepted for a processed query proves its explicit starting query SAT, through the existing checked tableau and ReLU introduction equivalences. |

The checker is exported to `Marabou_Assignment_Checker.ML`; the
[smoke script](../Isabelle/tests/assignment_smoke.ML) runs 11 SML checks.
[Rational_Assignment_Examples.thy](../Isabelle/Rational_Assignment_Examples.thy)
proves acceptance for `x+y=2, -1<=x<=1, y=ReLU(x)` at `x=y=1`, an inactive-phase
model, and exact witnesses for the relaxations of the `relu_aux_inactive` and
`relu_chain` captures proved satisfiable earlier. It proves rejection of
duplicates, missing variables (value 0), a `1e-20` perturbation, bound and
ReLU violations, and every assignment for an UNSAT query.

## Native SAT capture

[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) adds `relu_sat`.
Its seven-variable starting query, with `b=x0, f=x1, c=x2, g=x3, z=x4, w=x5,
y=x6`, is:

```text
b = z,   c = w,   f + g = y,   f = ReLU(b),   g = ReLU(c)
b,c in [-2,2]; f,g in [0,2]; z in [1/2,2]; w in [-2,-1/4]; y in [0,1]
```

`b>=1/2` forces the first ReLU active and `c<=-1/4` forces the second
inactive. The real `ReluConstraint::transformToUseAuxVariables` method adds
auxiliaries `x7, x8` (7 → 9 variables), engine initialization adds five
tableau slacks `x9..x13` (→ 14), and `Engine::solve` returns true with exit
code SAT after five main-loop iterations, two simplex steps and no splits.
Proof production stays enabled; preprocessing and DeepSoI are disabled.

After solving, the harness calls `Engine::extractSolution` on a copy of the
processed query. With preprocessing disabled this is `Tableau::getValue(i)` for
every processed variable (`Engine.cpp`, lines 1736–1775). Each value is written
twice in `solver_relu_sat_assignment.json`: a round-trip decimal and an exact
hexadecimal float. The captured assignment is

```text
b = f = z = y = 1/2,   c = w = -2,   g = 0,   aux1 = 0,   aux2 = 2,   slacks 0.
```

The harness does not construct or repair these values.

## Import and reconstruction

[import_marabou_assignment.py](../Isabelle/tools/import_marabou_assignment.py)
takes the source query, tableau steps, processed query and assignment,
optionally with the before-ReLU query and the native introduction records.
It reuses the existing strict checks: every introduction must reproduce the
independent processed and source queries exactly.

Every hexadecimal value must be finite and well formed, and the decimal copy
must round to the same double. Reconstruction is untrusted and ordered:

1. the exact binary value of each double;
2. only if that fails the exact check, the simplest rational with
   denominator at most `10^6` within `1e-9` of each value.

If neither candidate is an exact model the import rejects; this says nothing
about satisfiability of the query. The theory header states which candidate
was used. For `relu_sat` the exact binary values already form a model, and the
capture driver requires that.

The generated [Imported_Marabou_Native_Relu_Sat.thy](../Isabelle/Imported_Marabou_Native_Relu_Sat.thy)
proves by `code_simp` that the steps reproduce the processed and source
queries, and proves:

| Theorem | Statement |
| --- | --- |
| `imported_query_model` | The exact assignment satisfies the explicit 14-variable processed query. |
| `imported_source_query_model` | It satisfies the explicit nine-variable source query. |
| `imported_before_relu_query_model` | It satisfies the explicit seven-variable starting query before both native ReLU introductions. |
| `imported_source_query_satisfiable_via_processed`, `imported_before_relu_query_satisfiable_via_processed` | The same SAT conclusions, derived instead through the checked introduction equivalences. |

`Rational_Assignment_Examples.native_sat_relu_violation_rejected` proves that
an assignment satisfying every processed row and bound but with `g=1/2` and
`c=-1/4` is rejected, and accepted once the ReLU atoms are removed.

[test_marabou_assignment.py](../Isabelle/tests/test_marabou_assignment.py) adds
15 tests: regeneration of the theory, run report and provenance, changed
values, the ReLU-only violation, exact use of consistent non-dyadic values,
repair of a single near miss, rejection of a far miss, decimal/hex
disagreement, malformed and overflowing hex values, strict assignment shape,
query substitution, before-query pairing, and an UNSAT source rejecting a
witness that its SAT relaxation accepts.

## Assurance boundary

The theorem concerns the explicit rational queries and the explicit rational
assignment in the generated theory. It does not claim that the C++ solver's
floating-point assignment satisfies anything; here its exact binary values
happen to. No theorem relates `Engine::solve` returning true to these
predicates, and failure to reconstruct an exact model would not refute a
native SAT answer. Serialized query numbers keep their exact-decimal meaning.

## Reproduction

From the project root, using a fresh output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_sat --output /tmp/marabou-sat-capture
isabelle build -d Isabelle -D /tmp/marabou-sat-capture
```

Replay saved evidence without running C++:

```sh
F=Isabelle/tests/fixtures/marabou/solver_relu_sat
python3 Isabelle/tools/import_marabou_assignment.py \
  --before-relu ${F}_before_relu.json --relu-steps ${F}_relu_steps.json \
  --source ${F}_source.json --steps ${F}_steps.json --query ${F}_query.json \
  --assignment ${F}_assignment.json \
  --output /tmp/marabou-sat-replay/Imported_Sat.thy --session
isabelle build -d Isabelle -D /tmp/marabou-sat-replay
```
