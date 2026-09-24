# Certified ReLU phases fixed before solving

Completed on 2026-09-23 (milestone 23). Before this milestone the file
workflow rejected every query whose initial bounds already decide a ReLU
phase (`ReLU phase fixed before solving (uncertified initial phase fixing)`).
Native Marabou applies such phases without any explanation, so no native
proof could be replayed. The checker now justifies each such phase exactly, and
native proofs that depend on it replay in HOL.

## What native Marabou does

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`, preprocessing
disabled (the configuration of every capture here):

1. `Engine::invokePreprocessor` copies the query and calls
   `Preprocessor::informConstraintsOfInitialBounds` (Preprocessor.cpp
   1121–1142). No bound manager is registered yet, so
   `ReluConstraint::notifyLowerBound`/`notifyUpperBound` only record the bound
   and call `checkIfLowerBoundUpdateFixesPhase` /
   `checkIfUpperBoundUpdateFixesPhase` (ReluConstraint.cpp 125–146). These use
   epsilon tests. Active: `b ≥ −ε`, `f > ε`, or `aux ≈ 0` above. Inactive:
   `b ≤ ε` or `f ≤ ε` (the non-proof policy, because no bound manager
   exists yet), or `aux > ε` below. No PLC lemma is recorded.
2. `Engine::solve` registers the bound manager and immediately calls
   `applyAllValidConstraintCaseSplits` (Engine.cpp 207–208). For each fixed,
   active constraint, `applyValidConstraintCaseSplit` disables it and applies
   `getValidCaseSplit()`. With an auxiliary in use that is `b ≥ 0, aux ≤ 0`
   (active) or `b ≤ 0, f ≤ 0` (inactive).
3. `Engine::applySplit` (Engine.cpp 2108–2134), in proof mode, adds each split
   bound that is strictly tighter than the current one as a **new ground
   bound** (`addGroundBound(..., isPhaseFixing = true)`) and resets its
   explanation. Later explanations and contradictions use it as a given
   fact. The certificate tree has no node for it, so the native
   `Checker` cannot see it.

## The checked rule

[ReLU_Phase_Fixing.thy](../Isabelle/ReLU_Phase_Fixing.thy):

```isabelle
relu_hull_query Q x y   (* adds y ≥ 0 and y − x ≥ 0 in front of Q's atoms *)

check_relu_fixed_active Q x y b ws ⟷
  ReLU x y ∈ set (rat_relu_atoms Q) ∧ active_phase_bound x y b ∧
  check_linear_bound (relu_hull_query Q x y) b ws
```

`active_phase_bound` allows `b = RatLower x l` with `0 ≤ l`, or
`RatLower y l` with `0 < l`. The inactive version allows `RatUpper x u` or
`RatUpper y u` with `u ≤ 0`. The weights prove that bound from the query
plus the two inequalities every ReLU satisfies (its "hull" rows).

| Theorem | Guarantee |
| --- | --- |
| `relu_hull_query_models` | Every real model of `Q` satisfies the hull rows of a present ReLU. |
| `check_relu_fixed_active_sound` / `_inactive_sound` | If accepted, every real model has `0 ≤ x ∧ y = x` (resp. `x ≤ 0 ∧ y = 0`). |
| `relu_fixed_active_models` / `_inactive_models` | If accepted, the phase's split query (the ReLU replaced by that phase's linear constraints) has **exactly** the models of `Q`. |
| `unsatisfiable_relu_fixed_active` / `_inactive` | UNSAT of the phase's split query gives UNSAT of `Q`. |

[Rational_Proof_Trees.thy](../Isabelle/Rational_Proof_Trees.thy) adds two
certificate constructors, checked against the checker-built split query:

```isabelle
| Relu_Fix_Active var var rat_bound "rat list" certificate
| Relu_Fix_Inactive var var rat_bound "rat list" certificate
```

`check_certificate_sound` covers them. They are exported to
`Marabou_Proof_Checker.ML`; the SML smoke script now has 72 checks, 10 of
them for these constructors.

Only exact signs are accepted. With `x = −1/2, y = 0` the ReLU holds and
`x ≥ −1/2`, `y ≥ 0` are true, yet the active phase fails, so neither a
negative input bound nor a zero output bound fixes it
(`phase_premises_need_exact_signs`). In
[ReLU_Phase_Fixing_Examples.thy](../Isabelle/ReLU_Phase_Fixing_Examples.thy),
`tiny_positive` has an input upper bound of `10⁻¹²`, which an epsilon test
would treat as nonpositive. That query has exactly one model,
`x = y = 10⁻¹²`, but its inactive split is UNSAT, so an unchecked phase fix
would prove a false UNSAT. The exact check rejects the premise, and
`tiny_positive_has_no_certificate` shows that no certificate is accepted.
The examples also cover:
* fixing each phase from an input or an output bound;
* an active phase that needs the hull row `y ≥ 0` (`hull_row_is_needed`
  proves that no weights work without it);
* linear relaxations with models, showing each phase fix is essential;
* rejection of wrong directions, absent or reversed ReLUs, missing or
  negative weights, and bad continuations.

## Capture and import

In file mode, [capture.cpp](../Isabelle/tools/solver_capture/capture.cpp)
no longer rejects a fixed phase. After `processInputQuery` it reads the
engine's own constraints. It writes `solver_file_phase_fixing.json`
(`marabou-root-phase-fixing-v1`) listing each fixed ReLU `(b, f, aux)`, its
phase, and the bounds of `getValidCaseSplit()`. The run report sets
`relu_phase_unfixed_before_solve` to `false`. The ten hard-coded scenarios
still require every phase to be open, and their outputs are byte-identical.

The record is untrusted. [import_marabou_json.py](../Isabelle/tools/import_marabou_json.py)
(`parse_phase_fixing`) requires each entry to name a ReLU of the processed
query and its bounds to be exactly that phase's native valid split.
`phase_premise` then looks for an exact premise:
* active: the current lower bound of `b` if it is `≥ 0`; else that of `f` if
  it is `> 0`; else `b ≥ 0` derived through the hull row `f ≥ 0`;
* inactive: the upper bound of `b` or of `f` if it is `≤ 0`.

It rejects the run if none works. It inserts `Relu_Fix_*` at the proof root in
record order, then reconstructs the native tree against the split query. The
split bounds are recorded as ground bounds, as `applySplit` does. An
epsilon-decided phase such as `b ≤ 10⁻¹²` has no exact premise and is
rejected. An exact model (SAT) needs no phase justification, but a malformed
record is still rejected.

## Native examples

| File | Native behaviour | Result |
| --- | --- | --- |
| `phase_active_unsat.mqx`: `b ∈ [−1,1]`, `f ∈ [3/2,2]`, `b = z` | active because `f > 0`; split bounds `b ≥ 0`, `aux ≤ 0` both tighter; one-row contradiction | UNSAT: `Relu_Fix_Active` then a leaf |
| `phase_inactive_unsat.mqx`: `b ≤ −1/2`, `f = w ≥ 1/4` | inactive because `b < 0`; `f ≤ 0` tighter | UNSAT: `Relu_Fix_Inactive` then a leaf |
| `phase_chain_unsat.mqx`: two ReLUs, `c = f − 1/4`, `g = w ≥ 1/4` | first ReLU inactive at the root; the second gets two native PLC lemmas whose explanations use the unexplained `f ≤ 0` | UNSAT: fix, then linear premise, `Relu_Aux_Upper`, linear premise, `Relu_Upper`, leaf |
| `phase_fixed_sat.mqx` | active at the root | SAT: exact model of the file's query |

For each of the three UNSAT runs, reconstruction **fails** if the phase record
is removed (tested). Their native evidence depends on the unexplained
phase bound. With the checked fix, the complete unmodified native proof
replays. The generated replay theories `Imported_Marabou_File_Phase_*` and
theorem theories `Imported_Marabou_Example_Phase_*` are in the main session.
The theorems concern the decoded bytes of each example file.
[test_marabou_phase_fixing.py](../Isabelle/tests/test_marabou_phase_fixing.py)
(11 tests) covers:
* strict parsing of the record;
* the premise found for each example;
* that the record is necessary, and that the wrong phase is rejected;
* epsilon premises;
* the hull-row premise;
* the SAT case;
* the generated theories.

## Assurance and limits

The theorem relies on the HOL kernel and the existing build-time file check.
The record, harness, solver and importer are untrusted: a wrong record can
only make Isabelle reject. Only ReLUs are covered, and only phases fixed
before `solve()`. Phases fixed later arrive with PLC lemmas and were already
handled. The aux-lower trigger (`aux > ε`) cannot occur in file mode,
where the auxiliary's initial lower bound is 0. The importer does not look
for it and would reject such a run.
