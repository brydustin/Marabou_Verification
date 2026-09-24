# Checking Marabou's native preprocessing

Completed on 2026-09-23 (milestone 24). Every earlier capture called
`Engine::processInputQuery(input, false)`, which skips Marabou's
`Preprocessor::preprocess`. The query-file workflow now has a `--preprocess`
mode that runs the real native preprocessing. Isabelle then checks the
*result* of preprocessing independently. The C++ preprocessor itself is not
verified.

```sh
python3 Isabelle/tools/verify_query_file.py --preprocess Isabelle/examples/preprocess_eliminate_unsat.mqx /tmp/mqx-pre
```

In this mode a file may use `le`/`ge` statements; the native
`makeAllEquationsEqualities` converts them. Variables may also lack bounds,
provided the native preprocessor derives finite ones. The theorems still
concern `decode_query` of the file's exact bytes.

## What the native preprocessor does

Pinned revision `1c2f4788c32e2f4e407c356b763a8025c5578722`,
`src/engine/Preprocessor.cpp`:

| Step | Source | Effect on the query |
| --- | --- | --- |
| `informConstraintsOfInitialBounds` | 1121–1142 | Phase statuses only (no bound change). |
| `makeAllEquationsEqualities` | 224–244 | LE/GE rows get slack `n, n+1, …` (+1 coefficient, one zero bound). |
| network-level reasoner, `removeRedundantAddendsInAllEquations` | 76–91, 218–222 | Combines duplicate terms. The WS-layer merge needs a network-level reasoner, which these queries do not build; the harness checks that it is absent. |
| `transformConstraintsIfNeeded` | 212–216 | Each ReLU gets auxiliary `n+slacks+j` with `f − b − aux = 0`, `aux ≥ 0`, `aux ≤ −lb(b)`. |
| `processEquations`, `processConstraints` | 246–590 | Interval tightening from rows and `ReluConstraint::getEntailedTightenings`, repeated up to 1000 rounds. May throw `InfeasibleQueryException`. |
| `processIdenticalVariables` | 592–650 | Merges `v1` into `v2` for rows `c(v1 − v2) = 0`. |
| `collectFixedValues`, `eliminateVariables` | 652–1011 | Fixes variables with equal bounds (and unused ones), substitutes them, removes empty rows and obsolete ReLUs, renumbers. |

Several of these steps use floating point with tolerances: accepting a
tightening needs an improvement of more than epsilon, and an interval
narrower than `PREPROCESSOR_ALMOST_FIXED_THRESHOLD` (`1e-5`) is snapped to a
point. Snapping can change the query's real meaning; see the example below.

## The checked relation

[Preprocessing_Projection.thy](../Isabelle/Preprocessing_Projection.thy)
defines two things.

* **Checked facts** (`fact`, `apply_fact`, `apply_facts`). Each fact adds
  constraints that every real model already satisfies: a linearly implied
  bound, the ReLU hull rows `y ≥ 0` and `y ≥ x`, a phase fact (the phase's
  equation and bound, keeping the ReLU, justified as in
  [phase fixing](RELU_PHASE_FIXING.md)), or one of the four existing ReLU
  propagation rules. `apply_facts_models` proves that the facts keep every
  model.
* **A projection** `Projection facts σ rows links`, checked by
  `check_projection Q pr P`. After the facts, it requires, for every
  normalized row `e ≤ 0` of `P`, an exact linear implication of
  `rename_expr σ e ≤ 0`. Each ReLU of `P`, renamed, must match a ReLU of `Q`
  up to proved equalities of input and output (`same_value`).

| Theorem | Guarantee |
| --- | --- |
| `check_projection_model` | Every real model `v` of `Q` gives the model `λu. v (σ u)` of `P`. |
| `check_projection_unsatisfiable` | UNSAT of `P` proves UNSAT of `Q`. |
| `check_projection_rejects_false_unsat` | If `Q` has a real model, no projection onto an unsatisfiable `P` is accepted. |

`σ` need not be injective, and nothing in `P` has to match the native
computation. Merged and fixed variables, removed rows and obsolete ReLUs are
all handled by implication: a merged variable's rows use the merge equality,
and a fixed variable's substitution uses its equal bounds.

## The chain for one file

[import_marabou_preprocessing.py](../Isabelle/tools/import_marabou_preprocessing.py)
(untrusted) proposes, and the generated replay theory proves by `code_simp`:

```text
decode_query bytes = Q          (decodes_like, as before)
Q --rat_introduce_inequality_aux_sequence-->  (native slack numbering)
  --rat_introduce_relu_aux_sequence-->        S2  (native auxiliary numbering and caps)
S2 --check_projection--> P      P = captured preprocessed query, or a crossing pair
P  --rat_introduce_fixed_aux_sequence-->  processed query   (existing tableau steps)
processed --check_certificate--> ⊥                          (the native proof)
```

The last two steps are the existing source replay: `P` plays the role of the
source query. The inequality and ReLU sequences are the verified
introductions of earlier milestones, applied in the native order with the
native variable numbers. UNSAT transfers back through
`check_projection_unsatisfiable`, `relu_aux_sequence_unsatisfiable_iff` and
`inequality_aux_sequence_unsatisfiable_iff`.

The facts are an exact re-derivation of the native tightenings (`Deriver`).
It runs each linear row, including hull and phase rows, as interval
propagation. It applies the phase-deciding and `getEntailedTightenings`
rules for ReLUs. Each derived bound carries its row-combination witness.
The rows of `P` are then proved from equalities (including fixed variables
as equalities) plus at most one inequality row.

**Preprocessing that finds UNSAT.** If `Preprocessor::preprocess` throws
`InfeasibleQueryException`, Marabou reports UNSAT with no proof at all. The
harness then records only that (`result: "infeasible"`) and confirms that
`Engine::processInputQuery(input, true)` also returns false with exit code
UNSAT. The importer re-derives the tightenings exactly until some variable's
lower bound exceeds its upper bound. It then projects `S2` onto the
two-bound query `{l ≤ y0, y0 ≤ u}` with `l > u`, which a one-row
`Linear_Unsat` refutes. If only a tolerance produced the native
infeasibility, no exact crossing exists and the run is rejected.

**SAT.** `Engine::extractSolution` maps the native solution back through
the preprocessor's merges, fixed values and renumbering to the file's
variables. The adapter checks those values directly against the file's
query, exactly or after the existing bounded small-denominator repair.
Isabelle proves `check_rat_assignment` for the decoded query.

## Capture

`capture.cpp` has a new mode, `file-preprocess QUERY.mqx`. The reader accepts
`le`/`ge` statements (as `Equation::LE/GE`) and missing bounds.
1. A standalone `Preprocessor::preprocess(input, PREPROCESSOR_ELIMINATE_VARIABLES)`
   call exposes the preprocessed query. It is written as `_source.json`,
   which the tableau steps start from.
2. The variable maps (`variableIsFixed`/`getFixedValue`,
   `variableIsMerged`/`getMergedIndex`, `getNewIndex`, Preprocessor.cpp
   1013–1044) are written as `_preprocessing.json`
   (`marabou-preprocessing-map-v1`).
3. The engine then runs `processInputQuery(input, true)`, with the real
   preprocessing inside it. Its preprocessor's maps must equal the recorded
   ones. The existing snapshot checks (processed query, tableau and ground
   bounds) are unchanged.
4. Root phase fixing ([RELU_PHASE_FIXING.md](RELU_PHASE_FIXING.md)) is
   recorded as in the non-preprocessing file mode.

`capture_marabou_solver.py --query-file F --preprocess` selects the mode and
skips the local inequality preparation. The pre-check then allows missing
bounds. The record is untrusted: a wrong map or query can only make
Isabelle reject.

## Examples

| File | Native behaviour | Checked result |
| --- | --- | --- |
| `preprocess_split_unsat.mqx` (the split scenario's query) | tightens `x3`, `x4` to `[−3/4, 3/4]` and the slack-like `x5…x8` to `≤ 3/2`, adds the ReLU auxiliary; then a native binary split proof | UNSAT: 11 facts, projection, 6 tableau steps, `Relu_Split` |
| `preprocess_eliminate_unsat.mqx` | as above, plus a copy `x9 = x0` and a fixed `x10 = 1/4`; merges the ReLU input `x0` into `x9`, eliminates `x10`, renumbers 12 → 10 variables | UNSAT: 13 facts; the ReLU link proves `x0 = x9`; native split proof |
| `preprocess_inequality_unsat.mqx`: `x0 + x1 ≥ 3`, `x2 − x1 ≤ −1`, `x2 = ReLU(x1)`, `x1`, `x2` partly unbounded | two native slacks; preprocessing throws `InfeasibleQueryException` | UNSAT: 14 facts derive `3 ≤ x1 ≤ 2` (including a phase fact) |
| `preprocess_mixed_sat.mqx`: `eq`, `le`, `ge`, a fixed variable, missing bounds, one ReLU | merges `x0` into `x3`, fixes `x2` and the ReLU auxiliary | SAT: exact model of the file's query |

Main-session theories: `Imported_Marabou_Preprocessed_*` (replay) and
`Imported_Marabou_Example_Preprocess_*` (theorems about the file bytes).
With `--preprocess`, the earlier example files `relu_chain_unsat.mqx` and
`inequality_relu_unsat.mqx` are refuted inside native preprocessing. Both
also went end to end through `verify_query_file.py --preprocess`: Isabelle
checked their exact re-derivations. `relu_sat.mqx` gave a checked model.

[Preprocessing_Projection_Examples.thy](../Isabelle/Preprocessing_Projection_Examples.thy)
proves the following by hand:
* a merge, a fixed variable, a tightened bound, renumbering and a ReLU link
  through the merge, together with rejections of a swapped renaming, an
  over-tight bound, missing link witnesses, a foreign ReLU and a forged fact;
* the ReLU fact kinds `Relu_Upper`, `Relu_Aux_Upper` and `Phase_Inactive`,
  with their rejections;
* a tolerance-snapping case. The source `x0 ∈ [0, 10⁻⁶]`, `x1 = x0 ≥ 10⁻⁶`
  has a model, while its snapped version `x0 = 0` is UNSAT.
  `snapped_projection_rejected` shows that no projection onto the snapped
  query is accepted.

[test_marabou_preprocessing.py](../Isabelle/tests/test_marabou_preprocessing.py)
(17 tests) covers:
* the route each example takes and the native slack and auxiliary numbering;
* strict parsing of the map record;
* rejection of unimplied or snapped bounds, swapped renamings, changed
  files, wrong artifact sets, forged facts and a perturbed assignment;
* a weakened file whose preprocessed query is still implied, which is still
  proved;
* the pre-check relaxation, the command-line checks, and the run reports.

## Assurance and limits

Trusted: the HOL kernel and the build-time file check. Untrusted: the C++
reader, `Preprocessor`, the engine and its extraction, the harness, the
map record and all Python. A theorem about a `--preprocess` run is about the
file's bytes. It does not say that Marabou's preprocessor is correct: only
that this run's result was implied, or that its infeasibility was re-derived
exactly.

Limits:
* The re-derivation is bounded (40 rounds, 400 facts). A preprocessing result
  that needs a longer exact derivation, or that holds only up to tolerance,
  is rejected.
* Only the native path without a network-level reasoner is supported. The
  harness checks that none exists. Queries from network files, which would
  enable WS-layer merging and symbolic bound tightening, are out of scope.
* `removeRedundantEquations` in `processInputQuery` must not remove rows,
  or the tableau-step check fails.
