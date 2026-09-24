# Positive-auxiliary-lower-bound propagation and its native capture

Completed on 2026-09-23 against Marabou
`1c2f4788c32e2f4e407c356b763a8025c5578722`; neither upstream repository was
modified. This is the dual of the
[positive-output rule](RELU_OUTPUT_BOUND_PROPAGATION.md).

The rule is verified in
[ReLU_Aux_Lower_Bound_Propagation.thy](../Isabelle/ReLU_Aux_Lower_Bound_Propagation.thy),
added to the recursive checker and its SML export, and recognized by the
strict adapter. A new actual proof-enabled `Engine::solve` run, scenario
`relu_aux_inactive`, emits exactly this lemma. Its unmodified proof replays
through three checked tableau introductions to
`Imported_Marabou_Source_Relu_Aux_Inactive.imported_source_query_unsatisfiable`,
UNSAT of the explicit captured five-variable source over real valuations.
Extraction, JSON decoding, floating-point refinement and the C++
implementation remain unverified.

## Mathematical rule and exact checker

For real values:

```text
y = ReLU(x),   y - x - a = 0,   0 < l <= a
                         imply
                       y = 0,   hence  y <= u  for every u >= 0.
```

`relu_positive_aux_output_zero` proves this: `a > 0` makes `y ≠ x`, and a
ReLU output different from its input is zero. Strictness is essential.
`relu_zero_aux_does_not_fix_output` records the counterexample `x=y=1, a=0`:
the ReLU and equation hold, the auxiliary is nonnegative, and `y=1>0`.

`check_relu_aux_lower_output_upper_bound Q x y a l u pos neg` checks:

1. `ReLU x y` is present.
2. The **auxiliary** bound `RatLower a l` is present and `0<l` exactly.
3. Two exact linear implication witnesses prove `y-x-a<=0` and
   `-(y-x-a)<=0` from the current query.
4. `0<=u`, permitting the zero cap or a weaker output upper bound.

| Theorem | Guarantee |
| --- | --- |
| `check_relu_aux_lower_output_upper_bound_sound` | Every real model of the current embedded query satisfies the accepted output upper bound `y<=u`. |
| `rat_relu_aux_lower_output_upper_preserves_models` | Adding that bound preserves the entire real model set. |
| `unsatisfiable_relu_aux_lower_output_upper_bound` | UNSAT after adding a checked bound implies UNSAT before it. |
| `check_certificate_sound`, extended | The new constructor `Relu_Aux_Lower_Output_Upper x y a l u pos neg child` has its own induction case and composes with every other rule. Acceptance still implies real-semantic UNSAT. |

In the new constructor, `l` names an auxiliary lower bound and `u` an output
upper bound. `Relu_Output_Aux_Upper` has the same argument shape with the
opposite roles; the HOL examples prove that it cannot be used with an
auxiliary premise. Metadata never supplies the auxiliary equation.

## Actual source correspondence

| Source | Observed behavior / comparison |
| --- | --- |
| `src/engine/ReluConstraint.cpp::checkIfLowerBoundUpdateFixesPhase`, lines 125–133 | A positive `_aux` lower bound marks the phase inactive before the notification branches run. |
| `src/engine/ReluConstraint.cpp::notifyLowerBound`, lines 207–226 | `_auxVarInUse && variable == _aux && FloatUtils::isPositive(bound)`: in proof mode, `addLemmaExplanationAndTightenBound(_f, 0, UB, {_aux}, LB, *this, true, LEMMA_CERTIFICATION_TOLERANCE)`, then `tightenUpperBound(_b, -bound, *_tighteningRow)`. The second update is a linear explained tightening, not a PLC lemma. |
| `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound`, lines 414–494 | Records a `PLCLemma` with the causing variable's current explanation only when the affected bound actually tightens, then makes the conclusion a ground bound. |
| `src/engine/BoundManager.cpp::propagateTightenings`, lines 268–284 | Notifies watchers in ascending variable index, lower before upper. When several bounds tighten in one round this decides which ReLU rule fires; the capture uses it deliberately. |
| `src/proofs/Checker.cpp::checkReluLemma`, lines 685–689 | Accepts `causingVar == aux`, LB, `affectedVar == f`, UB if the explained bound plus epsilon is positive, returning 0. HOL instead requires strict positivity of the exact reconstructed rational premise. |
| `src/proofs/UnsatCertificateUtils.cpp`, `UNSATCertificateUtils::computeBound/getExplanationRowCombination` | The explanation is `e_aux + wᵀA`. The adapter reconstructs and validates an exact lower-bound implication for the actual causing variable. |
| `src/proofs/JsonWriter.cpp::writePLCLemmas` | Serializes `causVar/causBound`, `affVar/affBound`, the bound, `constraint = 0` and the explanation. |

The native epsilon could accept an auxiliary premise that is zero or tiny
negative in exact arithmetic; such a lemma is rejected here. No theorem
transfers the epsilon policy into real arithmetic, and no solver defect is
claimed.

## Import

[import_marabou_json.py](../Isabelle/tools/import_marabou_json.py) adds
`AuxLowerOutputUpperLemma` and `ReluAuxLowerOutputUpper`. A lemma with
`causBound=L`, `affBound=U` is matched against three patterns over all ReLU
metadata: input or output lower to auxiliary upper, and auxiliary lower to
output upper. Exactly one pattern and ReLU must match in total; otherwise the
import rejects, for example if another ReLU's metadata makes the same
cause/affected pair readable as input-lower-to-auxiliary-upper.

The premise is reconstructed for the actual causing auxiliary. It must be
strictly positive in exact arithmetic, the conclusion must be nonnegative, and
both equation directions need exact witnesses from the current query. As with
the other rules, a nonempty explanation becomes a checked `Linear_Bound`
premise without updating the native ground-bound state; only the PLC
conclusion does. The generated HOL term is
`Relu_Aux_Lower_Output_Upper x y a l u pos neg (child)`.

## Native capture

[capture.cpp](../Isabelle/tools/solver_capture/capture.cpp) adds scenario
`relu_aux_inactive`. The source query, with `a=x0, b=x1, f=x2, w=x3, t=x4`, is:

```text
a - w = 0,   f - t = 0,   f - b - a = 0,   f = ReLU(b) with auxiliary a
a in [0,2], b in [-2,2], f in [0,2], w in [1/4,2], t in [1/4,2]
```

Its linear relaxation is satisfiable (`a=w=f=t=1/4, b=0`), but the ReLU is
not: `f>0` would force `f=b` and `a=0<1/4`. Both the auxiliary and the output
receive positive lower bounds in the first bound-tightening round. The
auxiliary has the smaller index, so it is notified first, fixes the inactive
phase and emits the target lemma. The output rule then no longer fires.
This ordering was chosen by the harness; it is documented rather than hidden.

The run, with proof production enabled and preprocessing/DeepSoI disabled,
initialized with an unfixed phase and no lemmas, then `Engine::solve` returned
false with exit code UNSAT after two main-loop iterations, no simplex steps,
no splits and no delegation. The processed query has eight variables: three
tableau auxiliaries `x5..x7` fixed at 0. The writer output is:

```text
lemma: causVar 0 (aux) L -> affVar 2 (f) U, bound 0.0, expl [row 0: -1]
contradiction: [row 1: 1]
```

The exact replay is:

| Step | Checked HOL node |
| --- | --- |
| Explanation `e_a - (a - w - x5)` gives `a >= lb(w) + lb(x5) = 1/4` | `Linear_Bound (RatLower 0 (1/4))` |
| Rule with witnesses for `f-b-a=0` from row 2 and `x7=0` | `Relu_Aux_Lower_Output_Upper 1 2 0 (1/4) 0` |
| Row 1 with `f<=0`, `t>=1/4`, `x6>=0` | `Linear_Unsat`, margin `1/4` |

`Imported_Marabou_Solver_Relu_Aux_Inactive.imported_query_unsatisfiable`
proves the processed query UNSAT. The source theorem additionally checks the
three proposed introductions `(0,5), (1,6), (2,7)`, the native term order of
row 2, and exact equality with the independently captured processed query.

Scope of this capture: the auxiliary is an ordinary variable of the captured
source query, with its equation as a source row, as in `relu_aux` and
`relu_aux_active`. It is not produced by `transformToUseAuxVariables`.
In a native-introduction query the auxiliary receives the largest index, and
its positive lower bound arises only from bounds that trigger the input- or
output-based rules earlier; no such run is claimed.

## Examples and tests

[ReLU_Aux_Lower_Bound_Examples.thy](../Isabelle/ReLU_Aux_Lower_Bound_Examples.thy)
proves acceptance and UNSAT for a small single-rule query, exact tiny-positive
acceptance, a weaker cap `1/8`, and rejection of an insufficient cap `1/4`.
A positive auxiliary alone has the real model `x=-1/2, y=0, a=1/2`. At the
zero boundary `x=y=1, a=0` is a model; unsoundly adding `y<=0` creates a checked
linear contradiction, while the guarded rule rejects zero and tiny negative
premises. Wrong or absent premises (output, input or upper bounds on the
auxiliary), either missing equation witness, wrong variables, a missing ReLU
and a bad continuation reject. For the native capture, the processed query's
linear relaxation has a model, so no linear leaf alone can certify it, and
relaxing `w>=1/4` to `w>=0` in the source admits `a=w=0, b=f=t=1/4`; every
composed introduction/certificate is then rejected.

[test_marabou_aux_lower_bound.py](../Isabelle/tests/test_marabou_aux_lower_bound.py)
adds 24 importer tests: regeneration of the source theory, the unfiltered
native lemma and run report, removal or corruption of the lemma, a linear
premise not becoming ground state, the `w>=0` relaxation, exact strict
positivity at and near zero, input/output bounds not substituting, conclusion
strength, metadata not replacing the equation, missing fixed tableau bounds,
wrong coefficients or variables, cross-pattern ambiguity, unsupported
directions, exact rendering, recursion under both children of a split and
sibling isolation. `proof_tree_smoke.ML` adds 15 exported-SML checks.

## Remaining native ReLU lemma patterns

Proof-mode emission sites in `ReluConstraint.cpp` at the pinned revision
(calls to `addLemmaExplanationAndTightenBound`) and their current status:

| Line | Native lemma | Status |
| --- | --- | --- |
| 180 | `f` or `b` lower positive → `aux` upper 0 | Supported: `Relu_Output_Aux_Upper` / `Relu_Aux_Upper`. |
| 201 | `b` lower zero (`isZero`, tolerance) → `aux` upper 0 | Supported by `Relu_Aux_Upper` when the exact premise is `>=0`; a tiny negative premise is rejected as too strong. |
| 212 | `aux` lower positive → `f` upper 0 | Supported by this milestone. |
| 237 | `b` lower negative → `aux` upper `-bound` | Supported: `Relu_Aux_Upper`. |
| 294 | `f` upper non-positive, inactive phase → `b` upper 0 | **Unsupported.** Mathematically `x<=relu(x)=y<=u`, so `x<=c` for `u<=c`. Reached only when `f`'s upper bound became negative, immediately before `InfeasibleQueryException`. |
| 317 | `b` upper negative → `f` upper 0 | Supported: `Relu_Upper`. |
| 344 | `b` upper positive → `f` upper `bound` | Supported: `Relu_Upper`. |
| 366 | `aux` upper zero (`isZero`), active phase → `b` lower 0 | **Unsupported.** Mathematically `-x<=relu(-x)=a<=u` gives `x>=-u`; the exact rule needs `c<=-u`. This is the only emitted ReLU lemma with a lower-bound conclusion. |

Reachability of the two unsupported sites, from source inspection:

* Line 294 needs `f`'s upper bound to turn negative in a notification.
  `RowBoundTightener::tightenOnSingleInvertedBasisRow` (lines 307–311 and
  393–397) throws `InfeasibleQueryException` as soon as a row makes a
  variable's own bounds cross, before any notification. With `f>=0`, as in
  every capture here and after standard preprocessing, a negative row-derived
  upper bound on `f` therefore never reaches `notifyUpperBound`. Even when it
  does, the lemma is followed immediately by `InfeasibleQueryException`, and
  in auxiliary form it is linearly implied by `f-b-aux=0` and `aux>=0`.
* Line 366 needs `FloatUtils::isZero` of `aux`'s new upper bound (tolerance
  `1e-10`). Row tightening loosens every derived upper bound by
  `EXPLICIT_BASIS_BOUND_TIGHTENING_ROUNDING_CONSTANT = 1e-6`, so a row-derived
  zero cap does not qualify; an exact zero would have to come from another
  constraint sharing the variable.

A scratch probe,
[relu_lemma_reachability.cpp](../Isabelle/tools/solver_capture/probes/relu_lemma_reachability.cpp),
built from the pinned sources outside the capture harness, tried both sites
with `f>=0` and with `f>=-1` (preprocessing disabled). No run emitted either
lemma: three closed with row-combination contradictions, and the `aux_zero`
variant with `f>=-1` ended UNSAT with a **delegated** leaf, which the adapter
rejects by design. These probes are exploratory; they are not replay evidence
and are not claims about all queries. Both patterns are therefore left
unsupported until a capture actually needs them.

`Checker::checkReluLemma` also accepts `f` lower negative → `f` lower 0 and
`b` upper non-positive → `aux` lower `-bound`, but at this revision neither
is emitted as a PLC lemma in proof mode: the first tightening is guarded by
`!proofs`, the second is a linear update through the tightening row.
Sign, absolute value, max, leaky ReLU and disjunction lemmas are out of scope.

## Validation and reproduction

The session has 58 theories, all checked without admissions or added axioms.
All 221 importer tests pass. The regenerated exports pass 8 linear-leaf and
62 proof-tree SML checks. All 24 generated theories match regeneration.
There are eighteen canonical accepted writer fixtures: nine component
fixtures and nine replayed native scenarios. All eight earlier scenarios were
rerun with the final sources; data, reports and logs are byte-identical, and
only the hashes of the edited harness, capture script, importer and binary
changed in their provenance. See [BUILD_RESULT.md](BUILD_RESULT.md).

From the project root, using a fresh output directory:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_aux_inactive --output /tmp/marabou-aux-lower-capture
isabelle build -d Isabelle -D /tmp/marabou-aux-lower-capture
```

Replay saved evidence without running C++:

```sh
python3 Isabelle/tools/import_marabou_source.py \
  --source Isabelle/tests/fixtures/marabou/solver_relu_aux_inactive_source.json \
  --steps Isabelle/tests/fixtures/marabou/solver_relu_aux_inactive_steps.json \
  --query Isabelle/tests/fixtures/marabou/solver_relu_aux_inactive_query.json \
  --certificate Isabelle/tests/fixtures/marabou/solver_relu_aux_inactive.json \
  --output /tmp/marabou-aux-lower-replay/Imported_Aux_Lower.thy --session
isabelle build -d Isabelle -D /tmp/marabou-aux-lower-replay
```

The two unsupported emitted ReLU patterns above stay open until a capture
needs them; each would need its own exact guard, soundness proof and native
evidence. General preprocessing, verified decoding, SAT witnesses and
network-file correspondence remain outside this milestone.
