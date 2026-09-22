# Verified ReLU auxiliary upper bounds and native replay

Completed on 2026-09-22 with Isabelle2025-2 and unchanged Marabou revision
`1c2f4788c32e2f4e407c356b763a8025c5578722`. This adds the auxiliary-bound
rule encountered during the earlier ReLU capture experiments, extends the
recursive soundness proof, and replays two new actual solver executions.
The previously rejected negative variant's query and native proof are unchanged.

## Mathematical rule and checked premises

For real values:

```text
b ≥ l       f = ReLU(b)       f - b - a = 0       max(0,-l) ≤ u
----------------------------------------------------------------
                              a ≤ u
```

The identity `ReLU(b) - b = ReLU(-b)` proves the rule. Negative, zero, and
positive lower bounds are covered. A weaker upper conclusion is permitted;
no tolerance is used, and the input bound must be checked before propagation.

[ReLU_Aux_Bound_Propagation.thy](../Isabelle/ReLU_Aux_Bound_Propagation.thy)
defines `relu_aux_expr b f a = f-b-a` as a rational expression.
`check_relu_aux_upper_bound Q b f a l u pos neg` requires:

1. `ReLU b f` occurs in the current query.
2. `RatLower b l` occurs in the current query.
3. `pos` passes `check_linear_implication` for `f-b-a ≤ 0`.
4. `neg` passes that checker for `-(f-b-a) ≤ 0`.
5. `max(0,-l) ≤ u` holds exactly.

The two independent linear witnesses establish the auxiliary equation.
Metadata naming an auxiliary variable is insufficient. For a native row
`f-b-a-s=0`, both bounds fixing `s=0` supply those witnesses. If a required
bound or the row is missing, reconstruction fails. The generic HOL rule can
use other exactly proved representations of the same equation.

| Theorem | Assurance over real valuations |
| --- | --- |
| `relu_aux_identity`, `relu_aux_upper_bound` | The identity and mathematical implication above. |
| `check_relu_aux_upper_bound_sound` | Every model of the current query satisfies an accepted auxiliary upper bound. |
| `rat_relu_aux_upper_preserves_models` | Adding that bound preserves the complete real model set. |
| `unsatisfiable_relu_aux_upper_bound` | UNSAT after a checked addition implies UNSAT before it. |
| Extended `check_certificate_sound` | All accepted finite certificates, including the new constructor, exclude every real model of the root. |

The recursive datatype adds:

```isabelle
Relu_Aux_Upper var var var rat rat "rat list" "rat list" certificate
```

Its fields are input, output, auxiliary, input lower bound, auxiliary upper
bound, positive/negative equation witnesses, and continuation. The checker
verifies **all** premises against the current query, then adds the upper bound
and checks the continuation. The two equation witnesses are part of the same
node; no asserted equality or arbitrary child query is imported.
The constructor and rule checker are exported to Standard ML.

## Correspondence to the pinned source

Paths are relative to `upstream/Marabou/`. These are observed C++ behaviors;
the mathematical rule above is our exact model, not a proof of those methods.

| Source | Relevant behavior |
| --- | --- |
| `src/engine/ReluConstraint.cpp::transformToUseAuxVariables` | Introduces `f-b-a=0` and nonnegative `a`; chooses its upper bound from the input lower bound. This transformation itself is not verified or invoked by our auxiliary-form capture inputs. |
| `ReluConstraint.cpp::notifyLowerBound` | With proof production and an unfixed phase, a negative input lower bound can emit `a ≤ -l`; a positive/zero input lower bound emits `a ≤ 0`. The output-lower-to-auxiliary rule in this method remains outside our supported pattern. |
| `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound` | Captures the causing variable's lower explanation, appends the native `PLCLemma`, promotes the auxiliary upper bound to a ground bound, and resets its explanation. |
| `src/proofs/BoundExplainer.cpp::updateBoundExplanation/getExplanation` | Supplies signed weights over original tableau rows for the linear premise. |
| `src/proofs/UnsatCertificateUtils.cpp::computeBound/getExplanationRowCombination/computeCombinationLowerBound` | Computes `c=e_b+wᵀA`, then uses lower ground bounds for positive coefficients and upper ground bounds for negative coefficients. |
| `src/proofs/Checker.cpp::checkReluLemma` | Recognizes negative and nonnegative input-lower to auxiliary-upper cases, using floating-point tolerances. These comparisons are not inherited by the HOL checker. |
| `src/proofs/JsonWriter.cpp::writePLCLemmas` | Serializes `causBound="L"`, `affBound="U"`, `causVar=b`, `affVar=a`, `constraint=0`, and the sparse explanation. |
| `src/engine/Engine.cpp::addAuxiliaryVariables` | Appends scalar-fixed tableau variables. The capture independently snapshots the resulting equations and initial ground bounds. |

The generic HOL rule does not model the C++ active/inactive phase flags.
Its exact premises justify the bound for every real model, independently
of whether a particular native notification would emit a new lemma.

## Exact import of lower explanations and auxiliary equations

The adapter recognizes only the input/auxiliary pair of a unique remaining
ReLU in the metadata. Other causing variables, affected lower bounds, other
activation types, multiple causes, and unknown fields remain rejected.
The metadata selects a candidate equation; it does not prove it.

For a nonempty explanation it forms:

```text
c = e_b + wᵀA
L = Σ(c_j > 0) c_j l_j + Σ(c_j < 0) c_j u_j.
```

The proposed lower bound has this normalized derivation:

```text
L - b = (wᵀA)v
      + Σ(c_j > 0) c_j (l_j - v_j)
      + Σ(c_j < 0) (-c_j) (v_j - u_j) ≤ 0.
```

The equality signs are reversed relative to the previous upper-bound
reconstruction. Each used ground bound must have an exact witness in the
current query. The importer emits `Linear_Bound (RatLower b L) ...` before
the auxiliary node. Empty explanations use the native ground lower bound;
nonempty exact-zero vectors reconstruct it without discarding tiny nonzero
coefficients.

For the auxiliary equation, the adapter uses its existing exact equality-span
elimination and, when needed, one available bound for each inequality. It
returns two nonnegative normalized-row weight lists. This reconstruction is
deliberately incomplete; the HOL checker accepts any valid witnesses, whereas
the adapter rejects when its limited search cannot find them.

Only the PLC conclusion updates native ground state. The checked input lower
premise is inserted into the HOL query alone. Equation witnesses are checked
before the proposed auxiliary upper bound is added. Later lemmas can use an
earlier auxiliary conclusion; they cannot use a future one or a sibling's.
Resource accounting still charges at most two unary nodes per native lemma.

## Actual captured executions

Both scenarios start with `b=x0, f=x1, z=x2, w=x3, a=x4` and `f=ReLU(b)`.
The capture supplies the auxiliary-form constraint and its equation as input
data. It never constructs, prunes, or replaces native proof evidence.
Proof production is enabled, preprocessing/DeepSoI disabled, and seed 1 used.
Initialization succeeds with the phase unfixed and no proof lemmas.

### Broader negative variant: `--scenario relu_aux`

Input equations, in order: `b=z`, `f=w`, `f-b-a=0`.
Bounds: `-2≤b≤2`, `0≤f≤2`, `-2≤z≤-1/2`, `1/4≤w≤2`, `0≤a≤2`.
Initialization appends `s0=x5`, `s1=x6`, `s2=x7`, all fixed to zero:

```text
A0: b-z-s0=0
A1: f-w-s1=0
A2: -b+f-a-s2=0
```

The solver emits an auxiliary-upper lemma with explanation weights `-1` on
row 1 and `+1` on row 2. Thus `e_b-A1+A2 = e_w-e_a+e_s1-e_s2`, whose lower
ground sum is `1/4-2=-7/4`. The emitted upper bound is `1.750002`.
Decoded exactly, it is `875001/500000 = 7/4 + 1/500000`, a valid weaker
conclusion. There is no assumption that this decimal equals its binary double.
The initial query data are dyadic; this new **certificate bound is not**.

Next, the solver emits the earlier explained output-upper lemma
`b≤-1/2 ⇒ f≤0`. A row-1 terminal contradiction then gives `1/4≤0`.
The extra auxiliary lemma is now fully checked, although this particular
terminal contradiction does not need it. The complete query/proof bytes
match the previously rejected exploratory capture.

### Necessary auxiliary inference: `--scenario relu_aux_active`

Input equations, in order: `b=z`, `a=w`, `f-b-a=0`.
Bounds: `-1≤b≤2`, `0≤f≤2`, `1/2≤z≤2`, `1/4≤w≤2`, `0≤a≤2`.
The rows are `A0=b-z-s0`, `A1=a-w-s1`, `A2=-b+f-a-s2`, each zero.

Exactly one lemma is emitted: input lower to auxiliary upper, with explanation
`-1` on row 0. It yields `b≥1/2`, then `a≤0`. The terminal contradiction uses
row 1:

```text
(-a+w+s1) + a + (1/4-w) + (-s1) = 1/4 ≤ 0.
```

[ReLU_Aux_Bound_Examples.thy](../Isabelle/ReLU_Aux_Bound_Examples.thy) proves
the captured linear relaxation has the real model
`(b,f,z,w,a,s0,s1,s2)=(1/2,3/4,1/2,1/4,1/4,0,0,0)`.
Consequently, no linear-leaf certificate alone can certify this root.
Removing the sole nonlinear lemma makes import of this evidence fail.

Both runs report one explained, nondelegated leaf, one explicit-basis tightening
call, zero simplex steps, no child proof nodes, and native main-loop counter 2
(which includes the pre-loop statistics call). There are two native lemmas in
the negative case and one in the active case. The pre-solve query snapshots
are compared against every native tableau entry and ground bound.

## Artifacts and validation

The five saved files for each `solver_relu_aux` and `solver_relu_aux_active`
prefix are in [tests/fixtures/marabou](../Isabelle/tests/fixtures/marabou):
query snapshot, native proof, run report, stdout/stderr log, and provenance.
Provenance includes the pinned revision, build inputs, binary/library hashes,
capture/adapter hashes, and output hashes. It is not a HOL premise.
The earlier two captures were rerun with the final shared harness; their
query/proof bytes stayed unchanged and their provenance was refreshed.

With the dependencies in [SOLVER_CAPTURE.md](SOLVER_CAPTURE.md), use empty/new
output directories:

```sh
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux --output /tmp/marabou-aux-capture
isabelle build -d Isabelle -D /tmp/marabou-aux-capture
python3 Isabelle/tools/capture_marabou_solver.py --scenario relu_aux_active --output /tmp/marabou-aux-active
isabelle build -d Isabelle -D /tmp/marabou-aux-active
```

The generated [negative](../Isabelle/Imported_Marabou_Solver_Relu_Aux.thy) and
[active](../Isabelle/Imported_Marabou_Solver_Relu_Aux_Active.thy) theories are in
the main session. Each proves acceptance with `code_simp` and derives real
UNSAT from `check_certificate_sound`. There are now 32 project theories,
13 imported certificates, and four actual solver captures.

Validation includes 86 importer tests and 35 exported SML tree-checker tests.
HOL examples cover negative/zero/positive lower bounds, weaker conclusions,
overstrong conclusions, both equation witnesses, wrong variables, missing
premises, and unchecked continuations. A real model proves that omitting the
auxiliary equation can invalidate the desired bound.
Import tests also cover both slack bounds, signed lower explanations, exact
tiny coefficients, native ground updates, original-row indices under splits,
sibling isolation, and corruption of actual capture data.
Exact builds and commands are in [BUILD_RESULT.md](BUILD_RESULT.md).

## Assurance and next target

The new rule and its composition are proved over the existing real semantics.
Both explicit processed queries have unconditional HOL UNSAT theorems backed
by native solver-produced evidence. The decoder, capture, floating-point code,
preprocessing, auxiliary introduction, and original-query correspondence
remain unverified. No incorrect solver result or checker soundness failure
was observed.

The next small integration target is a solver-produced binary ReLU split
whose two children replay with supported evidence. The separate semantic
target remains a verified bridge through auxiliary introduction to the
original query. Other ReLU propagation patterns remain outside this extension.
