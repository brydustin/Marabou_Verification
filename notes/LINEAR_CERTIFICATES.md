# Exact certificates for linear leaves: initial investigation

This records the initial mathematical and source investigation. The subsequent
[rational linear-leaf checker](RATIONAL_LINEAR_CHECKER.md), [recursive checker
and restricted JSON adapter](CERTIFICATE_IMPORT.md) are now implemented.
Source observations concern Marabou commit
`1c2f4788c32e2f4e407c356b763a8025c5578722` only. C++ paths below are relative to
`upstream/Marabou/`.

## Mathematical requirement

For finitely many real inequalities `a_i · x ≤ b_i`, a sufficient UNSAT witness
is a finite vector of weights `λ_i` satisfying, **exactly**:

```text
λ_i ≥ 0 for every i
Σ_i λ_i a_i = 0          (every variable coefficient cancels)
Σ_i λ_i b_i < 0
```

Any model would yield `0 ≤ Σ_i λ_i b_i < 0`. This elementary soundness argument
needs no proof of the solver's algorithm or of certificate existence. For
rational input, Farkas' lemma also supplies a rational witness whenever the
finite linear system is infeasible. See the author's [Farkas lemma lecture
notes](https://people.math.carleton.ca/~kcheung/math/notes/MATH3801/04/4_1_farkas_lemma.html).
That completeness fact is background, not a theorem of this project.

For our affine syntax, move constants to the right; reverse `≥` inequalities;
encode equality as two inequalities; and encode bounds as single-variable
inequalities. Alternatively, equality rows can have unrestricted-sign
multipliers, with nonnegative multipliers reserved for inequalities. Every
translation used by a checker needs a semantics-preservation proof.

A source-aligned alternative uses homogeneous equalities `A x = 0`, current
justified bounds, and an unrestricted-sign row-combination vector `w`. Set
`c = wᵀ A` and compute

```text
U = Σ_j (if c_j > 0 then c_j*u_j
         else if c_j < 0 then c_j*l_j
         else 0).
```

If every selected bound is available and `U < 0` exactly, a model would have
`0 = wᵀ A x = Σ_j c_j*x_j ≤ U < 0`. Unlike the normalized-inequality certificate,
`c` need not be zero: its terms are bounded. This derivation explains why the
current row-vector evidence is useful. For nonhomogeneous rows `A x = b`, the
corresponding condition is `U < wᵀ b`. Contradictory input bounds are a separate
trivial case. Unbounded variables are harmless only when the bound selected
for a nonzero coefficient exists; no `0 * infinity` operation is needed.

## What the papers specify

* Isac, Barrett, Zhang and Katz, [Neural Network Verification with Proof
  Production](https://theory.stanford.edu/~barrett/pubs/IBZ%2B22.pdf) (FMCAD 2022),
  §IV, describes linear leaf contradictions using combinations of tableau rows
  and bounds, and proof trees for nonlinear case splits. Its calculus and
  mathematical arguments are not a verification of the pinned C++ revision.
* Desmartin et al., [A Certified Proof Checker for Deep Neural Network
  Verification](https://arxiv.org/html/2405.10611v1) (2024), §§III–V, develops
  Imarabou in Imandra, including a certified arithmetic core and structural
  results. The paper distinguishes those results from full checker
  certification. It is relevant prior work; no theorem or implementation from
  that development has been imported into our Isabelle session.

## What the inspected implementation does

| Stage | Source / observation |
| --- | --- |
| Enable evidence | `src/configuration/OptionParser.cpp` exposes `--prove-unsat`, stored as `Options::PRODUCE_PROOFS`. `Options::getLPSolverType` selects the native engine for proof mode. `src/engine/MarabouMain.cpp` turns off incompatible DeepSoI, SNC and MILP modes in this CLI path. |
| Linear infeasibility | `src/engine/Engine.cpp`, `performSimplexStep`: when no entering candidate remains, recompute stale assignment/cost information; if the fresh failure persists outside optimization mode, throw `InfeasibleQueryException`. Bound inconsistency also triggers failure. |
| Explain failure | `Engine::explainSimplexFailure` (line 3420) tries an inconsistent variable, tableau explanations, and cost-function explanations. It calls `certifyInfeasibility`, computes a contradiction vector, and stores it. If explanations fail, `markLeafToDelegate` records incomplete evidence. |
| Maintain explanations | `src/proofs/BoundExplainer.cpp`, `updateBoundExplanation`, `updateBoundExplanationSparse`, `getExplanation`; integrated through `BoundManager` and ground bounds. The vectors have `double` entries. |
| Leaf representation | `src/proofs/Contradiction.{h,cpp}` stores either a sparse row vector (`SparseUnsortedList`) or the index of an inconsistent-bound variable. `Engine::computeContradiction` combines bound explanations. |
| Tree representation | `src/proofs/UnsatCertificateNode.{h,cpp}` stores a head split, children, PLC lemmas, a contradiction, and visited/delegation/SAT flags. `PlcLemma.{h,cpp}` stores nonlinear bound-propagation evidence. |
| Existing check | `src/proofs/Checker.cpp`, `checkContradiction` (line 185): inconsistent ground bounds for an empty vector, otherwise a negative upper bound on the row combination. `UnsatCertificateUtils::computeCombinationUpperBound` performs sign-selected bound arithmetic in doubles and skips near-zero quantities using `FloatUtils`. PLC checking also tolerates errors. |
| Homogeneous rows | `Engine::addAuxiliaryVariables` (line 1290) adds a variable fixed to each equation's scalar, with coefficient `-1`, then sets the scalar to zero. One exact step now has a checked freshness guard and real-semantic preservation theorem in [TABLEAU_AUXILIARY.md](TABLEAU_AUXILIARY.md); the native loop and general input correspondence remain unverified. |
| Proof starting point | `Engine::processInputQuery` initializes the tree after preprocessing and tableau construction; `certifyUNSATCertificate` uses the processed query's initial bounds and matrix. The exporter does not establish the missing preprocessing theorem. |

Thus Marabou contains enough *kinds of evidence* for exact rechecking of some
linear leaves: original-to-that-tableau rows, ground bounds, and combination
coefficients. It is not yet established that every current output reconstructs
as a valid exact certificate, or that its context matches the original query.

## Available export paths and practical limitations

`src/proofs/JsonWriter.cpp::writeProofToJson` accepts the initial tableau,
bounds, PL constraints, and proof tree. Its number formatting uses fixed decimal
precision derived from `DEFAULT_EPSILON_FOR_COMPARISONS`. A search of `src/`
found the declaration and definition but no call site for this entry point in
the inspected revision; its existence is not evidence that the ordinary CLI
currently emits JSON certificates.

`src/proofs/AletheProofWriter.cpp` is wired into `Engine` when
`GlobalConfiguration::WRITE_ALETHE_PROOF` is true; this source constant defaults
to **false** in `src/configuration/GlobalConfiguration.cpp`. Its supported
activation set is currently just ReLU. `writeContradiction` and `farkasStrings`
emit `la_generic` or the configured `bounded_farkas` rule. Notably,
`linearCombinationMpq` converts double coefficients through `mpq_set_d` and
recomputes combinations using GMP rational arithmetic. This differs from the
native floating-point checker and should not be described as entirely
floating-point proof writing.

However, `SmtLibWriter::signedValue` emits finite fixed-precision decimal text.
The exact rational value of a finite binary double, the emitted decimal
rational, and an original source decimal need not be identical. An adapter must
choose an explicit query contract and recompute every accepted combination
against that exact query. Rationalizing an approximate witness may fail; that
should produce rejection, not a tolerance-based acceptance.

`AletheProofWriter::writeDelegatedLeaf` writes a `hole` rule. The C++
`Checker::checkNode` returns true for delegated leaves (and for marked SAT
leaves in its wider protocol). `Engine::certifyUNSATCertificate` warns that
delegated leaves need separate checking; in Alethe mode it sets its success flag
after writing and explicitly asks for external certification. These success
flags must not be treated as sufficient premises for an Isabelle UNSAT theorem.

The CLI `Marabou::solveQuery` calls this certificate path only when input
processing succeeded and solving returned UNSAT; infeasibility discovered
during preprocessing requires separate attention. No Marabou C++ build, solver
run, or emitted-certificate experiment was performed in the initial
investigation. The third milestone subsequently compiled the writer components
and replayed their output on hand-constructed evidence, as recorded in
[CERTIFICATE_IMPORT.md](CERTIFICATE_IMPORT.md); it still did not run the solver.

## Implementation status and next step

1. Implemented: rational expressions and queries with `embed_query` into the
   unchanged real semantic core.
2. Proved: exact normalization of rational equality, inequality and bound atoms
   to finite inequalities, all interpreted as expressions constrained to be
   nonpositive.
3. Implemented and proved sound: `check_linear_leaf`, checking nonnegative
   rational weights, matching lengths, aggregated duplicate coefficients,
   exact cancellation, and a strictly positive contradictory constant.
4. Proved acceptance and rejection examples, including fractions, a wrong sign,
   a small nonzero residual, and malformed lengths. The generated SML library
   compiles and passes executable tests. No certificate-existence or simplex
   theorem was required.
5. Implemented in the third milestone: recursive composition with ReLU
   splitting and `check_certificate_sound`. Each selected ReLU must be present
   and both children must pass. A strict JSON adapter reconstructs native
   row/bound evidence as candidate normalized weights, replayed in Isabelle.
   Missing/delegated evidence is rejected. The third milestone initially
   rejected all PLC lemmas; the fourth supports the restricted propagation
   pattern described in [RELU_BOUND_PROPAGATION.md](RELU_BOUND_PROPAGATION.md).
6. Implemented in the fifth milestone: [exact linear
   implications](RATIONAL_LINEAR_IMPLICATION.md), model-preserving bound
   additions, and nonempty tableau explanations for the same ReLU rule.
   The extended recursive soundness theorem checks each premise before use.

This simple inequality view can consume the mathematical information in a
bounded row certificate: equality multipliers contribute cancelling row
terms, and the sign-selected bounds contribute nonnegative inequality weights.
The adapter's output is now checked in HOL; the Python conversion itself is
untrusted. A general format, Alethe rule library,
propagation rules beyond the single checked upper-bound rule, and the
preprocessing bridge remain outside the current development.

A leaf checker may use only the linear atoms and bounds of a query even if some
ReLUs remain: an inconsistent linear relaxation already implies inconsistency
of the full query. That sound direction does not assert completeness.
