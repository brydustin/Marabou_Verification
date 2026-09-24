# Previously rejected exploratory two-ReLU capture

These seven JSON files are unchanged output from an actual exploratory native
run during the finite-ReLU-introduction milestone. They were initially
rejected because one rule was unsupported. The
[positive-output rule milestone](../../../../../notes/RELU_OUTPUT_BOUND_PROPAGATION.md)
now replays the complete unchanged bundle in Isabelle. The directory name
is retained to preserve its provenance and historical references.
The separate `relu_sequence` scenario in the parent directory uses a different query.

The exploratory query had `b=x0, f=x1, c=x2, g=x3, z=x4, w=x5`:

```text
b=z, c=f-1/4, g=w, f=ReLU(b), g=ReLU(c)
b,c in [-2,2]; f,g in [0,2]; z in [-2,-1/2]; w in [1/4,2]
```

The harness called `transformToUseAuxVariables` for both plain ReLUs, after
`Preprocessor::informConstraintsOfInitialBounds`, then initialized without
general preprocessing and ran `Engine::solve(10)` with proofs enabled.
It recorded two introductions (6 → 8 variables), five tableau steps (8 → 13),
and a native UNSAT result with four PLC lemmas and one explained leaf.

The fourth lemma derives auxiliary `x7 <= 0` from an explained positive
lower bound on **output** `x3` of `ReLU(x2,x3)`. Its native source is
`src/engine/ReluConstraint.cpp::notifyLowerBound`, in the branch
`(variable == _f || variable == _b) && FloatUtils::isPositive(bound)`.
The importer now distinguishes output-based and input-based auxiliary rules,
checks strict positivity and the auxiliary equation exactly, and replays all
four lemmas. Nothing is filtered out or treated as an assumption.
`Imported_Marabou_Native_Relu_Chain.imported_before_relu_query_unsatisfiable`
proves UNSAT of the explicit six-variable before-query.

The exploratory command was a direct invocation of the locally built capture
binary into `Isabelle/generated/relu_sequence_probe_1`, before changing the
test-query construction to the final sum-of-outputs example. Its `scenario`
field therefore says `relu_sequence`, but these files are isolated here.
The full capture driver was not used: there is no saved build provenance or
binary hash for this original trial. A new `relu_chain` scenario reproduces
all six data inputs byte-for-byte and records full build/run provenance in the
parent directory under `solver_relu_chain*`. This does not retroactively
attest the historical execution. Tests check both replay and byte equality.
The upstream revision was `1c2f4788c32e2f4e407c356b763a8025c5578722`.
