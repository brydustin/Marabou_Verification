# Marabou verification: continuation handoff for Claude

Prepared 2026-09-23. Last completed implementation milestone: 2026-09-22.

**Historical snapshot:** the milestones described below as future work have
since advanced. Read [notes/CONTINUATION_LOG.md](notes/CONTINUATION_LOG.md)
and the latest [build record](notes/BUILD_RESULT.md) before choosing a task.
Claude completed milestones 17–20; the subsequent
[signed slack development](notes/INEQUALITY_AUXILIARY.md) continues the
preprocessing work. Preserve this file as the original handoff, not a current
list of unfinished tasks.

This is a continuation task, not a request to restart the project or merely
propose a plan. Read the actual files, preserve the completed work, and make
incremental progress through the remaining tasks below. Use persistent
checkpoint notes so repeated invocations, including a user-configured
`/loop`, continue from the last completed step.

## 1. Objective and scope

Project directory:

```text
/home/dusty/Desktop/Marabou Verification
```

The goal is an Isabelle/HOL-verified basis for trusting supported Marabou
results through a small exact certificate checker:

```text
Marabou query + solver-produced evidence
    → explicit mathematical query and candidate certificate
    → Isabelle-checked transformations and certificate checking
    → theorem about SAT or UNSAT of that explicit query.
```

The initial mathematical fragment is real linear arithmetic, ReLU, case
splitting, exact terminal contradictions, and checked auxiliary introductions.
It already has working native captures and Isabelle replay.

The project does **not** initially aim to verify the entire existing C++
implementation. Do not expand into ONNX/TensorFlow parsing, all activations,
DeepPoly, DeepSoI, parallel search, Split-and-Conquer, Gurobi, or general
floating-point implementation correctness merely to claim completion.

“Finish” needs a stated boundary: a usable, checked pipeline for a documented
restricted query/evidence language is a meaningful release. Universal support
for every Marabou query or a correctness theorem for all C++ is a different,
much larger project. Work through the bounded roadmap below and report what
each theorem actually establishes.

## 2. Non-negotiable development rules

1. Use Isabelle/HOL, not Isabelle/FOL. Keep the session
   `Marabou_Verification` compiling at every meaningful checkpoint.
2. Finish proofs. No `sorry`, `oops`, `axiomatization`, added axioms,
   untrusted oracles, or equivalent proof bypasses in completed theories.
   Retain `quick_and_dirty = false`. Explicit premises must be justified by
   the mathematical contract or checked evidence, not hidden assumptions
   that the solver is correct.
3. Prefer simple definitions and proofs. Existing replay uses proof-producing
   `code_simp`. Passing Python or exported SML tests is not a substitute for
   Isabelle proof replay.
4. Inspect actual pinned Marabou source before modeling its behavior.
   Distinguish C++ behavior, paper descriptions, and chosen mathematical
   abstractions. Record exact files, classes and functions.
5. Keep the development under `Isabelle/` and documentation under `notes/`.
   Do not modify upstream repositories unless explicitly necessary and within
   the user's authorization. Existing capture tools build upstream unchanged.
6. Check all required certificate nodes, premises and children. Unsupported,
   malformed, missing or inexact evidence must fail closed. Do not delete
   difficult native lemmas or replace them with hand-written proof data and
   then claim to have replayed the original proof.
7. Use exact rational certificate data with real-valued semantics. Do not
   inherit native tolerance comparisons into an exact theorem.
8. Preserve source/proof artifacts and provenance honestly. A hash is
   provenance, not a logical assumption or proof of faithful extraction.
9. Continue routine authorized development without requesting permission at
   every step. Respect the host's actual filesystem and execution permissions.
   Ask only when an essential requirement or authority is missing.
10. Do not claim “Marabou is verified.” State the theorem, explicit query,
    checked transformations, and remaining trust boundary.

## 3. Preserve this working tree

The project has extensive **uncommitted modified and untracked work**,
including completed Isabelle theories, tools and captured evidence. This is
the current baseline, not disposable scratch data.

On 2026-09-23 the root HEAD was
`60016b0ba2a1d2b35f9480d30f7dd35ed8db2284`; staging was empty.
That commit alone does **not** contain the complete current development.
Do not use `git clean`, `reset --hard`, broad checkout/revert, or reconstruct
the project only from HEAD. Do not stage, commit or publish inherited changes
as though they were all newly authored by you. Follow the user's Git workflow.

Before editing, inspect `git status --short` and applicable local instructions.
No applicable `AGENTS.md` was found in the workspace or its ancestors at this
handoff. Recheck if the environment changes.

Upstream repositories, clean at the last implementation audit:

| Directory | Pinned revision |
| --- | --- |
| `upstream/Marabou` | `1c2f4788c32e2f4e407c356b763a8025c5578722` |
| `upstream/ReluplexCav2017` | `60b482eec832c891cb59c0966c9821e40051c082` |

Reluplex is a historical reference, not the primary verification target.
Do not update these pins as an incidental part of the next rule.

## 4. Read these first

Read selectively; old milestone notes intentionally contain historical counts
and earlier “next targets” that have since been completed.

1. [README.md](README.md): current scope, file map and assurance table.
2. [notes/RELU_OUTPUT_BOUND_PROPAGATION.md](notes/RELU_OUTPUT_BOUND_PROPAGATION.md):
   latest completed rule, native chain, boundary tests and immediate next target.
3. [notes/BUILD_RESULT.md](notes/BUILD_RESULT.md), especially **Sixteenth milestone**:
   latest exact build and test results. Earlier milestones are historical.
4. [notes/CERTIFICATE_IMPORT.md](notes/CERTIFICATE_IMPORT.md):
   recursive checker, import contract and evidence reconstruction.
5. [notes/FORMALIZATION_MAP.md](notes/FORMALIZATION_MAP.md) and
   [notes/MARABOU_SOURCE_MAP.md](notes/MARABOU_SOURCE_MAP.md):
   code correspondence and unresolved semantic questions.
6. [notes/RELU_AUXILIARY_SEQUENCE.md](notes/RELU_AUXILIARY_SEQUENCE.md) and
   [notes/SOURCE_QUERY_CAPTURE.md](notes/SOURCE_QUERY_CAPTURE.md):
   checked introductions and the source-to-processed connection.
7. [Isabelle/tests/fixtures/marabou/README.md](Isabelle/tests/fixtures/marabou/README.md):
   fixture provenance and native scenario distinctions.

## 5. What is already complete

The last fully validated baseline has:

| Item | Result |
| --- | --- |
| Isabelle installation | Isabelle2025-2 |
| Session | `Marabou_Verification = HOL +` |
| Project theories | 54 |
| Generated import theories | 22 |
| Python importer tests | 197 passed |
| Exported SML leaf checks | 8 passed |
| Exported SML proof-tree checks | 47 passed |
| Canonical accepted native-writer fixtures | 17: nine component fixtures and eight solver scenarios |
| Final `isabelle build -D Isabelle` | Exit 0; up to date; `0:00:02 elapsed time` |
| Build log Error/Warning filter | Exit 0; no output |

These results were recorded on 2026-09-22. Preparing this handoff inspected the
files; it did not rerun the implementation test suite. Re-establish the baseline
when starting implementation and record any environmental differences.

Completed capabilities:

* Variables are natural numbers; valuations are total functions into real
  numbers. Finite affine expressions, linear equalities/inequalities, variable
  bounds, ReLUs and query semantics are defined.
* ReLU phase decomposition and binary splitting are proved. Both children are
  checked; the active/inactive cases overlap harmlessly at input zero.
* An exact rational linear-leaf checker is proved sound over real semantics.
  Exact linear-implication and bound checkers justify explained premises.
* A recursive certificate checker composes linear leaves, splits, checked
  linear bounds and three ReLU propagation rules.
* Fresh scalar-fixed tableau auxiliaries and fresh ReLU auxiliaries have
  model-extension/projection theorems and executable guarded introductions.
  Finite sequences compose, with exact final-query matching.
* Strict untrusted adapters emit explicit HOL queries, certificates and
  proof obligations. Supported native proofs replay to processed-query and,
  through checked introductions, starting-query UNSAT theorems.
* Actual solver-produced propagation, a binary split with both children,
  one and two native ReLU introductions, and the latest chained proof have
  all been captured and replayed.

The current certificate constructors are:

```isabelle
Linear_Unsat
Relu_Split
Relu_Upper
Relu_Aux_Upper
Relu_Output_Aux_Upper
Linear_Bound
```

The central theorem in `Isabelle/Rational_Proof_Trees.thy` is:

```isabelle
check_certificate Q cert ⟹ unsatisfiable (embed_query Q)
```

Successful checked introduction sequences lift this to their explicit
starting queries. These are not theorems about an arbitrary C++ return code.
The project has mathematical SAT examples but **no general imported SAT
assignment checker yet**.

## 6. Implementation entry points

| Files | Purpose |
| --- | --- |
| `Isabelle/ROOT` | Session membership, HOL options and code exports. |
| `Marabou_Syntax.thy`, `Marabou_Semantics.thy`, `Query_Semantics.thy` | Existing real semantic core; preserve its meaning. |
| `Rational_Linear_Constraints.thy` | Rational data and embedding into real semantics. |
| `Rational_Linear_Certificates.thy`, `Rational_Linear_Implication.thy` | Exact leaves, implication witnesses and bound checks. |
| `ReLU_Bound_Propagation.thy` | Input upper → output upper. |
| `ReLU_Aux_Bound_Propagation.thy` | Input lower → auxiliary upper. |
| `ReLU_Output_Bound_Propagation.thy` | Strictly positive output lower → auxiliary upper zero. |
| `Rational_Proof_Trees.thy` | Datatype, recursive checking, soundness induction, SML exports. |
| `ReLU_Auxiliary_Sequence.thy`, `Tableau_Auxiliary_Sequence.thy` | Finite checked introduction composition. |
| `Isabelle/tools/import_marabou_json.py` | Strict native proof/query import and exact candidate reconstruction. |
| `Isabelle/tools/import_marabou_source.py` | Source query + scalar-fixed steps + processed query + proof. |
| `Isabelle/tools/import_marabou_relu_intro.py` | One captured native ReLU introduction plus that pipeline. |
| `Isabelle/tools/import_marabou_relu_sequence.py` | Finite native ReLU introductions plus that pipeline. |
| `Isabelle/tools/solver_capture/capture.cpp` | External native-engine harness and query scenarios. |
| `Isabelle/tools/capture_marabou_solver.py` | Build/run, independent snapshots, provenance and replay generation. |
| `Isabelle/tests/test_marabou_output_bound.py` | Latest native replay, exact guards, provenance and malformed-evidence tests. |
| `Isabelle/ReLU_Output_Bound_Examples.thy` | Latest HOL acceptance, rejection and real countermodels. |
| `Isabelle/tests/proof_tree_smoke.ML` | Standalone checks of exported SML. |

Unprefixed theory filenames in this table are under `Isabelle/`.
Generate imported theories with the adapters; do not hand-edit generated
weights merely to obtain a successful build.

## 7. Important current evidence and traps

Eight accepted solver scenarios are:

```text
linear
relu
relu_aux
relu_aux_active
relu_split
relu_intro
relu_sequence
relu_chain
```

Their artifacts live under `Isabelle/tests/fixtures/marabou/solver_<scenario>*`.
The first five have source/step/processed-query/proof inputs. The native ReLU
introduction scenarios additionally have a before-ReLU query and one
introduction record or a sequence, making six replay inputs.

The directory
`Isabelle/tests/fixtures/marabou/rejected_relu_chain/`
is **historically named**. Its proof is now accepted in full. Keep its seven
original JSON files unchanged. Their historical prefix is
`solver_relu_sequence`, but their query is the chained variant, not the
separate canonical sum scenario called `relu_sequence`.

The fresh `solver_relu_chain` capture reproduces all six historical data
artifacts byte-for-byte. The old exploratory execution lacks full build/run
provenance; the fresh run has it. Do not retroactively assign the fresh
provenance to the old execution.

The latest chained starting query is:

```text
b = z, c = f - 1/4, g = w
f = ReLU(b), g = ReLU(c)
b,c ∈ [-2,2]; f,g ∈ [0,2]; z ∈ [-2,-1/2]; w ∈ [1/4,2].
```

Two native ReLU introductions and five tableau introductions take it from
6 to 8 to 13 variables. All four native propagation lemmas are replayed.
The last is the newly verified positive-output rule. A shorter refutation
can omit it, so do not claim it is essential to this particular query.
Separate small examples exercise the new rule directly, including the
invalid zero-boundary case.

Further constraints to preserve:

* Output-lower and input-lower auxiliary rules are different. Strict
  positivity is essential for the output rule.
* An auxiliary metadata tuple is not proof of its defining equation.
  Both equation directions require checked linear witnesses.
* Reconstruct explanations using the actual causing variable.
* A locally checked linear premise does not automatically update the
  native ground-bound state. Validated PLC conclusions do. Sibling branches
  must not share new bounds.
* Finite serialized decimals denote exact decimal rationals. This is not
  a proof that serialization preserved a binary double's value.
* Weaker native conclusions such as `0.250001` and `1.750001` are retained
  and checked exactly; do not silently strengthen or round them.
* Native capture success creates candidate evidence. The emitted Isabelle
  session must also build before claiming a theorem.
* Current adapters impose a restricted finite/homogeneous tableau language,
  finite bounds and limited ReLU metadata. The HOL semantics is more general.
  Resource and reconstruction limits are documented in CERTIFICATE_IMPORT.
* Unsupported-rule rejection is a coverage limit, not evidence of a solver
  defect. A suspected defect needs a separate reproducible analysis.

## 8. Immediate next milestone: positive auxiliary lower bound

This is the first task to implement. The previous positive-output milestone
is already complete.

Prove and check the dual rule:

```text
y = ReLU(x),  y - x - a = 0,  0 < l ≤ a
    ⇒ y = 0
    ⇒ y ≤ u for any checked u ≥ 0.
```

Inspect the current pinned source again:

* `upstream/Marabou/src/engine/ReluConstraint.cpp::notifyLowerBound`:
  the `variable == _aux && FloatUtils::isPositive(bound)` branch, around
  lines 209–226, emits an output upper bound zero in proof mode.
* `upstream/Marabou/src/proofs/Checker.cpp::checkReluLemma`:
  `causingVar == aux`, lower bound, `affectedVar == f`, upper bound.
  Its epsilon comparison is not the exact mathematical guard.
* `src/proofs/UnsatCertificateUtils.cpp`:
  class `UNSATCertificateUtils` supplies explanation reconstruction.
* `src/proofs/JsonWriter.cpp::writePLCLemmas` and
  `src/engine/BoundManager.cpp::addLemmaExplanationAndTightenBound`.

Suggested implementation order:

1. Prove the real lemma and a zero-boundary counterexample. For example,
   `x=y=1,a=0` satisfies ReLU and the equation but has positive output;
   `a≥0` alone is insufficient.
2. Add a small exact rational guard using existing implication witnesses,
   prove bound soundness and preservation of real models, and build.
3. Add a distinct recursive constructor and extend the central soundness
   induction and SML export; build again.
4. Extend the strict adapter to recognize this exact cause/affected pattern,
   reconstruct the auxiliary lower premise, and validate both directions
   of the equation. Preserve ambiguity rejection and ground-state behavior.
5. Add meaningful acceptance, zero/negative, tiny-positive, wrong-variable,
   wrong-direction, missing-equation, bad-child and real-model tests.
6. Find one tiny **actual native proof-enabled run** that emits the rule.
   Change the local harness, not upstream. Capture the whole proof and
   independent query/transformation artifacts, then replay in Isabelle.
7. If additional unsupported evidence appears, preserve it and document the
   exact coverage gap. Do not filter it out and claim complete replay.
8. Update source/formalization maps, fixture provenance, README, test counts
   and BUILD_RESULT with the precise new assurance and next bounded target.

Completion requires both the generic soundness theorem and an unmodified
native proof containing the supported rule replayed to a starting-query
theorem through the existing checked pipeline. If native evidence is not
yet obtained, report a partial milestone accurately and keep that subtask open.
No such new capture is claimed to exist at this handoff.

## 9. Roadmap after that milestone

These are future tasks, not claims of completed results. Choose one bounded
step at a time, guided by actual evidence.

### A. Expand useful ReLU proof coverage

Inventory remaining native ReLU lemma patterns from source. For each needed
pattern, give an exact mathematical rule, a checked premise, a soundness proof,
negative/boundary examples and native replay. Add combined cases with nested
splits and ordered propagation only when they exercise a real gap.

Prefer witnesses demonstrating why a new rule or child matters. A redundant
native lemma is still worth checking, but document redundancy honestly.
Do not invent an elaborate universal certificate schema before seeing evidence.

### B. Close the source/query interpretation gap for a narrow input language

The current theorem is about explicit HOL query data produced by untrusted
decoding. Define exactly what a future external input claim means: exact
decimal rationals, exact finite binary-double values, or another documented
representation. Do not silently change the existing exact-decimal contract.

Start with a small exact linear/ReLU query representation, not an ONNX parser.
Specify the relation from bytes or structured source data to the HOL query.
Then choose a small verified decoder or proof-producing translation workflow
with an explicit trust boundary. Test malformed data and theorem-statement
substitution. If faithfully relating native serialized data requires exact
double encodings or additional evidence, document that before implementation.

### C. Add only necessary checked preprocessing transformations

Fresh ReLU and scalar-fixed auxiliary sequences are already verified.
Inspect the next actual preprocessing operation needed by a target capture;
prove model extension/projection or an appropriate satisfiability relation,
then add exact checking and native evidence. General preprocessing as a
single trusted transformation is not an acceptable shortcut.

### D. Exact SAT witnesses

Add a separate finite exact assignment checker and prove that acceptance
constructs a real model of the explicit query. Check every linear atom, bound
and ReLU. An approximate floating-point assignment is not an exact witness.

Investigate exact reconstruction from a native SAT run for a tiny rational
linear/ReLU query. Distinguish success of reconstruction from correctness of
the checking theorem. Where introductions are present, use the existing
projection results to connect to the starting query. Do not assume every
reported floating-point assignment can be repaired.

### E. Package a reproducible restricted-fragment release

Make one documented invocation carry a supported explicit input and evidence
through checked introductions to an Isabelle theorem, with clear rejection
reasons for unsupported evidence. Preserve strict query identity and
deterministic theorem regeneration. Include native UNSAT and, once implemented,
SAT examples, adversarial mutations, source pins, provenance and exact build
instructions.

Document whether the theorem concerns HOL data, decoded bytes or original
network input. A usable first release may explicitly retain an unverified
extraction/decoder boundary; it must not advertise that boundary as closed.
Full C++ verification, search completeness, Farkas completeness and neural
network file semantics are separate research milestones.

## 10. Commands and environment

Run from the project root. Quote its path because it contains a space:

```sh
cd "/home/dusty/Desktop/Marabou Verification"
isabelle version
isabelle build -D Isabelle
python3 -m unittest discover -s Isabelle/tests -p 'test_*.py'
```

The known Isabelle executable is:

```text
/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle
```

When executable definitions or exports change, regenerate and exercise SML:

```sh
isabelle build -e -D Isabelle
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --script Isabelle/tests/linear_leaf_smoke.ML
/home/dusty/Desktop/Isabelle/Isabelle2025-2/contrib/polyml-5.9.2-2/x86_64-linux/poly \
  --script Isabelle/tests/proof_tree_smoke.ML
isabelle build_log -H 'Error|Warning' Marabou_Verification
git diff --check
```

`poly` is not necessarily on PATH. The absolute executable above worked.
The capture driver requires a new or empty output directory. Choose a fresh
path rather than deleting an earlier run:

```sh
python3 Isabelle/tools/capture_marabou_solver.py \
  --scenario relu_chain --output /tmp/claude-marabou-chain-001
isabelle build -d Isabelle -D /tmp/claude-marabou-chain-001
```

Standalone replay sessions use the name `Marabou_Import_Replay`. Build them
one at a time. Do not race builds or captures sharing the same heap/build tree.
The native driver defaults to four build jobs and permits `--jobs`.

The native build lives in `Isabelle/generated/solver_capture_build`.
`Isabelle/tools/solver_capture/CMakeLists.txt` builds selected actual engine
sources using C++17, CMake, GMP, Boost and bundled CVC4 context code. It
excludes CLI/network parsers. See SOLVER_CAPTURE for the dependency setup.
HOL replay and Python tests do not require rebuilding the C++ engine.

`Isabelle/generated/` is ignored, as are Python caches. Durable fixtures and
generated project theories must live outside that ignored directory.
The Isabelle installation writes its user heaps outside the project; use
the host's permission mechanism if required instead of changing global
installation settings to work around an access failure.

## 11. Provenance and regression workflow

Tests check saved artifact hashes and current capture/importer sources.
If a shared harness or hashed importer changes, inspect which provenance
records are affected. Re-run the corresponding captures to refresh provenance
from real executions. Do not simply rewrite hashes and claim old binary runs
used the new source.

All seven older scenarios were actually rerun for the latest milestone.
Their data stayed byte-identical; reports, logs and provenance were refreshed.
Follow that pattern when appropriate, while preserving historical raw evidence.

Changing generated theory output requires regeneration and a successful
Isabelle build. Compare complete queries and step results, not only selected
fields or the final UNSAT flag. Keep component fixtures explicitly distinct
from real solver-produced evidence.

For final validation, run tests appropriate to the changed layer, the complete
session build and importer regression suite. Repeat SML checks after export
changes. Investigate genuine warnings. Record exact exit status and output;
never infer that a still-running build passed.

## 12. Persistent loop protocol

Use `notes/CONTINUATION_LOG.md` as the persistent working record. Create it
when implementation resumes; this handoff does not claim it already exists.
Each invocation should:

1. Read the current log, latest completed BUILD_RESULT section and Git status.
   Determine the outstanding objective before choosing new work.
2. Select one concrete task with a completion condition: a real lemma, a
   checked guard, a soundness induction case, an importer pattern, a native
   capture or a full replay. Work on that task rather than restarting the audit.
3. Complete useful implementation and verification. Build at meaningful
   checkpoints and fix failures before declaring a milestone complete.
4. Update the log with completed work, edited files, exact test/build result,
   preserved evidence, remaining uncertainty and the next precise action.
5. On failure, retain diagnostics and distinguish a proof gap, import gap,
   unsupported native rule, environmental issue and genuine missing user
   decision. Do not retry the same failed command indefinitely.
6. Before ending an invocation, leave a compiling checkpoint if possible.
   If it is not possible, explicitly mark the development incomplete and
   record the exact failing command and state; never report a green checkpoint.

Suggested record:

```text
Date / milestone:
Current objective and completion condition:
Completed this invocation:
Files changed:
Last successful Isabelle build:
Other checks and exact results:
Native artifacts / provenance:
Open issue or blocker:
Next concrete action:
Assurance gained / boundaries remaining:
```

Routine reversible work should continue without repeated confirmation.
Do not turn the loop into unbounded speculative scope expansion. When the
agreed restricted-fragment release is complete, or an essential external
decision is needed, report that state plainly.

## 13. Existing sigmoid definition: retain this knowledge

The user specifically noted that UAT already defines a polymorphic sigmoid.
See [notes/ACTIVATION_REUSE.md](notes/ACTIVATION_REUSE.md).

```text
/home/dusty/Desktop/Academic/Isabelle_Stuff/Sigmoid_Universal_Approximation/
    Sigmoid_Definition.thy
```

The existing constant is:

```isabelle
Sigmoid_Definition.sigmoid :: "'a::{real_normed_field,banach} ⇒ 'a"
sigmoid x = exp x / (1 + exp x)
```

Reuse its real instance if sigmoid support is eventually authorized.
Do not introduce a duplicate definition or a UAT dependency for the present
linear/ReLU milestone. That external definition was modified in its working
tree when inspected; the note records its hash. Do not overwrite or assume a
clean UAT checkout. Its real range/order facts must not be generalized to its
complex instance without proof.

## 14. Suggested instruction to start continuation

Paste this as a normal task instruction or use it as the body of your chosen
loop workflow; no particular Claude slash-command syntax is assumed here:

> Read CLAUDE_HANDOFF.md in /home/dusty/Desktop/Marabou Verification and continue
> the existing Isabelle/HOL certificate-checking project. Preserve all current
> work. First complete the verified positive-auxiliary-lower-bound rule and
> capture/import a real native proof using it. Keep the session compiling,
> finish every claimed proof, and record progress in notes/CONTINUATION_LOG.md.
> Then progress through the bounded remaining roadmap, one tested milestone
> at a time. Do the implementation and validation, not just planning. Be precise
> about the theorem established and the extraction/decoder boundary.
