#!/usr/bin/env python3
"""Connect an exact query file (.mqx) to a native capture of that file.

The native harness reads the file with its own untrusted C++ reader. This
adapter reuses the strict source, ReLU-sequence and assignment importers for
the captured artifacts, checks early that the file's decoding has exactly the
constraints of the captured starting query, and renders a theory whose
theorems concern decode_query of the file's bytes. Isabelle decides every
step; nothing here is a premise.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import math
from pathlib import Path
import re
import sys

import exact_query_text as text
import import_marabou_assignment as assignment
import import_marabou_json as proof
import import_marabou_preprocessing as preprocessing
import import_marabou_relu_sequence as sequence
import import_marabou_source as source
import prepare_inequalities as inequalities

MAX_FILE_BYTES = 1_000_000


def exact_double(q: Fraction) -> bool:
    try:
        x = float(q)
    except OverflowError:
        return False
    return math.isfinite(x) and Fraction(x) == q


def check_pipeline_support(data: bytes, *, equality_only=False, native_preprocessing=False):
    """Mirror the capture pipeline's restrictions for readable early rejection.
    With native preprocessing, bounds may be missing (the preprocessor must
    derive finite ones) and le/ge statements go to the native conversion."""
    proof.require(len(data) <= MAX_FILE_BYTES, "query file too large")
    decoded = text.decode(data)
    proof.require(decoded is not None,
                  "not a marabou-exact-query-v1 file (see notes/EXACT_QUERY_FORMAT.md)")
    proof.require(not equality_only or all(kind == "EQ" for kind, _, _ in decoded.linear),
                  "inequalities remain in the native input")
    proof.require(decoded.linear, "at least one linear constraint is needed")
    proof.require(len(decoded.linear) <= 512, "too many linear constraints")
    for _, terms, _ in decoded.linear:
        proof.require(len({x for _, x in terms}) == len(terms), "repeated variable in an equation")
    variables = {x for _, terms, _ in decoded.linear for _, x in terms}
    variables |= {b.variable for b in decoded.bounds} | {v for r in decoded.relus for v in r}
    n = max(variables, default=-1) + 1
    proof.require(n > 0, "at least one variable is needed")
    proof.require(n <= 4096, "variable index too large")
    for kind in ("L", "U"):
        indices = [b.variable for b in decoded.bounds if b.kind == kind]
        proof.require(len(indices) == len(set(indices)),
                      "each variable needs exactly one lower and one upper bound")
        missing = sorted(set(range(n)) - set(indices))
        proof.require(native_preprocessing or not missing,
                      f"variable x{missing[0] if missing else 0} needs finite lower and upper bounds")
    proof.require(all(x != y for x, y in decoded.relus), "a ReLU needs distinct input and output")
    numbers = [q for _, terms, rhs in decoded.linear for q in [rhs, *(a for a, _ in terms)]]
    numbers += [b.value for b in decoded.bounds]
    bad = [q for q in numbers if not exact_double(q)]
    proof.require(not bad, f"number {bad[0] if bad else 0} is not exactly a binary double")
    return decoded


@dataclass(frozen=True)
class FileReplay:
    data: bytes
    kind: str                 # "unsat" or "sat"
    relus: bool               # starting query has ReLUs (native introductions)
    replay: object            # sequence.Replay, source.Replay, assignment.SatReplay or
                              # preprocessing.Preprocessed
    hashes: dict
    inequality_steps: tuple = ()
    preprocessed: bool = False


def reconstruct(data, loaded):
    """loaded: dict of (object, digest) for source, steps, query and either
    certificate or assignment, plus before/introductions when ReLUs exist."""
    if "preprocessing" in loaded:
        return reconstruct_preprocessed(data, loaded)
    decoded = check_pipeline_support(data)
    has_inequalities = any(kind != "EQ" for kind, _, _ in decoded.linear)
    proof.require(has_inequalities == ("inequalities" in loaded) == ("prepared" in loaded),
                  "inequality files need both preparation evidence and the prepared file, and only they do")
    required = {"source", "steps", "query"}
    allowed = required | {"certificate", "assignment", "before", "introductions",
                          "inequalities", "prepared", "phase_fixing"}
    proof.require(required <= loaded.keys() and loaded.keys() <= allowed, "unexpected or missing artifacts")
    inequality_steps = ()
    if has_inequalities:
        inequality_steps = inequalities.parse_record(loaded["inequalities"][0])
        decoded = inequalities.replay(decoded, inequality_steps)
        prepared = check_pipeline_support(loaded["prepared"][0], equality_only=True)
        proof.require(prepared == decoded, "prepared file differs from the checked inequality steps")
    relus = bool(decoded.relus)
    proof.require(relus == ("before" in loaded) == ("introductions" in loaded),
                  "ReLU files need the before-ReLU query and introduction records, and only they do")
    proof.require(("certificate" in loaded) != ("assignment" in loaded),
                  "supply exactly one of a certificate (UNSAT) or an assignment (SAT)")
    proof.require(relus or "phase_fixing" not in loaded, "a phase-fixing record needs ReLUs")
    obj = {k: v[0] for k, v in loaded.items()}
    if "assignment" in loaded:
        # An exact model needs no phase justification; the record is still
        # parsed so that a malformed one is rejected.
        if "phase_fixing" in loaded:
            proof.parse_phase_fixing(obj["phase_fixing"], proof.parse_instance(obj["query"]))
        replay = assignment.reconstruct(obj["source"], obj["steps"], obj["query"], obj["assignment"],
                                        obj.get("before"), obj.get("introductions"))
        start = replay.before if relus else replay.source
        kind = "sat"
    elif relus:
        replay = sequence.reconstruct(obj["before"], obj["introductions"], obj["source"], obj["steps"],
                                      obj["query"], obj["certificate"], obj.get("phase_fixing"))
        start, kind = replay.before, "unsat"
    else:
        replay = source.reconstruct(obj["source"], obj["steps"], obj["query"], obj["certificate"])
        start, kind = replay.source, "unsat"
    proof.require(text.same_constraints(decoded, start),
                  "the query captured from the solver differs from the query the file denotes")
    return FileReplay(data, kind, relus, replay, {k: v[1] for k, v in loaded.items()}, inequality_steps)


PREPROCESSED_ARTIFACTS = {
    "unsat": {"preprocessing", "source", "steps", "query", "certificate"},
    "infeasible": {"preprocessing"},
    "sat": {"preprocessing", "source", "steps", "query", "assignment"},
}


def reconstruct_preprocessed(data, loaded):
    """A run with Marabou's own preprocessing (capture mode file-preprocess)."""
    decoded = check_pipeline_support(data, native_preprocessing=True)
    kind = ("sat" if "assignment" in loaded else "unsat" if "certificate" in loaded else "infeasible")
    expected = PREPROCESSED_ARTIFACTS[kind]
    allowed = expected | ({"phase_fixing"} if kind != "infeasible" else set())
    proof.require(expected <= loaded.keys() <= allowed,
                  "unexpected or missing artifacts for a preprocessed run")
    result = preprocessing.reconstruct(decoded, loaded)
    proof.require(result.kind == kind, "inconsistent preprocessed run")
    return FileReplay(data, "sat" if kind == "sat" else "unsat", bool(decoded.relus), result,
                      {k: v[1] for k, v in loaded.items()}, preprocessed=True)


def render_replay_theory(name, file_replay):
    h = file_replay.hashes
    if file_replay.preprocessed:
        return preprocessing.render_theory(name, file_replay.replay, h)
    if file_replay.kind == "sat":
        return assignment.render_theory(name, file_replay.replay, h)
    if file_replay.relus:
        return sequence.render_theory(name, file_replay.replay, h["before"], h["introductions"],
                                      h["source"], h["steps"], h["query"], h["certificate"])
    return source.render_theory(name, file_replay.replay, h["source"], h["steps"], h["query"],
                                h["certificate"])


THEOREM_TEMPLATE = """theory {name}
  imports "Marabou_Verification.Exact_Query_Format" {replay}
begin

text \\<open>
  Generated by the untrusted query-file adapter. The theorems below concern
  decode_query of the exact bytes of {reference}
  ({size} bytes, SHA-256 {digest}), which the build checks against the file.
  The native solver read this file with an untrusted C++ reader. Isabelle
  proves that the file's decoding has exactly the constraints of the query
  captured from that run, so neither the reader, the solver nor the JSON
  import is trusted for these conclusions.
\\<close>

definition query_file :: bytes where
  "query_file = {data}"

external_file "{reference}"

ML \\<open>
  Exact_Query_Text.check_file \\<^theory> @{{thm query_file_def}} "{reference}"
\\<close>

lemma query_file_decodes_like_capture:
  "decodes_like query_file {replay}.{query}"
  by code_simp

theorem query_file_decodes:
  "\\<exists>Q. decode_query query_file = Some Q"
  by (rule decodes_like_decodes[OF query_file_decodes_like_capture])

{conclusion}
end
"""

UNSAT_CONCLUSION = """theorem query_file_unsatisfiable:
  "decode_query query_file = Some Q \\<Longrightarrow> unsatisfiable (embed_query Q)"
  by (rule decodes_like_unsatisfiable[OF query_file_decodes_like_capture
        {replay}.{query}_unsatisfiable])
"""

SAT_CONCLUSION = """theorem query_file_model:
  "decode_query query_file = Some Q \\<Longrightarrow>
    satisfies_query (assignment_valuation {replay}.imported_assignment) (embed_query Q)"
  by (rule decodes_like_model[OF query_file_decodes_like_capture {replay}.{query}_model])

theorem query_file_satisfiable:
  "decode_query query_file = Some Q \\<Longrightarrow> satisfiable (embed_query Q)"
  using query_file_model unfolding satisfiable_def by blast
"""


def render_theorem_theory(name, replay_name, file_replay, reference):
    for theory in (name, replay_name):
        proof.require(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", theory) is not None, "invalid theory name")
    proof.require(re.fullmatch(r"[A-Za-z0-9_./-]+\.mqx", reference) is not None and ".." not in reference,
                  "invalid file reference")
    query = "imported_before_relu_query" if file_replay.relus else "imported_source_query"
    template = SAT_CONCLUSION if file_replay.kind == "sat" else UNSAT_CONCLUSION
    data = file_replay.data
    theorem_template = THEOREM_TEMPLATE
    if file_replay.preprocessed:
        query = "imported_file_query"
        theorem_template = theorem_template.replace(
            "  The native solver read this file with an untrusted C++ reader. Isabelle\n"
            "  proves that the file's decoding has exactly the constraints of the query\n"
            "  captured from that run, so neither the reader, the solver nor the JSON\n"
            "  import is trusted for these conclusions.",
            "  The native solver read this file and ran Marabou's own preprocessing.\n"
            "  The replay theory checks the native slack and ReLU introductions, exact\n"
            "  re-derivations of the tightened bounds, and a projection onto the captured\n"
            "  preprocessed query (or onto derived crossing bounds). Neither the reader,\n"
            "  the solver, the preprocessing record nor the JSON import is trusted.")
    if file_replay.inequality_steps:
        theorem_template = theorem_template.replace(
            "Marabou_Verification.Exact_Query_Format", "Marabou_Verification.Bounded_Inequality_Auxiliary")
        theorem_template = theorem_template.replace(
            "  The native solver read this file with an untrusted C++ reader. Isabelle\n"
            "  proves that the file's decoding has exactly the constraints of the query\n"
            "  captured from that run, so neither the reader, the solver nor the JSON\n"
            "  import is trusted for these conclusions.",
            "  The native solver read a locally prepared equality file. Isabelle checks\n"
            "  fresh signed slacks and exact witnesses for their finite opposite bounds,\n"
            "  then matches the result to the independently captured native query.\n"
            "  These theorems concern the original bytes above; the Python preparation,\n"
            "  C++ reader, solver and JSON import are untrusted.")
        theorem_template = theorem_template.replace(
            "lemma query_file_decodes_like_capture:",
            'definition inequality_steps :: "bounded_inequality_step list" where\n'
            '  "inequality_steps = ' + inequalities.hol_steps(file_replay.inequality_steps) + '"\n\n'
            "lemma query_file_decodes_like_capture:")
        theorem_template = theorem_template.replace(
            "decodes_like query_file {replay}.{query}",
            "bounded_decodes_like query_file inequality_steps {replay}.{query}")
        theorem_template = theorem_template.replace(
            "rule decodes_like_decodes", "rule bounded_decodes_like_decodes")
        template = template.replace("rule decodes_like_", "rule bounded_decodes_like_")
    return theorem_template.format(
        name=name, replay=replay_name, reference=reference, size=len(data),
        digest=hashlib.sha256(data).hexdigest(), data=text.hol_bytes(data), query=query,
        conclusion=template.format(replay=replay_name, query=query))


ARTIFACTS = (("source", "_source.json"), ("steps", "_steps.json"), ("query", "_query.json"),
             ("certificate", ".json"), ("assignment", "_assignment.json"),
             ("before", "_before_relu.json"), ("introductions", "_relu_steps.json"),
             ("inequalities", "_inequality_steps.json"), ("phase_fixing", "_phase_fixing.json"),
             ("preprocessing", "_preprocessing.json"))


def load_artifacts(prefix: Path):
    """Artifacts written by the harness for one run, keyed as reconstruct expects."""
    loaded = {}
    for key, suffix in ARTIFACTS:
        path = prefix.parent / (prefix.name + suffix)
        if path.exists():
            loaded[key] = proof.load_json(path)
    prepared = prefix.parent / (prefix.name + "_prepared.mqx")
    if prepared.exists():
        data = prepared.read_bytes()
        loaded["prepared"] = (data, hashlib.sha256(data).hexdigest())
    return loaded


def write_session(directory: Path, data: bytes, loaded, replay_name="Captured_Query_File",
                  theorem_name="Query_File_Theorem"):
    """Write query.mqx, both theories and a ROOT into an output directory."""
    file_replay = reconstruct(data, loaded)
    root = directory / "ROOT"
    proof.require(not root.exists(), "refusing to replace an existing ROOT")
    (directory / "query.mqx").write_bytes(data)
    (directory / (replay_name + ".thy")).write_text(
        render_replay_theory(replay_name, file_replay), encoding="utf-8")
    (directory / (theorem_name + ".thy")).write_text(
        render_theorem_theory(theorem_name, replay_name, file_replay, "query.mqx"), encoding="utf-8")
    root.write_text("session Marabou_Import_Replay = Marabou_Verification +\n"
                    "  options [document = false, quick_and_dirty = false]\n"
                    f"  theories {replay_name} {theorem_name}\n", encoding="utf-8")
    return file_replay


# Example files in Isabelle/examples whose native file runs reproduced the
# artifacts of these saved scenarios byte-for-byte (checked by the tests via
# the saved file-run provenance). (example, scenario, replay theory)
EXAMPLES = (
    ("relu_chain_unsat", "relu_chain", "Imported_Marabou_Native_Relu_Chain"),
    ("relu_sat", "relu_sat", "Imported_Marabou_Native_Relu_Sat"),
    ("linear_unsat", "linear", "Imported_Marabou_Source_Linear"),
)

# Example files whose complete native artifact set is saved as
# tests/fixtures/marabou/file_<example>_*. (example, replay theory)
FULL_ARTIFACT_EXAMPLES = (
    ("inequality_relu_unsat", "Imported_Marabou_Prepared_Inequality_Relu_Unsat"),
    ("inequality_relu_sat", "Imported_Marabou_Prepared_Inequality_Relu_Sat"),
    ("inequality_linear_sat", "Imported_Marabou_Prepared_Inequality_Linear_Sat"),
    ("phase_active_unsat", "Imported_Marabou_File_Phase_Active_Unsat"),
    ("phase_inactive_unsat", "Imported_Marabou_File_Phase_Inactive_Unsat"),
    ("phase_chain_unsat", "Imported_Marabou_File_Phase_Chain_Unsat"),
    ("phase_fixed_sat", "Imported_Marabou_File_Phase_Fixed_Sat"),
)

# Example files run with Marabou's own preprocessing (capture --preprocess);
# their complete artifact sets are saved as file_<example>_*.
PREPROCESSED_EXAMPLES = (
    ("preprocess_split_unsat", "Imported_Marabou_Preprocessed_Split_Unsat"),
    ("preprocess_eliminate_unsat", "Imported_Marabou_Preprocessed_Eliminate_Unsat"),
    ("preprocess_inequality_unsat", "Imported_Marabou_Preprocessed_Inequality_Unsat"),
    ("preprocess_mixed_sat", "Imported_Marabou_Preprocessed_Mixed_Sat"),
)


def example_theory_name(example):
    return "Imported_Marabou_Example_" + example.title()


def example_theories(isabelle: Path):
    """Main-session theorem theories for the example files, keyed by file name."""
    result = {}
    fixtures = isabelle / "tests/fixtures/marabou"
    for example, scenario, replay in EXAMPLES:
        data = (isabelle / "examples" / (example + ".mqx")).read_bytes()
        file_replay = reconstruct(data, load_artifacts(fixtures / ("solver_" + scenario)))
        name = example_theory_name(example)
        result[name + ".thy"] = render_theorem_theory(name, replay, file_replay,
                                                      f"examples/{example}.mqx")
    return result


def full_artifact_example_theories(isabelle: Path):
    """Both native replay and original-byte theorem for each saved file run."""
    result = {}
    fixtures = isabelle / "tests/fixtures/marabou"
    for example, replay in FULL_ARTIFACT_EXAMPLES + PREPROCESSED_EXAMPLES:
        data = (isabelle / "examples" / (example + ".mqx")).read_bytes()
        file_replay = reconstruct(data, load_artifacts(fixtures / ("file_" + example)))
        name = example_theory_name(example)
        result[replay + ".thy"] = render_replay_theory(replay, file_replay)
        result[name + ".thy"] = render_theorem_theory(name, replay, file_replay,
                                                    f"examples/{example}.mqx")
    return result


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query-file", type=Path, help="the .mqx file that was solved")
    parser.add_argument("--artifacts", type=Path,
                        help="artifact prefix written by the harness, e.g. DIR/solver_file")
    parser.add_argument("--output", type=Path, help="new or empty output directory")
    parser.add_argument("--examples", type=Path,
                        help="regenerate the example theorem theories in this Isabelle directory")
    args = parser.parse_args(argv)
    try:
        if args.examples is not None:
            proof.require(args.query_file is None and args.artifacts is None and args.output is None,
                          "--examples cannot be combined with other options")
            for name, theory in (example_theories(args.examples) |
                                 full_artifact_example_theories(args.examples)).items():
                (args.examples / name).write_text(theory, encoding="utf-8")
            print("Wrote the example theorem theories.")
            return 0
        proof.require(None not in (args.query_file, args.artifacts, args.output),
                      "give --query-file, --artifacts and --output, or --examples")
        output = args.output
        proof.require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
                      "output directory must be new or empty")
        data = args.query_file.read_bytes()
        loaded = load_artifacts(args.artifacts)
        output.mkdir(parents=True, exist_ok=True)
        write_session(output, data, loaded)
    except (proof.ImportFailure, OSError, RecursionError, ValueError) as exc:
        parser.exit(1, f"Query-file import rejected: {exc}\n")
    print(f"Wrote {output}; build it with: isabelle build -d Isabelle -D {output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
