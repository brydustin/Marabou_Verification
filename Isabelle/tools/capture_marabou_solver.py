#!/usr/bin/env python3
"""Build the unchanged native engine, capture a tiny run, and prepare HOL replay.

No automatic downloads, system installation, or upstream edits. Supply an empty
output directory. A successful capture is candidate evidence; build the emitted
Isabelle session to establish the captured source query's UNSAT theorem, or,
for the SAT scenario, the exact model theorems for its reconstructed assignment.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys

import import_marabou_assignment as assignment_adapter
import import_marabou_json as adapter
import import_marabou_query_file as query_file_adapter
import import_marabou_source as source_adapter
import import_marabou_relu_intro as intro_adapter
import import_marabou_relu_sequence as sequence_adapter


PINNED_REVISION = "1c2f4788c32e2f4e407c356b763a8025c5578722"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command_output(command, **kwargs):
    return subprocess.check_output(command, text=True, **kwargs).strip()


def build_record(build, binary, root, revision):
    """The actual build inputs and binary. Hashes are provenance, not HOL premises."""
    sources = json.loads((build / "compile_commands.json").read_text())
    source_hashes = {
        str(Path(entry["file"]).resolve().relative_to(root)): sha256(Path(entry["file"]))
        for entry in sources
    }
    compile_command = next(entry["command"] for entry in sources
                           if Path(entry["file"]).name == "capture.cpp")
    compiler = shlex.split(compile_command)[0]
    libraries = {}
    for line in (build / "CMakeCache.txt").read_text().splitlines():
        if line.startswith(("BOOST_", "GMP")) and "_LIBRARY:FILEPATH=" in line:
            key, path = line.split(":FILEPATH=", 1)
            libraries[key] = {"path": path, "sha256": sha256(Path(path))}
    return {
        "marabou_revision": revision,
        "capture_script_sha256": sha256(Path(__file__)),
        "importer_sha256": sha256(Path(adapter.__file__)),
        "source_importer_sha256": sha256(Path(source_adapter.__file__)),
        "cmake_sha256": sha256(Path(__file__).with_name("solver_capture") / "CMakeLists.txt"),
        "binary_sha256": sha256(binary),
        "compiled_sources": source_hashes,
        "capture_compile_command": compile_command,
        "compiler_version": command_output([compiler, "--version"]).splitlines()[0],
        "linked_libraries": libraries,
        "cmake_version": command_output(["cmake", "--version"]).splitlines()[0],
    }


def capture_query_file(output, stem, query_bytes, binary, build, root, revision):
    """Replay a native run on a user file; the theorem is about the file's bytes."""
    loaded = query_file_adapter.load_artifacts(output / stem)
    file_replay = query_file_adapter.write_session(output, query_bytes, loaded)
    report = json.loads((output / (stem + "_run.json")).read_text())
    provenance = build_record(build, binary, root, revision)
    provenance.update({f"{key}_sha256": digest for key, (_, digest) in loaded.items()})
    provenance.update({
        "scenario": "file",
        "query_file_sha256": hashlib.sha256(query_bytes).hexdigest(),
        "result": file_replay.kind,
        "exit_code": report["exit_code"],
        "run_report_sha256": sha256(output / (stem + "_run.json")),
        "solver_log_sha256": sha256(output / (stem + ".log")),
        "query_file_importer_sha256": sha256(Path(query_file_adapter.__file__)),
        "exact_text_sha256": sha256(Path(query_file_adapter.text.__file__)),
        "assignment_importer_sha256": sha256(Path(assignment_adapter.__file__)),
        "relu_sequence_importer_sha256": sha256(Path(sequence_adapter.__file__)),
        "inequality_preparer_sha256": sha256(Path(query_file_adapter.inequalities.__file__)),
        "preprocessing_importer_sha256": sha256(Path(query_file_adapter.preprocessing.__file__)),
        "native_preprocessing": "preprocessing" in loaded,
        "assurance": "Provenance only; the generated theorem concerns decode_query of the "
                     "exact bytes of query.mqx. Isabelle checks any local inequality preparation, "
                     "any native preprocessing (introductions, re-derived bounds and projection) "
                     "and any ReLU phase fixed before solving, and matches the resulting constraints "
                     "to the captured query. Python preparation, C++ reading and execution, "
                     "extraction, and JSON decoding are not verified.",
    })
    (output / (stem + "_provenance.json")).write_text(
        json.dumps(provenance, indent=2, sort_keys=True) + "\n")
    result = "UNSAT" if file_replay.kind == "unsat" else "SAT"
    print(f"Native result {report['exit_code']}; prepared Query_File_Theorem for a {result} theorem.")
    print(f"Build it with: isabelle build -d Isabelle -D {output}")
    return 0


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument("--scenario", choices=("linear", "relu", "relu_aux", "relu_aux_active",
                                             "relu_aux_inactive", "relu_split", "relu_intro",
                                             "relu_sequence", "relu_chain", "relu_sat"))
    mode.add_argument("--query-file", type=Path,
                      help="solve this marabou-exact-query-v1 file and prove a theorem about its bytes")
    parser.add_argument("--preprocess", action="store_true",
                        help="with --query-file: run Marabou's own preprocessing and check its result")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args(argv)
    if args.preprocess and args.query_file is None:
        parser.error("--preprocess requires --query-file")
    if args.scenario is None and args.query_file is None:
        args.scenario = "linear"
    root = Path(__file__).resolve().parents[2]
    upstream = root / "upstream/Marabou"
    build = root / "Isabelle/generated/solver_capture_build"
    output = args.output.resolve()
    stem = "solver_" + (args.scenario or "file")
    theory = "Captured_Solver_" + (args.scenario or "file").title()
    try:
        prepared_bytes, inequality_steps = None, ()
        adapter.require(1 <= args.jobs <= 32, "jobs must be between 1 and 32")
        adapter.require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
                        "capture output directory must be empty")
        if args.query_file is not None:
            # Reject unsupported files before building or running anything.
            query_bytes = args.query_file.read_bytes()
            decoded = query_file_adapter.check_pipeline_support(
                query_bytes, native_preprocessing=args.preprocess)
            if not args.preprocess and any(kind != "EQ" for kind, _, _ in decoded.linear):
                prepared, inequality_steps = query_file_adapter.inequalities.prepare(decoded)
                prepared_bytes = query_file_adapter.inequalities.encode(prepared)
                query_file_adapter.check_pipeline_support(prepared_bytes, equality_only=True)
        revision = command_output(["git", "-C", str(upstream), "rev-parse", "HEAD"])
        adapter.require(revision == PINNED_REVISION, "unexpected Marabou revision")
        adapter.require(not command_output(["git", "-C", str(upstream), "status",
                                            "--porcelain", "--untracked-files=all"]),
                        "Marabou checkout must be clean")
        output.mkdir(parents=True, exist_ok=True)
        if prepared_bytes is not None:
            (output / (stem + "_prepared.mqx")).write_bytes(prepared_bytes)
            (output / (stem + "_inequality_steps.json")).write_text(
                json.dumps(query_file_adapter.inequalities.record(inequality_steps),
                           indent=2, sort_keys=True) + "\n")
        with (output / "build.log").open("w") as log:
            for command in (
                ["cmake", "-S", str(Path(__file__).with_name("solver_capture")), "-B", str(build),
                 "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                 "-DMARABOU_SOURCE=" + str(upstream)],
                ["cmake", "--build", str(build), "--parallel", str(args.jobs)],
            ):
                subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
        binary = build / "marabou_solver_capture"
        command = [str(binary), str(output), args.scenario]
        if args.query_file is not None:
            native_input = (output / (stem + "_prepared.mqx") if prepared_bytes is not None
                            else args.query_file.resolve())
            command = [str(binary), str(output), "file-preprocess" if args.preprocess else "file",
                       str(native_input)]
        run = subprocess.run(command, cwd=output, capture_output=True, text=True, timeout=30)
        (output / (stem + ".log")).write_text(run.stdout + run.stderr)
        if run.returncode != 0:
            adapter.require(False, (run.stderr.strip() or "native capture failed") +
                            f" (exit {run.returncode})")
        print(run.stdout, end="")
        if args.query_file is not None:
            return capture_query_file(output, stem, query_bytes, binary, build, root, revision)
        query, query_hash = adapter.load_json(output / (stem + "_query.json"))
        source, source_hash = adapter.load_json(output / (stem + "_source.json"))
        steps, steps_hash = adapter.load_json(output / (stem + "_steps.json"))
        sat = args.scenario == "relu_sat"
        if sat:
            # No certificate exists; the candidate witness is the native assignment.
            assignment, assignment_hash = adapter.load_json(output / (stem + "_assignment.json"))
            before, before_hash = adapter.load_json(output / (stem + "_before_relu.json"))
            introductions, introductions_hash = adapter.load_json(output / (stem + "_relu_steps.json"))
            witness = assignment_adapter.reconstruct(source, steps, query, assignment, before, introductions)
            adapter.require(witness.reconstruction == assignment_adapter.EXACT,
                            "expected the native doubles themselves to be an exact model")
        else:
            evidence, proof_hash = adapter.load_json(output / (stem + ".json"))
        if sat:
            certificate = None
        elif args.scenario in ("relu_sequence", "relu_chain"):
            before, before_hash = adapter.load_json(output / (stem + "_before_relu.json"))
            introductions, introductions_hash = adapter.load_json(output / (stem + "_relu_steps.json"))
            introduced = sequence_adapter.reconstruct(before, introductions, source, steps, query, evidence)
            replay = introduced.after
        elif args.scenario == "relu_intro":
            before, before_hash = adapter.load_json(output / (stem + "_before_relu.json"))
            introduction, introduction_hash = adapter.load_json(output / (stem + "_relu_step.json"))
            introduced = intro_adapter.reconstruct(before, introduction, source, steps, query, evidence)
            replay = introduced.after
        else:
            replay = source_adapter.reconstruct(source, steps, query, evidence)
        if not sat:
            certificate = replay.certificate
        if sat:
            pass  # The exact check above and the emitted HOL theory cover the witness.
        elif args.scenario == "linear":
            adapter.require(isinstance(certificate, adapter.Leaf), "expected a linear certificate")
        elif args.scenario == "relu":
            adapter.require(isinstance(certificate, adapter.LinearBound) and
                            isinstance(certificate.child, adapter.ReluUpper) and
                            isinstance(certificate.child.child, adapter.Leaf),
                            "expected a checked linear premise, ReLU propagation, and linear leaf")
        elif args.scenario == "relu_sequence":
            continuation = certificate
            pairs = []
            while isinstance(continuation, adapter.LinearBound) and isinstance(continuation.child, adapter.ReluUpper):
                upper = continuation.child
                pairs.append((upper.x, upper.y))
                continuation = upper.child
            adapter.require(len(pairs) == 2 and set(pairs) == {(0, 1), (2, 3)} and
                            isinstance(continuation, adapter.Leaf),
                            "expected two explained ReLU upper rules followed by a linear leaf")
        elif args.scenario == "relu_chain":
            continuation = certificate
            kinds, pairs = [], []
            while isinstance(continuation, adapter.LinearBound) and isinstance(
                    continuation.child, (adapter.ReluUpper, adapter.ReluAuxUpper, adapter.ReluOutputAuxUpper)):
                rule = continuation.child
                kinds.append(type(rule))
                pairs.append((rule.x, rule.y))
                continuation = rule.child
            adapter.require(kinds == [adapter.ReluUpper, adapter.ReluAuxUpper,
                                      adapter.ReluUpper, adapter.ReluOutputAuxUpper] and
                            pairs == [(0, 1), (2, 3), (2, 3), (2, 3)] and
                            isinstance(continuation, adapter.Leaf),
                            "expected the complete four-lemma chain and terminal leaf")
        elif args.scenario == "relu_aux_inactive":
            adapter.require(isinstance(certificate, adapter.LinearBound) and
                            isinstance(certificate.child, adapter.ReluAuxLowerOutputUpper) and
                            isinstance(certificate.child.child, adapter.Leaf),
                            "expected a checked auxiliary lower premise, output-zero propagation, "
                            "and a linear leaf")
        elif args.scenario == "relu_split":
            adapter.require(isinstance(certificate, adapter.Split) and
                            (certificate.x, certificate.y) == (0, 1) and
                            isinstance(certificate.active, adapter.Leaf) and
                            isinstance(certificate.inactive, adapter.Leaf),
                            "expected a binary ReLU split with two checked linear leaves")
        else:
            adapter.require(isinstance(certificate, adapter.LinearBound) and
                            isinstance(certificate.child, adapter.ReluAuxUpper),
                            "expected a checked lower premise followed by auxiliary propagation")
            continuation = certificate.child.child
            if args.scenario in ("relu_aux", "relu_intro"):
                adapter.require(isinstance(continuation, adapter.LinearBound) and
                                isinstance(continuation.child, adapter.ReluUpper),
                                "expected an additional explained output-upper propagation")
                continuation = continuation.child.child
            adapter.require(isinstance(continuation, adapter.Leaf), "expected a final linear leaf")
        provenance = build_record(build, binary, root, revision)
        provenance.update({
            "scenario": args.scenario,
            "processed_query_sha256": query_hash,
            "source_query_sha256": source_hash,
            "introduction_list_sha256": steps_hash,
            "run_report_sha256": sha256(output / (stem + "_run.json")),
            "solver_log_sha256": sha256(output / (stem + ".log")),
            "assurance": "Provenance only; replay proves the explicit captured source query, "
                         "its equisatisfiability with the processed query, and the latter's UNSAT. "
                         "The C++ execution and JSON decoding are not verified.",
        })
        if not sat:
            provenance["certificate_sha256"] = proof_hash
        if args.scenario == "relu_intro":
            provenance.update({
                "before_relu_query_sha256": before_hash,
                "relu_introduction_sha256": introduction_hash,
                "relu_intro_importer_sha256": sha256(Path(intro_adapter.__file__)),
                "assurance": "Provenance only; replay proves the explicit before-ReLU query "
                             "UNSAT through checked ReLU and tableau introductions and the native proof. "
                             "C++ execution, extraction, and JSON decoding are not verified.",
            })
        if sat:
            provenance.update({
                "assignment_sha256": assignment_hash,
                "assignment_importer_sha256": sha256(Path(assignment_adapter.__file__)),
                "before_relu_query_sha256": before_hash,
                "relu_introduction_sequence_sha256": introductions_hash,
                "relu_sequence_importer_sha256": sha256(Path(sequence_adapter.__file__)),
                "assurance": "Provenance only; replay proves that the exactly reconstructed "
                             "native assignment is a real model of the explicit processed, source "
                             "and before-ReLU queries. C++ execution, extraction, and JSON decoding "
                             "are not verified.",
            })
        if args.scenario in ("relu_sequence", "relu_chain"):
            provenance.update({
                "before_relu_query_sha256": before_hash,
                "relu_introduction_sequence_sha256": introductions_hash,
                "relu_sequence_importer_sha256": sha256(Path(sequence_adapter.__file__)),
                "assurance": "Provenance only; replay proves the explicit before-ReLU query "
                             "UNSAT through checked finite ReLU and tableau introductions and "
                             "the native proof. C++ execution, extraction, and JSON decoding are not verified.",
            })
        (output / (stem + "_provenance.json")).write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n")
        replay_arguments = [
            "--source", str(output / (stem + "_source.json")),
            "--steps", str(output / (stem + "_steps.json")),
            "--query", str(output / (stem + "_query.json")),
            "--output", str(output / (theory + ".thy")), "--session"]
        if not sat:
            replay_arguments[6:6] = ["--certificate", str(output / (stem + ".json"))]
        if sat:
            result = assignment_adapter.main([
                "--before-relu", str(output / (stem + "_before_relu.json")),
                "--relu-steps", str(output / (stem + "_relu_steps.json")),
                "--assignment", str(output / (stem + "_assignment.json")),
            ] + replay_arguments)
        elif args.scenario in ("relu_sequence", "relu_chain"):
            result = sequence_adapter.main([
                "--before-relu", str(output / (stem + "_before_relu.json")),
                "--relu-steps", str(output / (stem + "_relu_steps.json")),
            ] + replay_arguments)
        elif args.scenario == "relu_intro":
            result = intro_adapter.main([
                "--before-relu", str(output / (stem + "_before_relu.json")),
                "--relu-step", str(output / (stem + "_relu_step.json")),
            ] + replay_arguments)
        else:
            result = source_adapter.main(replay_arguments)
        adapter.require(result == 0, "could not prepare the replay theory")
    except (adapter.ImportFailure, OSError, subprocess.SubprocessError) as error:
        logs = f"Available build/run logs are in {output}.\n" if (output / "build.log").exists() else ""
        parser.exit(1, f"Capture failed: {error}\n{logs}")
    print("Capture complete. Build this replay session with -d Isabelle -D OUTPUT_DIRECTORY.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
