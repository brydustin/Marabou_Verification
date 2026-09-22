#!/usr/bin/env python3
"""Build the unchanged native engine, capture its tiny UNSAT run, and prepare HOL replay.

No automatic downloads, system installation, or upstream edits. Supply an empty
output directory. A successful capture is candidate evidence; build the emitted
Isabelle session to establish the processed query's UNSAT theorem.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import sys

import import_marabou_json as adapter


PINNED_REVISION = "1c2f4788c32e2f4e407c356b763a8025c5578722"


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command_output(command, **kwargs):
    return subprocess.check_output(command, text=True, **kwargs).strip()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--scenario", choices=("linear", "relu", "relu_aux", "relu_aux_active"),
                        default="linear")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args(argv)
    root = Path(__file__).resolve().parents[2]
    upstream = root / "upstream/Marabou"
    build = root / "Isabelle/generated/solver_capture_build"
    output = args.output.resolve()
    stem = "solver_" + args.scenario
    theory = "Captured_Solver_" + args.scenario.title()
    try:
        adapter.require(1 <= args.jobs <= 32, "jobs must be between 1 and 32")
        adapter.require(not output.exists() or (output.is_dir() and not any(output.iterdir())),
                        "capture output directory must be empty")
        revision = command_output(["git", "-C", str(upstream), "rev-parse", "HEAD"])
        adapter.require(revision == PINNED_REVISION, "unexpected Marabou revision")
        adapter.require(not command_output(["git", "-C", str(upstream), "status",
                                            "--porcelain", "--untracked-files=all"]),
                        "Marabou checkout must be clean")
        output.mkdir(parents=True, exist_ok=True)
        with (output / "build.log").open("w") as log:
            for command in (
                ["cmake", "-S", str(Path(__file__).with_name("solver_capture")), "-B", str(build),
                 "-DCMAKE_BUILD_TYPE=Release", "-DCMAKE_EXPORT_COMPILE_COMMANDS=ON",
                 "-DMARABOU_SOURCE=" + str(upstream)],
                ["cmake", "--build", str(build), "--parallel", str(args.jobs)],
            ):
                subprocess.run(command, stdout=log, stderr=subprocess.STDOUT, check=True)
        binary = build / "marabou_solver_capture"
        run = subprocess.run([str(binary), str(output), args.scenario], cwd=output, capture_output=True, text=True,
                             timeout=30)
        (output / (stem + ".log")).write_text(run.stdout + run.stderr)
        run.check_returncode()
        print(run.stdout, end="")
        query, query_hash = adapter.load_json(output / (stem + "_query.json"))
        evidence, proof_hash = adapter.load_json(output / (stem + ".json"))
        instance, certificate = adapter.reconstruct(query, evidence)
        if args.scenario == "linear":
            adapter.require(isinstance(certificate, adapter.Leaf), "expected a linear certificate")
        elif args.scenario == "relu":
            adapter.require(isinstance(certificate, adapter.LinearBound) and
                            isinstance(certificate.child, adapter.ReluUpper) and
                            isinstance(certificate.child.child, adapter.Leaf),
                            "expected a checked linear premise, ReLU propagation, and linear leaf")
        else:
            adapter.require(isinstance(certificate, adapter.LinearBound) and
                            isinstance(certificate.child, adapter.ReluAuxUpper),
                            "expected a checked lower premise followed by auxiliary propagation")
            continuation = certificate.child.child
            if args.scenario == "relu_aux":
                adapter.require(isinstance(continuation, adapter.LinearBound) and
                                isinstance(continuation.child, adapter.ReluUpper),
                                "expected an additional explained output-upper propagation")
                continuation = continuation.child.child
            adapter.require(isinstance(continuation, adapter.Leaf), "expected a final linear leaf")
        # Record the actual build inputs and binary. Hashes are provenance, not HOL premises.
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
        provenance = {
            "scenario": args.scenario,
            "marabou_revision": revision,
            "capture_script_sha256": sha256(Path(__file__)),
            "importer_sha256": sha256(Path(adapter.__file__)),
            "cmake_sha256": sha256(Path(__file__).with_name("solver_capture") / "CMakeLists.txt"),
            "binary_sha256": sha256(binary),
            "processed_query_sha256": query_hash,
            "certificate_sha256": proof_hash,
            "run_report_sha256": sha256(output / (stem + "_run.json")),
            "solver_log_sha256": sha256(output / (stem + ".log")),
            "compiled_sources": source_hashes,
            "capture_compile_command": compile_command,
            "compiler_version": command_output([compiler, "--version"]).splitlines()[0],
            "linked_libraries": libraries,
            "cmake_version": command_output(["cmake", "--version"]).splitlines()[0],
            "assurance": "Provenance only; replay proves the explicit processed query, not C++ execution.",
        }
        (output / (stem + "_provenance.json")).write_text(
            json.dumps(provenance, indent=2, sort_keys=True) + "\n")
        result = adapter.main(["--query", str(output / (stem + "_query.json")),
                               "--certificate", str(output / (stem + ".json")),
                               "--output", str(output / (theory + ".thy")), "--session"])
        adapter.require(result == 0, "could not prepare the replay theory")
    except (adapter.ImportFailure, OSError, subprocess.SubprocessError) as error:
        parser.exit(1, f"Capture failed: {error}\nBuild/run logs are in {output}.\n")
    print("Capture complete. Build this replay session with -d Isabelle -D OUTPUT_DIRECTORY.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
