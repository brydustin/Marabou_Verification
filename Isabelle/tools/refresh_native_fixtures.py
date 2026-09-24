#!/usr/bin/env python3
"""Rerun every saved native capture and refresh its fixtures from the new run.

Provenance is only ever copied from a real rerun, never edited. By default a
rerun must reproduce every saved data artifact (queries, steps, proofs,
assignments) byte-for-byte; only the run report, solver log and provenance
record are replaced. --accept-data-changes also replaces data artifacts; the
generated theories must then be regenerated and rebuilt.
"""
import argparse
import filecmp
from pathlib import Path
import shutil
import subprocess
import sys

import import_marabou_query_file as query_files

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
EXAMPLES = ISABELLE / "examples"
SCENARIOS = ("linear", "relu", "relu_aux", "relu_aux_active", "relu_aux_inactive", "relu_split",
             "relu_intro", "relu_sequence", "relu_chain", "relu_sat")
COMPANIONS = ("_run.json", ".log", "_provenance.json")


def capture(arguments, output, jobs):
    command = [sys.executable, str(ISABELLE / "tools/capture_marabou_solver.py"),
               *arguments, "--output", str(output), "--jobs", str(jobs)]
    run = subprocess.run(command, capture_output=True, text=True)
    (output.parent / (output.name + ".stdout")).write_text(run.stdout + run.stderr)
    if run.returncode != 0:
        raise RuntimeError(f"{' '.join(arguments)} failed:\n{run.stdout}{run.stderr}")


def outputs(directory, stem):
    """Suffix -> path for every artifact the harness wrote for this stem."""
    return {path.name[len(stem):]: path for path in sorted(directory.iterdir())
            if path.name.startswith(stem) and path.name[len(stem):len(stem) + 1] in (".", "_")}


def refresh(directory, stem, saved_stem, reference_stem, accept, report):
    """Copy companions to saved_stem; data must equal reference_stem's fixtures.

    A data artifact with no saved counterpart is new and is always saved."""
    changed, new = [], []
    for suffix, path in outputs(directory, stem).items():
        if suffix in COMPANIONS:
            shutil.copyfile(path, FIXTURES / (saved_stem + suffix))
            continue
        reference = FIXTURES / (reference_stem + suffix)
        if not reference.exists():
            new.append(saved_stem + suffix)
            shutil.copyfile(path, FIXTURES / (saved_stem + suffix))
        elif not filecmp.cmp(path, reference, shallow=False):
            changed.append(reference.name)
            if accept:
                shutil.copyfile(path, FIXTURES / (saved_stem + suffix))
    report.append((saved_stem, changed, new))
    return changed


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tag", required=True, help="new directory name under Isabelle/generated")
    parser.add_argument("--only", nargs="*", help="scenario or example names to rerun")
    parser.add_argument("--accept-data-changes", action="store_true")
    parser.add_argument("--jobs", type=int, default=4)
    args = parser.parse_args(argv)
    root = ISABELLE / "generated" / args.tag
    if root.exists():
        parser.exit(1, f"{root} already exists; choose a new tag\n")
    root.mkdir(parents=True)
    wanted = set(args.only) if args.only else None
    report, failures = [], []
    for scenario in SCENARIOS:
        if wanted is not None and scenario not in wanted:
            continue
        output = root / scenario
        capture(["--scenario", scenario], output, args.jobs)
        stem = "solver_" + scenario
        if refresh(output, stem, stem, stem, args.accept_data_changes, report):
            failures.append(scenario)
    # Files whose runs reproduce a scenario's data keep only their companions.
    for example, scenario, _ in query_files.EXAMPLES:
        if wanted is not None and example not in wanted:
            continue
        output = root / ("file_" + example)
        capture(["--query-file", str(EXAMPLES / (example + ".mqx"))], output, args.jobs)
        if refresh(output, "solver_file", "file_" + example, "solver_" + scenario, False, report):
            failures.append(example)
    # Other files keep their complete artifact set.
    for example, preprocess in ([(e, False) for e, _ in query_files.FULL_ARTIFACT_EXAMPLES] +
                                [(e, True) for e, _ in query_files.PREPROCESSED_EXAMPLES]):
        if wanted is not None and example not in wanted:
            continue
        output = root / ("file_" + example)
        capture(["--query-file", str(EXAMPLES / (example + ".mqx"))] + (["--preprocess"] if preprocess else []),
                output, args.jobs)
        saved = "file_" + example
        if refresh(output, "solver_file", saved, saved, args.accept_data_changes, report):
            failures.append(example)
    for saved, changed, new in report:
        print(f"{saved}: " + ("data identical" if not changed else "DATA CHANGED: " + ", ".join(changed)) +
              ("; new: " + ", ".join(new) if new else ""))
    if failures and not args.accept_data_changes:
        print("Companions were refreshed, but data differed for: " + ", ".join(failures) +
              ". Investigate, or rerun with --accept-data-changes.", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
