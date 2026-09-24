#!/usr/bin/env python3
"""One invocation: solve an exact query file natively and prove the result in Isabelle.

Runs capture_marabou_solver.py --query-file, then builds the generated session
with Isabelle. Success means Isabelle checked the stated theorem about the
file's decoded bytes; any rejection names its reason and claims nothing.
"""
import argparse
import contextlib
import io
import os
from pathlib import Path
import shutil
import subprocess
import sys

import capture_marabou_solver as driver

ISABELLE_DIR = Path(__file__).resolve().parents[1]


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("query_file", type=Path, help="marabou-exact-query-v1 file (.mqx)")
    parser.add_argument("output", type=Path, help="new or empty output directory")
    parser.add_argument("--jobs", type=int, default=4, help="native build jobs")
    parser.add_argument("--preprocess", action="store_true",
                        help="run Marabou's own preprocessing; Isabelle checks its result")
    args = parser.parse_args(argv)
    isabelle = os.environ.get("ISABELLE_TOOL") or shutil.which("isabelle")
    if isabelle is None:
        parser.exit(1, "Rejected: no isabelle executable on PATH (or set ISABELLE_TOOL).\n")
    captured = io.StringIO()
    try:
        with contextlib.redirect_stdout(captured):
            status = driver.main(["--query-file", str(args.query_file), "--output", str(args.output),
                                  "--jobs", str(args.jobs)] + (["--preprocess"] if args.preprocess else []))
    except SystemExit as exit_:
        status = exit_.code
    if status != 0:
        parser.exit(1, "Rejected before Isabelle; see the message above. No theorem was produced.\n")
    output = args.output.resolve()
    with (output / "isabelle_build.log").open("w") as log:
        build = subprocess.run([isabelle, "build", "-d", str(ISABELLE_DIR), "-D", str(output)],
                               stdout=log, stderr=subprocess.STDOUT)
    if build.returncode != 0:
        parser.exit(1, f"Rejected by Isabelle (exit {build.returncode}); see "
                       f"{output / 'isabelle_build.log'}. No theorem was established.\n")
    theorem = (output / "Query_File_Theorem.thy").read_text()
    if "theorem query_file_unsatisfiable:" in theorem:
        name = "query_file_unsatisfiable"
        statement = "decode_query query_file = Some Q ==> unsatisfiable (embed_query Q)"
    else:
        name = "query_file_model"
        statement = ("decode_query query_file = Some Q ==> satisfies_query "
                     "(assignment_valuation Captured_Query_File.imported_assignment) (embed_query Q)")
    print(f"Isabelle checked Query_File_Theorem.{name}:")
    print(f"  {statement}")
    print(f"where query_file is the exact content of {output / 'query.mqx'}, a copy of {args.query_file}.")
    print("Trust boundary: the Isabelle/HOL kernel and the build-time file check; the C++ reader,")
    print("solver, native preprocessing, capture, any local inequality preparation and the JSON")
    print("import are not trusted for this theorem (notes/QUERY_FILE_WORKFLOW.md).")
    return 0


if __name__ == "__main__":
    sys.exit(main())
