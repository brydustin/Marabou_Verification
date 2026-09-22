#!/usr/bin/env python3
"""Compile only the upstream components used by the JSON writer test harness.

No downloads, upstream edits, or full solver build. All build products go under
Isabelle/generated. The output directory must be explicitly supplied.
"""
import argparse
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = root / "upstream/Marabou"
    build = root / "Isabelle/generated/json_writer_build"
    build.mkdir(parents=True, exist_ok=True)
    args.output.mkdir(parents=True, exist_ok=True)
    includes = [source / "src" / d for d in
                ("common", "configuration", "engine", "basis_factorization", "proofs", "nlr")]
    includes += [source / "deps/CVC4", source / "deps/CVC4/include", source / "tools/cxxtest"]
    sources = ["src/" + s + ".cpp" for s in (
        "proofs/JsonWriter", "proofs/UnsatCertificateNode", "proofs/Contradiction",
        "proofs/BoundExplainer", "proofs/UnsatCertificateUtils",
        "proofs/PlcLemma", "engine/ReluConstraint", "engine/PiecewiseLinearConstraint",
        "engine/PiecewiseLinearCaseSplit", "engine/Equation", "engine/Query",
        "engine/TableauRow", "engine/GroundBoundManager",
        "basis_factorization/CSRMatrix", "basis_factorization/SparseUnsortedList",
        "common/MString", "common/FloatUtils", "common/Error", "common/Statistics",
        "common/LinearExpression", "common/real/CommonReal", "common/real/Errno",
        "configuration/GlobalConfiguration", "nlr/NetworkLevelReasoner", "nlr/Layer")]
    sources += ["deps/CVC4/" + s + ".cpp" for s in
                ("context/context", "context/context_mm", "base/check", "base/output", "base/exception")]
    objects = []
    for relative in sources:
        path = source / relative
        obj = build / (relative.replace("/", "_") + ".o")
        # Rebuild reproducibly, including after header changes.
        subprocess.run(["g++", "-std=c++17", "-O1", "-ffunction-sections", "-fdata-sections",
                        *["-I" + str(p) for p in includes], "-c", str(path), "-o", str(obj)],
                       check=True)
        objects.append(str(obj))
    binary = build / "write_fixtures"
    subprocess.run(["g++", "-std=c++17", "-Wl,--gc-sections",
                    *["-I" + str(p) for p in includes], str(Path(__file__).with_name("marabou_json_fixture.cpp")),
                    *objects, "-o", str(binary)], check=True)
    subprocess.run([str(binary), str(args.output.resolve())], check=True)
    print("Wrote nine fixtures using upstream JsonWriter; two explanations were computed "
          "by BoundExplainer on hand-constructed rows. No Engine::solve run.")


if __name__ == "__main__":
    main()
