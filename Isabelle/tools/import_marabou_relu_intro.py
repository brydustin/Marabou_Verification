#!/usr/bin/env python3
"""Import one native ReLU introduction followed by tableau steps and a proof.

Six independent input artifacts describe the before/after queries, the ReLU
step, the scalar-fixed sequence, the processed query, and the native proof.
Only a successful Isabelle build certifies the explicit generated HOL query.
The initial supported case has one plain ReLU and a finite input lower bound.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction
from pathlib import Path
import re
import sys

import import_marabou_json as proof
import import_marabou_source as source


@dataclass(frozen=True)
class Introduction:
    x: int
    y: int
    auxiliary: int
    lower: Fraction


@dataclass(frozen=True)
class Replay:
    before: source.Source
    introduction: Introduction
    after: source.Replay


def parse_introduction(obj, before, after):
    proof.fields(obj, ("format", "input", "output", "auxiliary", "lower"))
    proof.require(obj["format"] == "marabou-relu-aux-introduction-v1",
                  "unsupported ReLU introduction format")
    step = Introduction(proof.index(obj["input"], before.n),
                        proof.index(obj["output"], before.n),
                        proof.index(obj["auxiliary"], after.n),
                        proof.rational(obj["lower"]))
    proof.require(len(before.relu_metadata) == 1,
                  "this import path requires exactly one plain ReLU")
    proof.require((step.x, step.y) in before.relus, "selected ReLU is absent")
    used = {v for equation in before.equations for _, v in equation.terms}
    used.update(b.variable for b in before.bounds)
    used.update(v for r in before.relus for v in r)
    proof.require(step.auxiliary not in used, "ReLU auxiliary is not fresh")
    proof.require(proof.Bound(step.x, "L", step.lower) in before.bounds,
                  "selected finite input lower bound is absent")
    proof.require(after.n == before.n + 1 and step.auxiliary == before.n,
                  "unsupported native allocation")
    return step


def reconstruct(before_obj, introduction_obj, source_obj, steps_obj, query_obj, evidence):
    before = source.parse_source(before_obj, plain_relu=True)
    after_source = source.parse_source(source_obj)
    step = parse_introduction(introduction_obj, before, after_source)
    # Reconstruct every new atom; never trust a supplied cap or auxiliary row.
    expected = replace(
        before, n=before.n + 1,
        equations=before.equations + (source.Equation(
            ((proof.ONE, step.y), (-proof.ONE, step.x), (-proof.ONE, step.auxiliary)),
            proof.ZERO),),
        bounds=before.bounds + (proof.Bound(step.auxiliary, "L", proof.ZERO),
                                proof.Bound(step.auxiliary, "U", max(proof.ZERO, -step.lower))),
        relu_metadata=((step.x, step.y, step.auxiliary),))
    proof.require(expected == after_source,
                  "ReLU introduction result does not match the independent after query")
    after = source.reconstruct(source_obj, steps_obj, query_obj, evidence)
    return Replay(before, step, after)


def render_theory(name, replay, before_hash, introduction_hash, source_hash,
                  steps_hash, query_hash, proof_hash):
    proof.require(all(re.fullmatch(r"[0-9a-f]{64}", h)
                      for h in (before_hash, introduction_hash)), "invalid digest")
    step = replay.introduction
    arguments = f"{step.x} {step.y} {step.auxiliary} (Some {proof.hol_rat(step.lower)})"
    extension = f'''text \\<open>
  Additional capture before the native ReLU auxiliary introduction.
  The preceding imported_source_query is the independently captured result
  of that call, before Engine initialization. ReLU membership, freshness,
  the finite input lower bound, and the entire result are checked below.
  Before-ReLU query SHA-256: {before_hash}
  ReLU introduction SHA-256: {introduction_hash}
\\<close>

definition imported_before_relu_query :: rat_query where
  "imported_before_relu_query = {source.hol_source(replay.before)}"

lemma imported_relu_introduction_matches_source:
  "rat_introduce_relu_aux imported_before_relu_query {arguments} =
    Some imported_source_query"
  by code_simp

theorem imported_relu_introduction_equisatisfiable:
  "satisfiable (embed_query imported_source_query) \\<longleftrightarrow>
    satisfiable (embed_query imported_before_relu_query)"
  by (rule rat_introduce_relu_aux_satisfiable_iff[OF imported_relu_introduction_matches_source])

theorem imported_before_relu_processed_equisatisfiable:
  "satisfiable (embed_query imported_query) \\<longleftrightarrow>
    satisfiable (embed_query imported_before_relu_query)"
  using imported_source_equisatisfiable imported_relu_introduction_equisatisfiable by blast

lemma imported_before_relu_certificate_checked:
  "check_after_relu_aux imported_before_relu_query {arguments}
    imported_steps imported_certificate"
  by code_simp

theorem imported_before_relu_query_unsatisfiable:
  "unsatisfiable (embed_query imported_before_relu_query)"
  by (rule check_after_relu_aux_sound[OF imported_before_relu_certificate_checked])

'''
    return source.render_theory(
        name, replay.after, source_hash, steps_hash, query_hash, proof_hash,
        extra_imports=("Marabou_Verification.Rational_ReLU_Auxiliary",), extra_theory=extension)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name, help_text in (
        ("before-relu", "query captured before native ReLU auxiliary introduction"),
        ("relu-step", "native ReLU introduction record"),
        ("source", "independent query captured after that call and before Engine initialization"),
        ("steps", "proposed scalar-fixed tableau introduction list"),
        ("query", "independent processed query"),
        ("certificate", "complete native JsonWriter proof"),
        ("output", "generated HOL theory (.thy)"),
    ):
        parser.add_argument("--" + name, required=True, type=Path, help=help_text)
    parser.add_argument("--session", action="store_true", help="also create a standalone ROOT")
    args = parser.parse_args(argv)
    try:
        inputs = (args.before_relu, args.relu_step, args.source, args.steps, args.query, args.certificate)
        proof.require(args.output.suffix == ".thy", "output must have suffix .thy")
        proof.require(args.output.resolve() not in [p.resolve() for p in inputs],
                      "output cannot overwrite an input")
        root = args.output.parent / "ROOT"
        proof.require(not args.session or not root.exists(), "refusing to replace an existing ROOT")
        loaded = [proof.load_json(p) for p in inputs]
        replay = reconstruct(*(obj for obj, _ in loaded))
        theory = render_theory(args.output.stem, replay, *(digest for _, digest in loaded))
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(theory, encoding="utf-8")
        if args.session:
            root.write_text("session Marabou_Import_Replay = Marabou_Verification +\n"
                            "  options [document = false, quick_and_dirty = false]\n"
                            f"  theories {args.output.stem}\n", encoding="utf-8")
    except (proof.ImportFailure, OSError, RecursionError) as exc:
        parser.exit(1, f"ReLU introduction import rejected: {exc}\n")
    print(f"Wrote {args.output}; build its Isabelle session to establish acceptance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
