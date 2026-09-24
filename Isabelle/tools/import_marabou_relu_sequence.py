#!/usr/bin/env python3
"""Import finite native ReLU introductions, tableau steps and a native proof.

The six inputs include independent queries before and after the ReLU calls.
Every plain ReLU must receive one fresh auxiliary, with an explicit finite
input lower bound. Only a successful Isabelle replay certifies the HOL data.
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
    introductions: tuple[Introduction, ...]
    after: source.Replay


def check_introductions(obj, before, after):
    """Early rejection only; HOL recomputes the guarded sequence and result."""
    proof.fields(obj, ("format", "steps"))
    proof.require(obj["format"] == "marabou-relu-aux-sequence-v1",
                  "unsupported ReLU introduction sequence format")
    entries = proof.array(obj["steps"])
    proof.require(len(entries) <= proof.MAX_VARS, "too many ReLU introductions")
    proof.require(len(entries) == len(before.relus),
                  "every plain ReLU requires exactly one introduction")
    current = before
    result = []
    for entry in entries:
        proof.fields(entry, ("input", "output", "auxiliary", "lower"))
        step = Introduction(proof.index(entry["input"], current.n),
                            proof.index(entry["output"], current.n),
                            proof.index(entry["auxiliary"], after.n),
                            proof.rational(entry["lower"]))
        proof.require((step.x, step.y) in current.relu_metadata,
                      "selected plain ReLU is absent or already introduced")
        used = {v for e in current.equations for _, v in e.terms}
        used.update(b.variable for b in current.bounds)
        used.update(v for r in current.relus for v in r)
        proof.require(step.auxiliary not in used, "ReLU auxiliary is not fresh")
        proof.require(step.auxiliary == current.n, "unsupported native allocation")
        proof.require(proof.Bound(step.x, "L", step.lower) in current.bounds,
                      "selected finite input lower bound is absent")
        current = replace(
            current, n=current.n + 1,
            equations=current.equations + (source.Equation(
                ((proof.ONE, step.y), (-proof.ONE, step.x), (-proof.ONE, step.auxiliary)),
                proof.ZERO),),
            bounds=current.bounds + (
                proof.Bound(step.auxiliary, "L", proof.ZERO),
                proof.Bound(step.auxiliary, "U", max(proof.ZERO, -step.lower))),
            relu_metadata=tuple(
                (step.x, step.y, step.auxiliary) if r == (step.x, step.y) else r
                for r in current.relu_metadata))
        result.append(step)
    proof.require(current == after,
                  "ReLU introduction sequence does not match the independent after query")
    return tuple(result)


def reconstruct(before_obj, introductions_obj, source_obj, steps_obj, query_obj, evidence,
                phase_fixing=None):
    before = source.parse_source(before_obj, plain_relu=True)
    after_source = source.parse_source(source_obj)
    introductions = check_introductions(introductions_obj, before, after_source)
    after = source.reconstruct(source_obj, steps_obj, query_obj, evidence, phase_fixing)
    return Replay(before, introductions, after)


def render_theory(name, replay, before_hash, introductions_hash, source_hash,
                  steps_hash, query_hash, proof_hash):
    proof.require(all(re.fullmatch(r"[0-9a-f]{64}", h)
                      for h in (before_hash, introductions_hash)), "invalid digest")
    introductions = proof.hol_list(
        f"ReLU_Aux_Step {s.x} {s.y} {s.auxiliary} (Some {proof.hol_rat(s.lower)})"
        for s in replay.introductions)
    extension = f'''text \\<open>
  Additional native ReLU introduction sequence and independent before-query.
  Each step checks the current query. The whole final result must equal
  imported_source_query, captured independently after the native calls.
  Before-ReLU query SHA-256: {before_hash}
  ReLU introduction sequence SHA-256: {introductions_hash}
\\<close>

definition imported_before_relu_query :: rat_query where
  "imported_before_relu_query = {source.hol_source(replay.before)}"

definition imported_relu_steps :: "relu_aux_step list" where
  "imported_relu_steps = {introductions}"

lemma imported_relu_introductions_match_source:
  "rat_introduce_relu_aux_sequence imported_before_relu_query imported_relu_steps =
    Some imported_source_query"
  by code_simp

theorem imported_relu_introductions_equisatisfiable:
  "satisfiable (embed_query imported_source_query) \\<longleftrightarrow>
    satisfiable (embed_query imported_before_relu_query)"
  by (rule relu_aux_sequence_satisfiable_iff[OF imported_relu_introductions_match_source])

theorem imported_before_relu_processed_equisatisfiable:
  "satisfiable (embed_query imported_query) \\<longleftrightarrow>
    satisfiable (embed_query imported_before_relu_query)"
  using imported_source_equisatisfiable imported_relu_introductions_equisatisfiable by blast

lemma imported_before_relu_certificate_checked:
  "check_after_relu_aux_sequence imported_before_relu_query imported_relu_steps
    imported_steps imported_certificate"
  by code_simp

theorem imported_before_relu_query_unsatisfiable:
  "unsatisfiable (embed_query imported_before_relu_query)"
  by (rule check_after_relu_aux_sequence_sound[OF imported_before_relu_certificate_checked])

'''
    return source.render_theory(
        name, replay.after, source_hash, steps_hash, query_hash, proof_hash,
        extra_imports=("Marabou_Verification.ReLU_Auxiliary_Sequence",), extra_theory=extension)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name, help_text in (
        ("before-relu", "query captured before the native ReLU introductions"),
        ("relu-steps", "ordered native ReLU introduction records"),
        ("source", "independent query captured after the calls and before Engine initialization"),
        ("steps", "proposed scalar-fixed tableau introduction list"),
        ("query", "independent processed query"),
        ("certificate", "complete native JsonWriter proof"),
        ("output", "generated HOL theory (.thy)"),
    ):
        parser.add_argument("--" + name, required=True, type=Path, help=help_text)
    parser.add_argument("--session", action="store_true", help="also create a standalone ROOT")
    args = parser.parse_args(argv)
    try:
        inputs = (args.before_relu, args.relu_steps, args.source, args.steps, args.query, args.certificate)
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
        parser.exit(1, f"ReLU sequence import rejected: {exc}\n")
    print(f"Wrote {args.output}; build its Isabelle session to establish acceptance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
