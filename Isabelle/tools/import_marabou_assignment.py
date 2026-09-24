#!/usr/bin/env python3
"""Import a native SAT assignment and its captured queries for exact HOL checking.

Inputs are the source query, proposed tableau introductions, the processed
query and the native assignment, optionally preceded by the query before
native ReLU introductions and their ordered records. Each native double is
reconstructed as an exact rational: first its exact binary value; only if
that candidate fails the exact check, the simplest rational within 1e-9 of
each value. Neither reconstruction is trusted. The emitted theory proves
acceptance by code_simp and derives models from check_rat_assignment_sound.
A rejected or unrepairable assignment says nothing about satisfiability.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import math
from pathlib import Path
import re
import sys

import import_marabou_json as proof
import import_marabou_relu_sequence as sequence
import import_marabou_source as source

HEX_FLOAT = re.compile(r"-?0x[0-9a-f]+(\.[0-9a-f]+)?p[+-][0-9]{1,4}")
REPAIR_DISTANCE = Fraction(1, 10**9)
REPAIR_DENOMINATOR = 10**6
EXACT = "exact binary values of the native doubles"
REPAIRED = "simplest rationals within 1e-9 of the native doubles"


@dataclass(frozen=True)
class SatReplay:
    before: source.Source | None
    introductions: tuple[sequence.Introduction, ...]
    source: source.Source
    column_source: source.Source
    steps: tuple[tuple[int, int], ...]
    instance: proof.Instance
    assignment: tuple[Fraction, ...]
    reconstruction: str


def parse_assignment(obj, n):
    """Return the exact binary value of every native double, in variable order."""
    proof.fields(obj, ("format", "variables", "values"))
    proof.require(obj["format"] == "marabou-assignment-v1", "unsupported assignment format")
    proof.require(obj["variables"] == n and type(obj["variables"]) is int,
                  "assignment must cover exactly the processed variables")
    entries = proof.array(obj["values"])
    proof.require(len(entries) == n, "assignment must list every processed variable once")
    result = []
    for i, entry in enumerate(entries):
        proof.fields(entry, ("var", "value", "hex"))
        proof.require(proof.index(entry["var"], n) == i, "assignment variables must be listed in order")
        token = entry["hex"]
        proof.require(type(token) is str and len(token) <= 64 and HEX_FLOAT.fullmatch(token),
                      "invalid hexadecimal double")
        try:
            binary = float.fromhex(token)
        except OverflowError:
            binary = math.inf
        proof.require(math.isfinite(binary), "nonfinite assignment value")
        decimal = proof.rational(entry["value"])
        # The decimal token is only a readable copy; it must round to the same double.
        proof.require(float(decimal) == binary, "decimal and hexadecimal values disagree")
        result.append(Fraction(binary))
    return tuple(result)


def value(values, variable):
    return values[variable] if variable < len(values) else proof.ZERO


def relu_ok(values, relus):
    return all(value(values, y) == max(proof.ZERO, value(values, x)) for x, y in relus)


def bounds_ok(values, bounds):
    return all(b.value <= value(values, b.variable) if b.kind == "L"
               else value(values, b.variable) <= b.value for b in bounds)


def processed_model(instance, values):
    """Early exact check; the emitted HOL theorem is the authority."""
    query = instance.query
    return (all(e.constant + sum(a * value(values, x) for a, x in e.terms) == 0
                for e in query.equations) and
            bounds_ok(values, query.bounds) and relu_ok(values, query.relus))


def source_model(src, values):
    return (all(sum(a * value(values, x) for a, x in e.terms) == e.scalar for e in src.equations) and
            bounds_ok(values, src.bounds) and relu_ok(values, src.relus))


def reconstruct_values(instance, binary):
    if processed_model(instance, binary):
        return binary, EXACT
    repaired = []
    for exact in binary:
        candidate = exact.limit_denominator(REPAIR_DENOMINATOR)
        repaired.append(candidate if abs(candidate - exact) <= REPAIR_DISTANCE else exact)
    repaired = tuple(repaired)
    proof.require(processed_model(instance, repaired),
                  "native assignment is not an exact model of the processed query, "
                  "and no nearby small-denominator repair is one")
    return repaired, REPAIRED


def reconstruct(source_obj, steps_obj, query_obj, assignment_obj,
                before_obj=None, introductions_obj=None):
    proof.require((before_obj is None) == (introductions_obj is None),
                  "a before-ReLU query requires its introduction records and vice versa")
    src, column_source, steps, instance = source.reconstruct_queries(source_obj, steps_obj, query_obj)
    before, introductions = None, ()
    if before_obj is not None:
        before = source.parse_source(before_obj, plain_relu=True)
        introductions = sequence.check_introductions(introductions_obj, before, src)
    values, how = reconstruct_values(instance, parse_assignment(assignment_obj, instance.n))
    # The source and before queries only lose constraints on fresh variables.
    proof.require(source_model(src, values), "assignment does not satisfy the source query")
    proof.require(before is None or source_model(before, values),
                  "assignment does not satisfy the before-ReLU query")
    return SatReplay(before, introductions, src, column_source, steps, instance, values, how)


def render_theory(name, replay, hashes):
    proof.require(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is not None, "invalid theory name")
    proof.require(all(re.fullmatch(r"[0-9a-f]{64}", h) for h in hashes.values()), "invalid digest")
    labels = (("before", "Before-ReLU query"), ("introductions", "ReLU introduction sequence"),
              ("source", "Source query"), ("steps", "Introduction list"),
              ("query", "Processed query"), ("assignment", "Native assignment"))
    digests = "".join(f"\n  {label} SHA-256: {hashes[key]}" for key, label in labels if key in hashes)
    assignment = proof.hol_list(f"({i}, {proof.hol_rat(q)})" for i, q in enumerate(replay.assignment))
    steps = proof.hol_list(f"({i}, {s})" for i, s in replay.steps)
    before = ""
    if replay.before is not None:
        introductions = proof.hol_list(
            f"ReLU_Aux_Step {s.x} {s.y} {s.auxiliary} (Some {proof.hol_rat(s.lower)})"
            for s in replay.introductions)
        before = f'''definition imported_before_relu_query :: rat_query where
  "imported_before_relu_query = {source.hol_source(replay.before)}"

definition imported_relu_steps :: "relu_aux_step list" where
  "imported_relu_steps = {introductions}"

lemma imported_relu_introductions_match_source:
  "rat_introduce_relu_aux_sequence imported_before_relu_query imported_relu_steps =
    Some imported_source_query"
  by code_simp

lemma imported_before_relu_assignment_checked:
  "check_rat_assignment imported_before_relu_query imported_assignment"
  by code_simp

theorem imported_before_relu_query_model:
  "satisfies_query (assignment_valuation imported_assignment)
    (embed_query imported_before_relu_query)"
  by (rule check_rat_assignment_sound[OF imported_before_relu_assignment_checked])

theorem imported_before_relu_query_satisfiable_via_processed:
  "satisfiable (embed_query imported_before_relu_query)"
  using relu_aux_sequence_satisfiable_iff[OF imported_relu_introductions_match_source]
    imported_source_query_satisfiable_via_processed
  by blast

'''
    return f'''theory {name}
  imports "Marabou_Verification.Rational_Assignment"
begin

text \\<open>
  Generated by the untrusted assignment adapter. Query numbers denote exact
  rationals decoded from serialized decimal tokens. Assignment values are the
  {replay.reconstruction}.
  The code_simp proofs below check every linear atom, bound and ReLU exactly;
  the reconstruction itself is not trusted. The C++ solver, extraction and
  JSON decoding are not verified.{digests}
\\<close>

definition imported_source_query :: rat_query where
  "imported_source_query = {source.hol_source(replay.source)}"

definition imported_source_column_query :: rat_query where
  "imported_source_column_query = {source.hol_source(replay.column_source)}"

lemma imported_source_term_order:
  "satisfies_query v (embed_query imported_source_column_query) \\<longleftrightarrow>
    satisfies_query v (embed_query imported_source_query)"
  by (simp add: imported_source_query_def imported_source_column_query_def
      embed_query_def satisfies_query_def algebra_simps)

definition imported_steps :: "fixed_aux_step list" where
  "imported_steps = {steps}"

definition imported_query :: rat_query where
  "imported_query = {proof.hol_query(replay.instance.query)}"

definition imported_assignment :: rat_assignment where
  "imported_assignment = {assignment}"

lemma imported_steps_match_query:
  "rat_introduce_fixed_aux_sequence imported_source_column_query imported_steps =
    Some imported_query"
  by code_simp

lemma imported_assignment_checked:
  "check_rat_assignment imported_query imported_assignment"
  by code_simp

theorem imported_query_model:
  "satisfies_query (assignment_valuation imported_assignment) (embed_query imported_query)"
  by (rule check_rat_assignment_sound[OF imported_assignment_checked])

theorem imported_query_satisfiable:
  "satisfiable (embed_query imported_query)"
  by (rule check_rat_assignment_satisfiable[OF imported_assignment_checked])

lemma imported_source_assignment_checked:
  "check_rat_assignment imported_source_query imported_assignment"
  by code_simp

theorem imported_source_query_model:
  "satisfies_query (assignment_valuation imported_assignment) (embed_query imported_source_query)"
  by (rule check_rat_assignment_sound[OF imported_source_assignment_checked])

theorem imported_source_query_satisfiable_via_processed:
  "satisfiable (embed_query imported_source_query)"
proof -
  have "satisfiable (embed_query imported_source_column_query)"
    by (rule fixed_aux_sequence_assignment_satisfiable[OF imported_steps_match_query
          imported_assignment_checked])
  then show ?thesis by (simp add: satisfiable_def imported_source_term_order)
qed

{before}end
'''


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name, help_text in (
        ("source", "pre-initialization source-query JSON"),
        ("steps", "proposed fixed-auxiliary introduction list JSON"),
        ("query", "independent processed-query JSON"),
        ("assignment", "native assignment JSON"),
        ("output", "generated theory file (.thy)"),
    ):
        parser.add_argument("--" + name, required=True, type=Path, help=help_text)
    parser.add_argument("--before-relu", type=Path, help="query before native ReLU introductions")
    parser.add_argument("--relu-steps", type=Path, help="ordered native ReLU introduction records")
    parser.add_argument("--session", action="store_true", help="also create a standalone ROOT")
    args = parser.parse_args(argv)
    try:
        inputs = {"source": args.source, "steps": args.steps, "query": args.query,
                  "assignment": args.assignment}
        proof.require((args.before_relu is None) == (args.relu_steps is None),
                      "--before-relu and --relu-steps must be given together")
        if args.before_relu is not None:
            inputs.update(before=args.before_relu, introductions=args.relu_steps)
        proof.require(args.output.suffix == ".thy", "output must have suffix .thy")
        proof.require(args.output.resolve() not in [p.resolve() for p in inputs.values()],
                      "output cannot overwrite an input")
        root = args.output.parent / "ROOT"
        proof.require(not args.session or not root.exists(), "refusing to replace an existing ROOT")
        loaded = {key: proof.load_json(path) for key, path in inputs.items()}
        replay = reconstruct(*(loaded[k][0] for k in ("source", "steps", "query", "assignment")),
                             *(loaded[k][0] if k in loaded else None for k in ("before", "introductions")))
        theory = render_theory(args.output.stem, replay, {k: v[1] for k, v in loaded.items()})
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(theory, encoding="utf-8")
        if args.session:
            root.write_text("session Marabou_Import_Replay = Marabou_Verification +\n"
                            "  options [document = false, quick_and_dirty = false]\n"
                            f"  theories {args.output.stem}\n", encoding="utf-8")
    except (proof.ImportFailure, OSError, RecursionError, ValueError, OverflowError) as exc:
        parser.exit(1, f"Assignment import rejected: {exc}\n")
    print(f"Wrote {args.output}; build its Isabelle session to establish acceptance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
