#!/usr/bin/env python3
"""Import a captured source query, proposed introductions, processed query and proof.

This untrusted adapter supports finite equality queries with finite bounds and
existing auxiliary-form ReLUs. It emits explicit HOL data and proof obligations
for term reordering, every introduction, exact processed-query equality, and the
recursive certificate. Only a successful Isabelle build establishes acceptance.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass, replace
from fractions import Fraction
from pathlib import Path
import re
import sys

import import_marabou_json as proof


@dataclass(frozen=True)
class Equation:
    terms: tuple[tuple[Fraction, int], ...]
    scalar: Fraction


@dataclass(frozen=True)
class Source:
    n: int
    equations: tuple[Equation, ...]
    bounds: tuple[proof.Bound, ...]
    relu_metadata: tuple[tuple[int, ...], ...]

    @property
    def relus(self):
        return tuple(r[:2] for r in self.relu_metadata)


@dataclass(frozen=True)
class Replay:
    source: Source
    column_source: Source
    steps: tuple[tuple[int, int], ...]
    instance: proof.Instance
    certificate: object


def parse_source(obj, *, plain_relu=False):
    proof.fields(obj, ("format", "variables", "equations", "lowerBounds",
                       "upperBounds", "constraints"))
    expected_format = "marabou-plain-relu-query-v1" if plain_relu else "marabou-source-query-v1"
    proof.require(obj["format"] == expected_format, "unsupported source format")
    n = obj["variables"]
    proof.require(type(n) is int and 0 < n <= proof.MAX_VARS, "invalid source dimension")
    lower, upper = proof.array(obj["lowerBounds"]), proof.array(obj["upperBounds"])
    proof.require(len(lower) == len(upper) == n, "invalid source bound dimensions")
    bounds = tuple(b for i in range(n) for b in (
        proof.Bound(i, "L", proof.rational(lower[i])),
        proof.Bound(i, "U", proof.rational(upper[i]))))
    rows = proof.array(obj["equations"])
    proof.require(0 < len(rows) <= proof.MAX_ROWS, "invalid source equation count")
    equations = []
    for row in rows:
        proof.fields(row, ("type", "addends", "scalar"))
        proof.require(row["type"] == "EQ", "only source equalities are supported")
        equations.append(Equation(proof.sparse_entries(row["addends"], n),
                                  proof.rational(row["scalar"])))
    relus = []
    for constraint in proof.array(obj["constraints"]):
        proof.fields(constraint, ("constraintType", "vars"))
        proof.require(type(constraint["constraintType"]) is int and
                      constraint["constraintType"] == 0, "only source ReLUs are supported")
        variables = tuple(proof.index(v, n) for v in proof.array(constraint["vars"]))
        arity = 2 if plain_relu else 3
        proof.require(len(variables) == arity and len(set(variables)) == arity,
                      "expected distinct source ReLU variables " +
                      ("[b, f]" if plain_relu else "[b, f, aux]"))
        proof.require(variables[:2] not in [r[:2] for r in relus], "duplicate source ReLU")
        relus.append(variables)
    return Source(n, tuple(equations), bounds, tuple(relus))


def parse_steps(obj, rows, variables):
    proof.fields(obj, ("format", "steps"))
    proof.require(obj["format"] == "marabou-fixed-aux-sequence-v1",
                  "unsupported introduction format")
    entries = proof.array(obj["steps"])
    proof.require(len(entries) <= proof.MAX_VARS, "too many introductions")
    result = []
    for entry in entries:
        proof.fields(entry, ("equation", "variable"))
        result.append((proof.index(entry["equation"], rows),
                       proof.index(entry["variable"], variables)))
    return tuple(result)


def check_introductions(source, steps, instance):
    """Early rejection only: the generated theory independently checks this."""
    equations, bounds = list(source.equations), list(source.bounds)
    used = {v for e in equations for _, v in e.terms}
    used.update(b.variable for b in bounds)
    used.update(v for r in source.relus for v in r)
    for i, s in steps:
        proof.require(s not in used, "introduction variable is not fresh")
        equation = equations[i]
        equations[i] = Equation(equation.terms + ((-proof.ONE, s),), proof.ZERO)
        bounds.extend((proof.Bound(s, "L", equation.scalar),
                       proof.Bound(s, "U", equation.scalar)))
        used.add(s)
    proof.require(all(e.scalar == 0 for e in equations),
                  "introduction result still has a nonzero scalar")
    result = proof.Query(tuple(proof.Expr(proof.ZERO, e.terms) for e in equations),
                         tuple(bounds), source.relus)
    proof.require(result == instance.query,
                  "introduction result does not match the independent processed query")
    proof.require(source.relu_metadata == tuple(r[:3] for r in instance.relu_metadata),
                  "source and processed ReLU metadata differ")


def reconstruct_queries(source_obj, steps_obj, query_obj):
    """Source, column-ordered source, steps and processed instance; no proof."""
    source = parse_source(source_obj)
    instance = proof.parse_instance(query_obj)
    steps = parse_steps(steps_obj, len(source.equations), instance.n)
    # Native CSR serialization is in column order. Preserve the original source
    # separately and emit a HOL proof that this proposed permutation is harmless.
    column_source = replace(source, equations=tuple(
        replace(e, terms=tuple(sorted(e.terms, key=lambda t: t[1])))
        for e in source.equations))
    check_introductions(column_source, steps, instance)
    return source, column_source, steps, instance


def reconstruct(source_obj, steps_obj, query_obj, evidence, phase_fixing=None):
    source, column_source, steps, _ = reconstruct_queries(source_obj, steps_obj, query_obj)
    instance, certificate = proof.reconstruct(query_obj, evidence, phase_fixing)
    return Replay(source, column_source, steps, instance, certificate)


def hol_source(source):
    equations = proof.hol_list(
        f"RatEq {proof.hol_expr(proof.Expr(proof.ZERO, e.terms))} {proof.hol_rat(e.scalar)}"
        for e in source.equations)
    bounds = proof.hol_list(proof.hol_bound(b) for b in source.bounds)
    relus = proof.hol_list(f"ReLU {x} {y}" for x, y in source.relus)
    return ("\\<lparr>rat_linear_atoms = " + equations + ",\n"
            "     rat_query_bounds = " + bounds + ",\n"
            "     rat_relu_atoms = " + relus + "\\<rparr>")


def render_theory(name, replay, source_hash, steps_hash, query_hash, proof_hash,
                  *, extra_imports=(), extra_theory=""):
    # Extensions are internal generator templates, never strings read from JSON.
    proof.require(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is not None, "invalid theory name")
    proof.require(all(re.fullmatch(r"[A-Z][A-Za-z0-9_]*(\.[A-Z][A-Za-z0-9_]*)*", i)
                      for i in extra_imports), "invalid extra import")
    proof.require(all(re.fullmatch(r"[0-9a-f]{64}", h)
                      for h in (source_hash, steps_hash, query_hash, proof_hash)), "invalid digest")
    steps = proof.hol_list(f"({i}, {s})" for i, s in replay.steps)
    imports = "".join(f'\n    "{i}"' for i in extra_imports)
    return f'''theory {name}
  imports "Marabou_Verification.Tableau_Auxiliary_Sequence"{imports}
begin

text \\<open>
  Generated by the untrusted source-query adapter from four captured artifacts.
  Numbers denote exact rationals decoded from serialized decimal tokens.
  The source was captured before initialization; introductions are harness
  proposals recovered from added columns, not a native transformation log.
  The proofs below check reordering, introductions, the independent processed
  query, and the recursive proof. Neither the JSON decoder nor C++ is verified.
  Source query SHA-256: {source_hash}
  Introduction list SHA-256: {steps_hash}
  Processed query SHA-256: {query_hash}
  Certificate SHA-256: {proof_hash}
\\<close>

definition imported_source_query :: rat_query where
  "imported_source_query = {hol_source(replay.source)}"

definition imported_source_column_query :: rat_query where
  "imported_source_column_query = {hol_source(replay.column_source)}"

lemma imported_source_term_order:
  "satisfies_query v (embed_query imported_source_column_query) \\<longleftrightarrow>
    satisfies_query v (embed_query imported_source_query)"
  by (simp add: imported_source_query_def imported_source_column_query_def
      embed_query_def satisfies_query_def algebra_simps)

definition imported_steps :: "fixed_aux_step list" where
  "imported_steps = {steps}"

definition imported_query :: rat_query where
  "imported_query = {proof.hol_query(replay.instance.query)}"

definition imported_certificate :: certificate where
  "imported_certificate = {proof.hol_certificate(replay.certificate)}"

lemma imported_steps_match_query:
  "rat_introduce_fixed_aux_sequence imported_source_column_query imported_steps =
    Some imported_query"
  by code_simp

lemma imported_certificate_checked:
  "check_certificate imported_query imported_certificate"
  by code_simp

theorem imported_query_unsatisfiable:
  "unsatisfiable (embed_query imported_query)"
  by (rule check_certificate_sound[OF imported_certificate_checked])

lemma imported_source_certificate_checked:
  "check_after_fixed_aux_sequence imported_source_column_query
    imported_steps imported_certificate"
  by (simp add: check_after_fixed_aux_sequence_def imported_steps_match_query
      imported_certificate_checked)

theorem imported_source_equisatisfiable:
  "satisfiable (embed_query imported_query) \\<longleftrightarrow>
    satisfiable (embed_query imported_source_query)"
  using fixed_aux_sequence_satisfiable_iff[OF imported_steps_match_query]
  by (simp add: satisfiable_def imported_source_term_order)

theorem imported_source_query_unsatisfiable:
  "unsatisfiable (embed_query imported_source_query)"
proof -
  have "unsatisfiable (embed_query imported_source_column_query)"
    by (rule check_after_fixed_aux_sequence_sound[OF imported_source_certificate_checked])
  then show ?thesis
    by (simp add: unsatisfiable_def satisfiable_def imported_source_term_order)
qed

{extra_theory}end
'''


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    for name, help_text in (
        ("source", "pre-initialization source-query JSON"),
        ("steps", "proposed fixed-auxiliary introduction list JSON"),
        ("query", "independent processed-query JSON"),
        ("certificate", "native JsonWriter proof JSON"),
        ("output", "generated theory file (.thy)"),
    ):
        parser.add_argument("--" + name, required=True, type=Path, help=help_text)
    parser.add_argument("--session", action="store_true", help="also create a standalone ROOT")
    args = parser.parse_args(argv)
    try:
        inputs = (args.source, args.steps, args.query, args.certificate)
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
        parser.exit(1, f"Source import rejected: {exc}\n")
    print(f"Wrote {args.output}; build its Isabelle session to establish acceptance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
