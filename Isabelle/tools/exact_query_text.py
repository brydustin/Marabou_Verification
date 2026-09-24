#!/usr/bin/env python3
"""Write the canonical exact text (.mqx) of a captured source or plain-ReLU query.

The format's meaning is Exact_Query_Format.decode_query in Isabelle/HOL; this
untrusted exporter mirrors Exact_Query_Format.encode_query so that a captured
JSON query can be restated as bytes. Numbers are the exact rationals of the
JSON decimal tokens, written as integers or reduced fractions. Generated HOL
proves by code_simp what each file decodes to; nothing here is a premise.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
from pathlib import Path
import sys

import import_marabou_json as proof
import import_marabou_source as source

HEADER = b"marabou-exact-query-v1"
FORMATS = {"marabou-plain-relu-query-v1": True, "marabou-source-query-v1": False}
THEORY = "Imported_Marabou_Exact_Texts"

# Main-session fixtures: the explicit starting query of every native scenario.
# (scenario, JSON suffix, generated theory, starting-query constant, theorem kind)
SCENARIOS = (
    ("linear", "_source.json", "Imported_Marabou_Source_Linear", "imported_source_query", "unsat"),
    ("relu", "_source.json", "Imported_Marabou_Source_Relu", "imported_source_query", "unsat"),
    ("relu_aux", "_source.json", "Imported_Marabou_Source_Relu_Aux", "imported_source_query", "unsat"),
    ("relu_aux_active", "_source.json", "Imported_Marabou_Source_Relu_Aux_Active",
     "imported_source_query", "unsat"),
    ("relu_aux_inactive", "_source.json", "Imported_Marabou_Source_Relu_Aux_Inactive",
     "imported_source_query", "unsat"),
    ("relu_split", "_source.json", "Imported_Marabou_Source_Relu_Split", "imported_source_query", "unsat"),
    ("relu_intro", "_before_relu.json", "Imported_Marabou_Native_Relu_Intro",
     "imported_before_relu_query", "unsat"),
    ("relu_sequence", "_before_relu.json", "Imported_Marabou_Native_Relu_Sequence",
     "imported_before_relu_query", "unsat"),
    ("relu_chain", "_before_relu.json", "Imported_Marabou_Native_Relu_Chain",
     "imported_before_relu_query", "unsat"),
    ("relu_sat", "_before_relu.json", "Imported_Marabou_Native_Relu_Sat",
     "imported_before_relu_query", "sat"),
)


def print_rat(q: Fraction) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator}/{q.denominator}"


def encode(src: source.Source) -> bytes:
    """Linear statements, then bounds, then ReLUs, in their query order."""
    lines = []
    for e in src.equations:
        terms = [token for a, x in e.terms for token in (print_rat(a), f"x{x}")]
        lines.append(" ".join(["eq", *terms, "=", print_rat(e.scalar)]))
    for b in src.bounds:
        lines.append(f"{'lower' if b.kind == 'L' else 'upper'} x{b.variable} {print_rat(b.value)}")
    for x, y in src.relus:
        lines.append(f"relu x{x} x{y}")
    return HEADER + b"\n" + "".join(line + "\n" for line in lines).encode("ascii")


def load_query(obj):
    proof.require(type(obj) is dict and obj.get("format") in FORMATS, "unsupported query format")
    return source.parse_source(obj, plain_relu=FORMATS[obj["format"]])


KINDS = {b"eq": (b"=", "EQ"), b"le": (b"<=", "LE"), b"ge": (b">=", "GE")}


@dataclass(frozen=True)
class DecodedQuery:
    linear: tuple[tuple[str, tuple[tuple[Fraction, int], ...], Fraction], ...]
    bounds: tuple[proof.Bound, ...]
    relus: tuple[tuple[int, int], ...]


def _nat(cs: bytes):
    if not cs or any(c < 48 or c > 57 for c in cs):
        return None
    return int(cs)


def _unsigned(cs: bytes):
    parts = cs.split(b"/")
    if len(parts) == 2:
        n, d = _nat(parts[0]), _nat(parts[1])
        return None if n is None or d is None or d == 0 else Fraction(n, d)
    if len(parts) != 1:
        return None
    pieces = cs.split(b".")
    if len(pieces) == 1:
        n = _nat(pieces[0])
        return None if n is None else Fraction(n)
    if len(pieces) == 2:
        i, f = _nat(pieces[0]), _nat(pieces[1])
        return None if i is None or f is None else i + Fraction(f, 10 ** len(pieces[1]))
    return None


def _rat(cs: bytes):
    if cs[:1] == b"-":
        q = _unsigned(cs[1:])
        return None if q is None else -q
    return _unsigned(cs)


def _var(cs: bytes):
    return _nat(cs[1:]) if cs[:1] == b"x" else None


def decode(data: bytes):
    """Untrusted mirror of Exact_Query_Format.decode_query; None means rejected.

    Used only for early, readable rejection. Isabelle decides acceptance.
    """
    lines = data.split(b"\n")
    if lines[0] != HEADER or len(lines) < 2 or lines[-1] != b"":
        return None
    linear, bounds, relus = [], [], []
    for line in lines[1:-1]:
        tokens = line.split(b" ")
        if b"" in tokens:
            return None
        keyword, args = tokens[0], tokens[1:]
        if keyword in KINDS:
            relation, kind = KINDS[keyword]
            if len(args) < 2 or args[-2] != relation or len(args) % 2:
                return None
            terms = []
            for a, x in zip(args[:-2:2], args[1:-2:2]):
                q, v = _rat(a), _var(x)
                if q is None or v is None:
                    return None
                terms.append((q, v))
            rhs = _rat(args[-1])
            if rhs is None:
                return None
            linear.append((kind, tuple(terms), rhs))
        elif keyword in (b"lower", b"upper"):
            if len(args) != 2:
                return None
            v, q = _var(args[0]), _rat(args[1])
            if v is None or q is None:
                return None
            bounds.append(proof.Bound(v, "L" if keyword == b"lower" else "U", q))
        elif keyword == b"relu":
            if len(args) != 2:
                return None
            x, y = _var(args[0]), _var(args[1])
            if x is None or y is None:
                return None
            relus.append((x, y))
        else:
            return None
    return DecodedQuery(tuple(linear), tuple(bounds), tuple(relus))


def same_constraints(decoded: DecodedQuery, src: source.Source):
    """Mirror of Exact_Query_Format.same_constraints for a captured source."""
    captured = {("EQ", e.terms, e.scalar) for e in src.equations}
    return (set(decoded.linear) == captured and set(decoded.bounds) == set(src.bounds) and
            set(decoded.relus) == set(src.relus))


def fixture_texts(fixtures: Path):
    """Canonical texts of the captured starting queries, keyed by scenario."""
    result = {}
    for scenario, suffix, *_ in SCENARIOS:
        obj, _ = proof.load_json(fixtures / f"solver_{scenario}{suffix}")
        result[scenario] = encode(load_query(obj))
    return result


def hol_bytes(data: bytes, indent="    "):
    rows = [", ".join(str(b) for b in data[i:i + 24]) for i in range(0, len(data), 24)]
    return "[" + (",\n" + indent).join(rows) + "]"


UNSAT_TEMPLATE = """theorem {name}_unsatisfiable:
  "decode_query {name} = Some Q \\<Longrightarrow> unsatisfiable (embed_query Q)"
  using {name}_decodes {theory}.{constant}_unsatisfiable by simp
"""

SAT_TEMPLATE = """theorem {name}_model:
  "decode_query {name} = Some Q \\<Longrightarrow>
    satisfies_query (assignment_valuation {theory}.imported_assignment) (embed_query Q)"
  using {name}_decodes {theory}.{constant}_model by simp

theorem {name}_satisfiable:
  "decode_query {name} = Some Q \\<Longrightarrow> satisfiable (embed_query Q)"
  using {name}_model unfolding satisfiable_def by blast
"""

TEXT_TEMPLATE = """text \\<open>
  Bytes of tests/fixtures/marabou/solver_{scenario}.mqx
  ({size} bytes, SHA-256 {digest}).
\\<close>

definition {name} :: bytes where
  "{name} = {data}"

external_file "tests/fixtures/marabou/solver_{scenario}.mqx"

ML \\<open>
  Exact_Query_Text.check_file \\<^theory> @{{thm {name}_def}}
    "tests/fixtures/marabou/solver_{scenario}.mqx"
\\<close>

lemma {name}_decodes:
  "decode_query {name} = Some {theory}.{constant}"
  by code_simp

{conclusion}"""

THEORY_TEMPLATE = """theory {theory_name}
  imports Exact_Query_Format{imports}
begin

text \\<open>
  Generated by the untrusted exporter tools/exact_query_text.py. Each byte list
  is the exact content of a saved .mqx fixture: the build reads each declared
  file and fails unless it equals the defined bytes. The
  format's meaning is decode_query, and each decoding is proved by code_simp
  to be the explicit starting query of the named capture. The theorems below
  therefore concern the decoded bytes. The C++ solver, the capture of the
  JSON snapshot and the exporter itself are not verified or trusted.
\\<close>

{body}
end
"""


def render_theory(texts):
    parts = []
    for scenario, _, theory, constant, kind in SCENARIOS:
        name = f"solver_{scenario}_text"
        data = texts[scenario]
        template = UNSAT_TEMPLATE if kind == "unsat" else SAT_TEMPLATE
        conclusion = template.format(name=name, theory=theory, constant=constant)
        parts.append(TEXT_TEMPLATE.format(
            scenario=scenario, size=len(data), digest=hashlib.sha256(data).hexdigest(),
            name=name, data=hol_bytes(data), theory=theory, constant=constant,
            conclusion=conclusion))
    imports = "".join(f"\n    {theory}" for _, _, theory, _, _ in SCENARIOS)
    return THEORY_TEMPLATE.format(theory_name=THEORY, imports=imports, body="\n".join(parts))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", type=Path,
                        help="marabou-source-query-v1 or marabou-plain-relu-query-v1 JSON")
    parser.add_argument("--output", type=Path, help="exact text file (.mqx)")
    parser.add_argument("--fixtures", type=Path,
                        help="rewrite the solver_*.mqx fixtures from the JSON fixtures in this directory")
    parser.add_argument("--theory", type=Path, help="with --fixtures, also write the decoding theory")
    args = parser.parse_args(argv)
    try:
        if args.fixtures is not None:
            proof.require(args.query is None and args.output is None,
                          "--fixtures cannot be combined with --query/--output")
            texts = fixture_texts(args.fixtures)
            for scenario, data in texts.items():
                (args.fixtures / f"solver_{scenario}.mqx").write_bytes(data)
            if args.theory is not None:
                proof.require(args.theory.name == THEORY + ".thy", f"theory file must be {THEORY}.thy")
                args.theory.write_text(render_theory(texts), encoding="utf-8")
            print(f"Wrote {len(texts)} fixture texts.")
            return 0
        proof.require(args.query is not None and args.output is not None,
                      "give --query and --output, or --fixtures")
        proof.require(args.output.suffix == ".mqx", "output must have suffix .mqx")
        proof.require(args.output.resolve() != args.query.resolve(), "output cannot overwrite the input")
        obj, _ = proof.load_json(args.query)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_bytes(encode(load_query(obj)))
    except (proof.ImportFailure, OSError) as exc:
        parser.exit(1, f"Export rejected: {exc}\n")
    print(f"Wrote {args.output}; its meaning is decode_query of these bytes in Isabelle/HOL.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
