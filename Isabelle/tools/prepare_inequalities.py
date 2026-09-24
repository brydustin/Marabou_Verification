#!/usr/bin/env python3
"""Untrusted exact proposals for signed slacks and their opposite finite bounds.

This is a local translation, not an invocation of Marabou's private
Preprocessor::makeAllEquationsEqualities. Bounded_Inequality_Auxiliary checks
each proposal and its linear witness in HOL, then matches the captured query.
"""
from dataclasses import dataclass
from fractions import Fraction

import exact_query_text as text
import import_marabou_json as proof

FORMAT = "marabou-bounded-inequality-steps-v1"


@dataclass(frozen=True)
class Step:
    index: int
    variable: int
    cap: Fraction
    weights: tuple[Fraction, ...]


def variables(query):
    return ({x for _, terms, _ in query.linear for _, x in terms} |
            {b.variable for b in query.bounds} | {x for r in query.relus for x in r})


def rows(query):
    result = []
    for kind, terms, rhs in query.linear:
        expression = proof.Expr(-rhs, terms)
        if kind == "EQ":
            result.extend((expression, expression.scale(-1)))
        else:
            result.append(expression if kind == "LE" else expression.scale(-1))
    return result + [bound.expression() for bound in query.bounds]


def introduce(query, index, variable):
    proof.require(0 <= index < len(query.linear), "inequality index out of range")
    proof.require(variable not in variables(query), "inequality auxiliary is not fresh")
    kind, terms, rhs = query.linear[index]
    proof.require(kind in ("LE", "GE"), "selected atom is not an inequality")
    linear = list(query.linear)
    linear[index] = ("EQ", terms + ((Fraction(1), variable),), rhs)
    zero_bound = proof.Bound(variable, "L" if kind == "LE" else "U", Fraction(0))
    return text.DecodedQuery(tuple(linear), query.bounds + (zero_bound,), query.relus)


def apply_step(query, step):
    transformed = introduce(query, step.index, step.variable)
    kind = query.linear[step.index][0]
    bound = proof.Bound(step.variable, "U" if kind == "LE" else "L", step.cap)
    normalized = rows(transformed)
    proof.require(len(step.weights) == len(normalized) and all(w >= 0 for w in step.weights),
                  "invalid inequality-bound weights")
    n = max(variables(transformed), default=-1) + 1
    residual = bound.expression().vector(n)
    for row, weight in zip(normalized, step.weights):
        proof.add_scaled(residual, -weight, row.vector(n))
    proof.require(residual[0] <= 0 and not any(residual[1:]),
                  "no exact linear implication for the opposite slack bound")
    # rat_add_bound prepends. Preserve this order for subsequent witnesses.
    return text.DecodedQuery(transformed.linear, (bound,) + transformed.bounds, transformed.relus)


def prepare(query):
    """Propose one step per inequality, deriving bounds by interval arithmetic.

    The bound is weakened to include zero if the interval already contradicts
    the inequality, leaving the solver a consistent initial slack interval.
    The exact witness still justifies that weaker bound.
    """
    result, steps = query, []
    for i, (kind, terms, rhs) in enumerate(query.linear):
        if kind == "EQ":
            continue
        variable = max(variables(result), default=-1) + 1
        proof.require(variable < 4096, "too many variables after inequality introductions")
        intermediate = introduce(result, i, variable)
        normalized = rows(intermediate)
        weights = [Fraction(0)] * len(normalized)
        offset = sum(2 if k == "EQ" else 1 for k, _, _ in intermediate.linear[:i])
        weights[offset + (kind == "GE")] = Fraction(1)
        bounds_offset = sum(2 if k == "EQ" else 1 for k, _, _ in intermediate.linear)
        bound_map = {(b.variable, b.kind): (j, b.value) for j, b in enumerate(intermediate.bounds)}
        extreme = Fraction(0)
        for coefficient, x in terms:
            if coefficient == 0:
                continue
            use_lower = (coefficient > 0) == (kind == "LE")
            key = (x, "L" if use_lower else "U")
            proof.require(key in bound_map, f"missing finite bound for x{x}")
            j, value = bound_map[key]
            extreme += coefficient * value
            weights[bounds_offset + j] += abs(coefficient)
        cap = max(Fraction(0), rhs - extreme) if kind == "LE" else min(Fraction(0), rhs - extreme)
        step = Step(i, variable, cap, tuple(weights))
        result = apply_step(result, step)
        steps.append(step)
    return result, tuple(steps)


def encode(query):
    """Equality-only file supplied to the existing native reader."""
    proof.require(all(kind == "EQ" for kind, _, _ in query.linear), "inequalities remain after preparation")
    lines = []
    for _, terms, rhs in query.linear:
        tokens = [t for a, x in terms for t in (text.print_rat(a), f"x{x}")]
        lines.append(" ".join(["eq", *tokens, "=", text.print_rat(rhs)]))
    for b in query.bounds:
        lines.append(f"{'lower' if b.kind == 'L' else 'upper'} x{b.variable} {text.print_rat(b.value)}")
    lines.extend(f"relu x{x} x{y}" for x, y in query.relus)
    return text.HEADER + b"\n" + "".join(line + "\n" for line in lines).encode("ascii")


def record(steps):
    return {"format": FORMAT, "steps": [
        {"index": s.index, "variable": s.variable, "cap": text.print_rat(s.cap),
         "weights": [text.print_rat(w) for w in s.weights]} for s in steps]}


def parse_fraction(value):
    proof.require(type(value) is str and 0 < len(value) <= 128 and value.isascii(),
                  "invalid exact rational in inequality evidence")
    q = text._rat(value.encode("ascii"))
    proof.require(q is not None, "invalid exact rational in inequality evidence")
    return q


def parse_record(obj):
    proof.fields(obj, ("format", "steps"))
    proof.require(obj["format"] == FORMAT, "unsupported inequality evidence format")
    raw = proof.array(obj["steps"])
    proof.require(len(raw) <= 512, "too many inequality steps")
    steps = []
    for item in raw:
        proof.fields(item, ("index", "variable", "cap", "weights"))
        weights = proof.array(item["weights"])
        proof.require(len(weights) <= 10000, "too many inequality weights")
        steps.append(Step(proof.index(item["index"], 512), proof.index(item["variable"], 4096),
                          parse_fraction(item["cap"]), tuple(parse_fraction(w) for w in weights)))
    return tuple(steps)


def replay(query, steps):
    result = query
    for step in steps:
        result = apply_step(result, step)
    proof.require(all(kind == "EQ" for kind, _, _ in result.linear), "inequalities remain after preparation")
    return result


def hol_steps(steps):
    return proof.hol_list(
        f"Bounded_Inequality_Step {s.index} {s.variable} {proof.hol_rat(s.cap)} " +
        proof.hol_list(proof.hol_rat(w) for w in s.weights) for s in steps)
