#!/usr/bin/env python3
"""Reconstruct a candidate HOL certificate from Marabou JsonWriter evidence.

Supported: finite homogeneous tableaux, finite bounds, auxiliary-form ReLUs,
binary ReLU splits, row-combination and conflicting-bound leaves, and ReLU
input-to-output and input-lower-to-auxiliary-upper ReLU lemmas with ground or
tableau-explained premises. Auxiliary equations need exact linear witnesses.
This untrusted adapter emits data and a code_simp proof obligation. Acceptance
is established only when Isabelle builds the emitted theory.
"""
from __future__ import annotations

import argparse
from dataclasses import dataclass
from decimal import Decimal
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re
import sys


class ImportFailure(ValueError):
    pass


MAX_BYTES = 4_000_000
MAX_VARS = 256
MAX_ROWS = 512
MAX_DEPTH = 64
MAX_NODES = 4095
ZERO = Fraction(0)
ONE = Fraction(1)


def require(condition, message):
    if not condition:
        raise ImportFailure(message)


def exact_int(token):
    require(len(token) <= 128, "integer token too long")
    return int(token)


def exact_decimal(token):
    require(len(token) <= 128, "decimal token too long")
    value = Decimal(token)
    require(value.is_finite() and abs(value.as_tuple().exponent) <= 256,
            "nonfinite number or excessive decimal exponent")
    return Fraction(value)


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, f"duplicate JSON key: {key}")
        result[key] = value
    return result


def reject_constant(token):
    raise ImportFailure(f"nonfinite JSON constant: {token}")


def load_json(path):
    # Bound reads before parsing, including files that grow after stat().
    with Path(path).open("rb") as stream:
        data = stream.read(MAX_BYTES + 1)
    require(len(data) <= MAX_BYTES, "JSON file exceeds size limit")
    try:
        value = json.loads(data.decode("utf-8"), parse_int=exact_int,
                           parse_float=exact_decimal, parse_constant=reject_constant,
                           object_pairs_hook=unique_object)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise ImportFailure(f"invalid JSON: {exc}") from exc
    return value, hashlib.sha256(data).hexdigest()


def fields(obj, required, optional=()):
    require(type(obj) is dict, "expected a JSON object")
    require(set(required) <= obj.keys(), f"missing fields: {set(required) - obj.keys()}")
    require(obj.keys() <= set(required) | set(optional), "unknown or unsupported fields")


def array(value):
    require(type(value) is list, "expected a JSON array")
    return value


def index(value, size):
    require(type(value) is int and 0 <= value < size, "invalid or out-of-range index")
    return value


def rational(value):
    # In particular reject bool, strings, Python floats, NaN and infinities.
    require(type(value) in (int, Fraction), "expected an exact JSON number")
    return Fraction(value)


@dataclass(frozen=True)
class Expr:
    constant: Fraction
    terms: tuple[tuple[Fraction, int], ...]

    def vector(self, n):
        result = [self.constant] + [ZERO] * n
        for coefficient, variable in self.terms:
            result[variable + 1] += coefficient
        return result

    def scale(self, coefficient):
        return Expr(coefficient * self.constant,
                    tuple((coefficient * a, x) for a, x in self.terms))


@dataclass(frozen=True)
class Bound:
    variable: int
    kind: str
    value: Fraction

    def expression(self):
        if self.kind == "L":
            return Expr(self.value, ((-ONE, self.variable),))
        return Expr(-self.value, ((ONE, self.variable),))


@dataclass(frozen=True)
class Query:
    equations: tuple[Expr, ...]
    bounds: tuple[Bound, ...]
    relus: tuple[tuple[int, int], ...]

    def rows(self):
        result = []
        for equation in self.equations:
            result.extend((equation, equation.scale(-ONE)))
        return result + [b.expression() for b in self.bounds]

    def split(self, x, y, active):
        equation = Expr(ZERO, ((ONE, y), (-ONE, x)) if active else ((ONE, y),))
        return Query((equation,) + self.equations,
                     (Bound(x, "L" if active else "U", ZERO),) + self.bounds,
                     tuple(r for r in self.relus if r != (x, y)))

    def add_bound(self, bound):
        return Query(self.equations, (bound,) + self.bounds, self.relus)


@dataclass(frozen=True)
class Instance:
    n: int
    query: Query
    relu_metadata: tuple[tuple[int, int, int, int], ...]


def sparse_entries(value, size):
    result, seen = [], set()
    for entry in array(value):
        fields(entry, ("var", "val"))
        i = index(entry["var"], size)
        require(i not in seen, "duplicate sparse index")
        seen.add(i)
        result.append((rational(entry["val"]), i))
    return tuple(result)


HEADER = ("tableau", "upperBounds", "lowerBounds", "constraints")


def parse_instance(obj, with_proof=False):
    fields(obj, HEADER + (("proof",) if with_proof else ()))
    lower, upper = array(obj["lowerBounds"]), array(obj["upperBounds"])
    n = len(lower)
    require(0 < n <= MAX_VARS and len(upper) == n, "invalid bound array dimensions")
    rows = array(obj["tableau"])
    require(0 < len(rows) <= MAX_ROWS, "invalid tableau dimensions")
    equations = tuple(Expr(ZERO, sparse_entries(row, n)) for row in rows)
    bounds = tuple(b for i in range(n) for b in
                   (Bound(i, "L", rational(lower[i])), Bound(i, "U", rational(upper[i]))))
    relus = []
    for constraint in array(obj["constraints"]):
        fields(constraint, ("constraintType", "vars"))
        require(type(constraint["constraintType"]) is int and constraint["constraintType"] == 0,
                "only ReLU constraintType 0 is supported")
        variables = tuple(index(x, n) for x in array(constraint["vars"]))
        require(len(variables) == 4 and len(set(variables)) == 4,
                "expected distinct ReLU variables [b, f, aux, tableauAux]")
        require(variables[:2] not in [r[:2] for r in relus], "duplicate ReLU metadata")
        relus.append(variables)
    return Instance(n, Query(equations, bounds, tuple(r[:2] for r in relus)), tuple(relus))


@dataclass(frozen=True)
class UpperLemma:
    x: int
    y: int
    bound: Fraction
    explanation: tuple[tuple[Fraction, int], ...]


@dataclass(frozen=True)
class AuxUpperLemma:
    x: int
    y: int
    auxiliary: int
    bound: Fraction
    explanation: tuple[tuple[Fraction, int], ...]


def parse_lemma(obj, instance):
    # JsonWriter::writePLCLemmas: a single cause and a single explanation.
    fields(obj, ("affVar", "affBound", "bound", "causVar", "causBound", "constraint", "expl"))
    require(type(obj["constraint"]) is int and obj["constraint"] == 0 and
            obj["affBound"] == "U" and obj["causBound"] in ("L", "U"),
            "unsupported PLC lemma: expected ReLU output/auxiliary upper propagation")
    x, affected = index(obj["causVar"], instance.n), index(obj["affVar"], instance.n)
    explanation = sparse_entries(obj["expl"], len(instance.query.equations))
    if obj["causBound"] == "U":
        require((x, affected) in instance.query.relus,
                "PLC lemma variables do not name an input/output ReLU pair")
        return UpperLemma(x, affected, rational(obj["bound"]), explanation)
    matches = [(b, f, aux) for b, f, aux, _ in instance.relu_metadata
               if b == x and aux == affected]
    require(len(matches) == 1, "PLC lemma variables do not name a unique input/auxiliary ReLU pair")
    b, f, aux = matches[0]
    return AuxUpperLemma(b, f, aux, rational(obj["bound"]), explanation)


@dataclass(frozen=True)
class Node:
    split: tuple[Bound, ...]
    children: tuple[Node, ...] = ()
    variable: int | None = None
    combination: tuple[tuple[Fraction, int], ...] | None = None
    lemmas: tuple[UpperLemma | AuxUpperLemma, ...] = ()


def parse_node(obj, instance, depth=0, counter=None):
    if counter is None:
        counter = [0]
    fields(obj, (), ("split", "lemmas", "children", "contradiction"))
    lemma_objects = array(obj.get("lemmas", []))
    # Each lemma needs at most two unary nodes: linear premise, then ReLU rule.
    # Auxiliary equations carry two witnesses within that ReLU node.
    # Conservatively charge both even if an explicit premise needs no addition.
    counter[0] += 1 + 2 * len(lemma_objects)
    depth += 2 * len(lemma_objects)
    require(depth <= MAX_DEPTH and counter[0] <= MAX_NODES, "proof tree exceeds limits")
    lemmas = tuple(parse_lemma(lemma, instance) for lemma in lemma_objects)
    split = []
    for item in array(obj.get("split", [])):
        fields(item, ("var", "val", "bound"))
        require(item["bound"] in ("L", "U"), "unknown bound direction")
        split.append(Bound(index(item["var"], instance.n), item["bound"], rational(item["val"])))
    require(("children" in obj) != ("contradiction" in obj),
            "each node needs exactly one of children or contradiction")
    if "children" in obj:
        children = array(obj["children"])
        require(len(children) == 2, "a split must have exactly two children")
        return Node(tuple(split), tuple(parse_node(c, instance, depth + 1, counter) for c in children),
                    lemmas=lemmas)
    contradiction = array(obj["contradiction"])
    require(contradiction, "missing leaf evidence")
    if len(contradiction) == 1 and type(contradiction[0]) is int:
        return Node(tuple(split), variable=index(contradiction[0], instance.n), lemmas=lemmas)
    return Node(tuple(split), combination=sparse_entries(contradiction, len(instance.query.equations)),
                lemmas=lemmas)


def add_scaled(target, scale, source):
    require(len(target) == len(source), "internal vector dimension mismatch")
    for i, value in enumerate(source):
        target[i] += scale * value


class EqualitySpan:
    """Untrusted exact Gaussian elimination, retaining row-combination witnesses."""
    def __init__(self, query, n):
        self.query, self.n, self.basis = query, n, []
        for i, equation in enumerate(query.equations):
            vector = equation.vector(n)
            witness = [ZERO] * len(query.equations)
            witness[i] = ONE
            for pivot, row, proof in self.basis:
                multiplier = vector[pivot]
                add_scaled(vector, -multiplier, row)
                add_scaled(witness, -multiplier, proof)
            pivot = next((j for j, c in enumerate(vector) if c), None)
            if pivot is not None:
                divisor = vector[pivot]
                self.basis.append((pivot, [x / divisor for x in vector],
                                   [x / divisor for x in witness]))
                self.basis.sort(key=lambda entry: entry[0])

    def express(self, vector):
        vector = list(vector)
        witness = [ZERO] * len(self.query.equations)
        for pivot, row, proof in self.basis:
            multiplier = vector[pivot]
            add_scaled(vector, -multiplier, row)
            add_scaled(witness, multiplier, proof)
        if any(vector):
            return None
        weights = [ZERO] * len(self.query.rows())
        for i, a in enumerate(witness):
            weights[2 * i + (a < 0)] = abs(a)
        return weights

    def bound(self, bound):
        for i, candidate in enumerate(self.query.bounds):
            if candidate == bound:
                weights = [ZERO] * len(self.query.rows())
                weights[2 * len(self.query.equations) + i] = ONE
                return weights
        return self.inequality(bound.expression())

    def inequality(self, expression):
        target = expression.vector(self.n)
        weights = self.express(target)
        if weights is not None:
            return weights
        # Auxiliary phase bounds commonly follow from equalities and one
        # ground bound, e.g. aux = -tableauAux and tableauAux >= 0.
        for i, candidate in enumerate(self.query.bounds):
            residual = list(target)
            add_scaled(residual, -ONE, candidate.expression().vector(self.n))
            weights = self.express(residual)
            if weights is not None:
                weights[2 * len(self.query.equations) + i] += ONE
                return weights
        raise ImportFailure(f"cannot reconstruct inequality {expression} from the canonical query")


def weighted_vector(query, n, weights):
    rows = query.rows()
    require(len(rows) == len(weights) and all(w >= 0 for w in weights), "invalid reconstructed weights")
    total = [ZERO] * (n + 1)
    for w, row in zip(weights, rows):
        add_scaled(total, w, row.vector(n))
    return total


def validate_weights(query, n, weights):
    total = weighted_vector(query, n, weights)
    require(total[0] > 0 and not any(total[1:]), "leaf has no exact constant contradiction")


def validate_implication(query, n, bound, weights):
    validate_expression_implication(query, n, bound.expression(), weights)


def validate_expression_implication(query, n, expression, weights):
    residual = expression.vector(n)
    add_scaled(residual, -ONE, weighted_vector(query, n, weights))
    require(residual[0] <= 0 and not any(residual[1:]),
            "no exact linear implication for the proposed expression")


@dataclass(frozen=True)
class Leaf:
    weights: tuple[Fraction, ...]


@dataclass(frozen=True)
class Split:
    x: int
    y: int
    active: Leaf | Split | ReluUpper | ReluAuxUpper | LinearBound
    inactive: Leaf | Split | ReluUpper | ReluAuxUpper | LinearBound


@dataclass(frozen=True)
class ReluUpper:
    x: int
    y: int
    input_upper: Fraction
    output_upper: Fraction
    child: Leaf | Split | ReluUpper | ReluAuxUpper | LinearBound


@dataclass(frozen=True)
class ReluAuxUpper:
    x: int
    y: int
    auxiliary: int
    input_lower: Fraction
    auxiliary_upper: Fraction
    positive: tuple[Fraction, ...]
    negative: tuple[Fraction, ...]
    child: Leaf | Split | ReluUpper | ReluAuxUpper | LinearBound


@dataclass(frozen=True)
class LinearBound:
    bound: Bound
    weights: tuple[Fraction, ...]
    child: Leaf | Split | ReluUpper | ReluAuxUpper | LinearBound


def update_bounds(bounds, additions):
    result = dict(bounds)
    for bound in additions:
        key = (bound.variable, bound.kind)
        old = result[key]
        if (bound.kind == "L" and bound.value > old.value) or (
                bound.kind == "U" and bound.value < old.value):
            result[key] = bound
    return result


def reconstruct_leaf(instance, query, node, bounds):
    span = EqualitySpan(query, instance.n)
    weights = [ZERO] * len(query.rows())
    if node.variable is not None:
        for kind in ("L", "U"):
            add_scaled(weights, ONE, span.bound(bounds[node.variable, kind]))
    else:
        require(node.combination is not None, "missing row combination")
        combined = [ZERO] * (instance.n + 1)
        offset = len(query.equations) - len(instance.query.equations)
        for a, i in node.combination:
            add_scaled(combined, a, instance.query.equations[i].vector(instance.n))
            # Negate the native equality combination, then add its upper-bound proof.
            weights[2 * (offset + i) + (a > 0)] += abs(a)
        for variable, a in enumerate(combined[1:]):
            if a:
                add_scaled(weights, abs(a), span.bound(bounds[variable, "U" if a > 0 else "L"]))
    validate_weights(query, instance.n, weights)
    return Leaf(tuple(weights))


def reconstruct_premise(instance, query, lemma, bounds, kind):
    source = bounds[lemma.x, kind]
    if not lemma.explanation and source in query.bounds:
        return source, None
    span = EqualitySpan(query, instance.n)
    if not lemma.explanation:
        # A native branch bound may follow from the canonical phase equality.
        weights = span.bound(source)
    else:
        weights = [ZERO] * len(query.rows())
        combined = [ZERO] * (instance.n + 1)
        combined[lemma.x + 1] = ONE
        offset = len(query.equations) - len(instance.query.equations)
        # U targets x-u; L targets l-x, reversing the equality signs.
        direction = ONE if kind == "U" else -ONE
        for a, i in lemma.explanation:
            # UNSATCertificateUtils::getExplanationRowCombination(var,...):
            # c = e_var + w^T A, so c*x = x_var on the original equalities.
            add_scaled(combined, a, instance.query.equations[i].vector(instance.n))
            coefficient = -direction * a
            weights[2 * (offset + i) + (coefficient < 0)] += abs(a)
        value = ZERO
        for variable, a in enumerate(combined[1:]):
            if a:
                ground_kind = kind if a > 0 else ("L" if kind == "U" else "U")
                ground = bounds[variable, ground_kind]
                value += a * ground.value
                add_scaled(weights, abs(a), span.bound(ground))
        source = Bound(lemma.x, kind, value)
    validate_implication(query, instance.n, source, weights)
    return source, tuple(weights)


def reconstruct_auxiliary_equation(instance, query, lemma):
    # Metadata names a candidate auxiliary; it does not establish this equation.
    expression = Expr(ZERO, ((ONE, lemma.y), (-ONE, lemma.x), (-ONE, lemma.auxiliary)))
    span = EqualitySpan(query, instance.n)
    positive = span.inequality(expression)
    negative = span.inequality(expression.scale(-ONE))
    validate_expression_implication(query, instance.n, expression, positive)
    validate_expression_implication(query, instance.n, expression.scale(-ONE), negative)
    return tuple(positive), tuple(negative)


def reconstruct_tree(instance, query, node, bounds):
    steps = []
    for lemma in node.lemmas:
        require((lemma.x, lemma.y) in query.relus, "PLC lemma selects a removed ReLU")
        auxiliary = isinstance(lemma, AuxUpperLemma)
        source, weights = reconstruct_premise(instance, query, lemma, bounds, "L" if auxiliary else "U")
        threshold = max(ZERO, -source.value if auxiliary else source.value)
        require(threshold <= lemma.bound, "PLC conclusion is too strong in exact arithmetic")
        if weights is not None:
            query = query.add_bound(source)
        equation = reconstruct_auxiliary_equation(instance, query, lemma) if auxiliary else None
        steps.append((lemma, source, weights, equation))
        # Only the PLC conclusion updates Marabou's ground-bound state.
        # The checked linear premise is local HOL evidence, not a ground update.
        bound = Bound(lemma.auxiliary if auxiliary else lemma.y, "U", lemma.bound)
        query = query.add_bound(bound)
        bounds = update_bounds(bounds, (bound,))
    cert = reconstruct_node_body(instance, query, node, bounds)
    for lemma, source, weights, equation in reversed(steps):
        if equation is None:
            cert = ReluUpper(lemma.x, lemma.y, source.value, lemma.bound, cert)
        else:
            cert = ReluAuxUpper(lemma.x, lemma.y, lemma.auxiliary, source.value, lemma.bound,
                                equation[0], equation[1], cert)
        if weights is not None:
            cert = LinearBound(source, weights, cert)
    return cert


def reconstruct_node_body(instance, query, node, bounds):
    if not node.children:
        return reconstruct_leaf(instance, query, node, bounds)
    matches = []
    for x, y, aux, _ in instance.relu_metadata:
        if (x, y) not in query.relus:
            continue
        active = {Bound(x, "L", ZERO), Bound(aux, "U", ZERO)}
        inactive = {Bound(x, "U", ZERO), Bound(y, "U", ZERO)}
        for a, b in ((0, 1), (1, 0)):
            if (len(node.children[a].split) == len(node.children[b].split) == 2 and
                    set(node.children[a].split) == active and set(node.children[b].split) == inactive):
                matches.append((x, y, node.children[a], node.children[b]))
    require(len(matches) == 1, "children must cover both phases of one remaining ReLU")
    x, y, active, inactive = matches[0]
    return Split(x, y,
                 reconstruct_tree(instance, query.split(x, y, True), active,
                                  update_bounds(bounds, active.split)),
                 reconstruct_tree(instance, query.split(x, y, False), inactive,
                                  update_bounds(bounds, inactive.split)))


def reconstruct(expected, certificate):
    instance = parse_instance(expected)
    require(parse_instance(certificate, with_proof=True) == instance,
            "certificate header does not match the independently supplied processed query")
    node = parse_node(certificate["proof"], instance)
    require(not node.split, "root split would add unjustified assumptions")
    bounds = {(b.variable, b.kind): b for b in instance.query.bounds}
    return instance, reconstruct_tree(instance, instance.query, node, bounds)


def hol_rat(value):
    if value.denominator == 1:
        return str(value.numerator) if value >= 0 else f"({value.numerator})"
    return f"({value.numerator} / {value.denominator})"


def hol_list(values):
    return "[" + ", ".join(values) + "]"


def hol_expr(expr):
    terms = hol_list(f"({hol_rat(a)}, {x})" for a, x in expr.terms)
    return f"(RatExpr {hol_rat(expr.constant)} {terms})"


def hol_bound(bound):
    return f"{'RatLower' if bound.kind == 'L' else 'RatUpper'} {bound.variable} {hol_rat(bound.value)}"


def hol_query(query):
    equations = hol_list(f"RatEq {hol_expr(e)} 0" for e in query.equations)
    bounds = hol_list(hol_bound(b) for b in query.bounds)
    relus = hol_list(f"ReLU {x} {y}" for x, y in query.relus)
    return ("\\<lparr>rat_linear_atoms = " + equations + ",\n"
            "     rat_query_bounds = " + bounds + ",\n"
            "     rat_relu_atoms = " + relus + "\\<rparr>")


def hol_certificate(cert, indent="    "):
    if isinstance(cert, Leaf):
        return "Linear_Unsat " + hol_list(hol_rat(w) for w in cert.weights)
    if isinstance(cert, LinearBound):
        return (f"Linear_Bound ({hol_bound(cert.bound)}) " +
                hol_list(hol_rat(w) for w in cert.weights) +
                f"\n{indent}(" + hol_certificate(cert.child, indent + "  ") + ")")
    if isinstance(cert, ReluUpper):
        return (f"Relu_Upper {cert.x} {cert.y} {hol_rat(cert.input_upper)} {hol_rat(cert.output_upper)}"
                f"\n{indent}(" + hol_certificate(cert.child, indent + "  ") + ")")
    if isinstance(cert, ReluAuxUpper):
        return (f"Relu_Aux_Upper {cert.x} {cert.y} {cert.auxiliary} "
                f"{hol_rat(cert.input_lower)} {hol_rat(cert.auxiliary_upper)} " +
                hol_list(hol_rat(w) for w in cert.positive) + "\n" + indent +
                hol_list(hol_rat(w) for w in cert.negative) +
                f"\n{indent}(" + hol_certificate(cert.child, indent + "  ") + ")")
    return (f"Relu_Split {cert.x} {cert.y}\n{indent}(" + hol_certificate(cert.active, indent + "  ") +
            f")\n{indent}(" + hol_certificate(cert.inactive, indent + "  ") + ")")


def render_theory(name, instance, cert, query_hash, proof_hash):
    require(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is not None, "invalid theory name")
    require(all(re.fullmatch(r"[0-9a-f]{64}", h) for h in (query_hash, proof_hash)), "invalid digest")
    return f'''theory {name}
  imports "Marabou_Verification.Rational_Proof_Trees"
begin

text \\<open>
  Generated by the untrusted Marabou JSON adapter. All numbers below denote
  exact rationals decoded from the serialized decimal tokens. This theorem
  concerns this explicit processed query, not an earlier neural-network input.
  Expected query SHA-256: {query_hash}
  Certificate SHA-256: {proof_hash}
\\<close>

definition imported_query :: rat_query where
  "imported_query = {hol_query(instance.query)}"

definition imported_certificate :: certificate where
  "imported_certificate = {hol_certificate(cert)}"

lemma imported_certificate_checked:
  "check_certificate imported_query imported_certificate"
  by code_simp

theorem imported_query_unsatisfiable:
  "unsatisfiable (embed_query imported_query)"
  by (rule check_certificate_sound[OF imported_certificate_checked])

end
'''


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--query", required=True, type=Path,
                        help="independently supplied processed-query JSON (no proof field)")
    parser.add_argument("--certificate", required=True, type=Path, help="upstream JsonWriter JSON")
    parser.add_argument("--output", required=True, type=Path, help="generated theory file (.thy)")
    parser.add_argument("--session", action="store_true",
                        help="also create a ROOT extending Marabou_Verification in the output directory")
    args = parser.parse_args(argv)
    try:
        require(args.output.suffix == ".thy", "output must have suffix .thy")
        require(args.output.resolve() not in (args.query.resolve(), args.certificate.resolve()),
                "output cannot overwrite an input")
        root = args.output.parent / "ROOT"
        require(not args.session or not root.exists(), "refusing to replace an existing ROOT")
        expected, query_hash = load_json(args.query)
        evidence, proof_hash = load_json(args.certificate)
        instance, cert = reconstruct(expected, evidence)
        theory = render_theory(args.output.stem, instance, cert, query_hash, proof_hash)
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(theory, encoding="utf-8")
        if args.session:
            root.write_text(f'session Marabou_Import_Replay = Marabou_Verification +\n'
                            f'  options [document = false, quick_and_dirty = false]\n'
                            f'  theories {args.output.stem}\n', encoding="utf-8")
    except (ImportFailure, OSError, RecursionError) as exc:
        parser.exit(1, f"Import rejected: {exc}\n")
    print(f"Wrote {args.output}; build its Isabelle session to establish acceptance.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
