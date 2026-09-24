#!/usr/bin/env python3
"""Untrusted reconstruction for runs with Marabou's native preprocessing.

For an exact query file whose native run enabled Preprocessor::preprocess,
this adapter proposes the HOL chain

    file query --slack steps--> --ReLU auxiliary steps--> S2
      --checked facts and projection (Preprocessing_Projection)--> P
      --tableau steps--> processed query --native certificate--> UNSAT.

P is the preprocessed query captured from the run. If native preprocessing
itself found the query infeasible (it then produces no proof), P is instead a
single pair of crossing bounds that the facts derive exactly. For SAT, the
native solution of the input variables is checked directly against the file
query. The facts mirror the native tightening rules (processEquations,
processConstraints) in exact arithmetic. Isabelle rechecks every step; a
wrong proposal can only make the build fail.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
import re

import exact_query_text as text
import import_marabou_assignment as assignment
import import_marabou_json as proof
import import_marabou_source as source

MAP_FORMAT = "marabou-preprocessing-map-v1"
ZERO, ONE = Fraction(0), Fraction(1)
MAX_ROUNDS = 40
MAX_FACTS = 400


class Lin:
    """Sparse exact affine form: constant + sum of coefficient * variable."""
    __slots__ = ("c", "t")

    def __init__(self, c=ZERO, t=None):
        self.c = Fraction(c)
        self.t = {k: Fraction(v) for k, v in (t or {}).items() if v}

    def plus(self, other, k=ONE):
        t = dict(self.t)
        for x, a in other.t.items():
            t[x] = t.get(x, ZERO) + k * a
        return Lin(self.c + k * other.c, t)

    def scale(self, k):
        return Lin(k * self.c, {x: k * a for x, a in self.t.items()})


def terms_lin(terms, constant=ZERO):
    result = Lin(constant)
    for a, x in terms:
        result = result.plus(Lin(ZERO, {x: Fraction(a)}))
    return result


@dataclass(frozen=True)
class Atom:
    kind: str                                 # "EQ", "LE" or "GE"
    terms: tuple[tuple[Fraction, int], ...]   # RatExpr 0 terms
    rhs: Fraction


@dataclass(frozen=True)
class HQuery:
    """Mirror of rat_query, with the same atom and bound order."""
    linear: tuple[Atom, ...]
    bounds: tuple[proof.Bound, ...]
    relus: tuple[tuple[int, int], ...]

    def variables(self):
        return ({x for a in self.linear for _, x in a.terms} | {b.variable for b in self.bounds} |
                {v for r in self.relus for v in r})


def bound_row(b):
    return Lin(b.value, {b.variable: -ONE}) if b.kind == "L" else Lin(-b.value, {b.variable: ONE})


def normalize(q):
    """normalize_query: linear rows in atom order, then one row per bound."""
    rows = []
    for atom in q.linear:
        e = terms_lin(atom.terms, -atom.rhs)
        rows.extend((e, e.scale(-ONE)) if atom.kind == "EQ" else
                    (e,) if atom.kind == "LE" else (e.scale(-ONE),))
    return rows + [bound_row(b) for b in q.bounds]


def implies(q, target, weights):
    """check_linear_implication, for early rejection only."""
    rows = normalize(q)
    if len(weights) != len(rows) or any(w < 0 for w in weights):
        return False
    residual = target
    for w, row in zip(weights, rows):
        if w:
            residual = residual.plus(row, -w)
    return residual.c <= 0 and not residual.t


def hull(q, x, y):
    """relu_hull_query: y >= 0 and y - x >= 0 in front of the atoms."""
    return replace(q, linear=(Atom("GE", ((ONE, y),), ZERO), Atom("GE", ((ONE, y), (-ONE, x)), ZERO))
                   + q.linear)


# ---- The checked introductions and facts, as HOL computes them ----

def introduce_inequality(q, i, s):
    proof.require(i < len(q.linear) and s not in q.variables(), "invalid slack introduction")
    atom = q.linear[i]
    proof.require(atom.kind in ("LE", "GE"), "slack introduction selects an equality")
    linear = list(q.linear)
    linear[i] = Atom("EQ", atom.terms + ((ONE, s),), atom.rhs)
    bound = proof.Bound(s, "L" if atom.kind == "LE" else "U", ZERO)
    return HQuery(tuple(linear), q.bounds + (bound,), q.relus)


def introduce_relu_aux(q, x, y, a, lower):
    proof.require((x, y) in q.relus and a not in q.variables(), "invalid ReLU auxiliary introduction")
    proof.require(lower is None or proof.Bound(x, "L", lower) in q.bounds, "missing ReLU input bound")
    atom = Atom("EQ", ((ONE, y), (-ONE, x), (-ONE, a)), ZERO)
    bounds = (proof.Bound(a, "L", ZERO),) + (() if lower is None else
                                             (proof.Bound(a, "U", max(ZERO, -lower)),))
    return HQuery(q.linear + (atom,), q.bounds + bounds, q.relus)


@dataclass(frozen=True)
class Fact:
    kind: str       # Bound, Hull, Phase_Active, Phase_Inactive, Relu_Upper, Relu_Aux_Upper,
    args: tuple     # Relu_Aux_Lower_Output_Upper; arguments in HOL constructor order


def active_phase_bound(x, y, b):
    return b.kind == "L" and ((b.variable == x and b.value >= 0) or (b.variable == y and b.value > 0))


def inactive_phase_bound(x, y, b):
    return b.kind == "U" and b.variable in (x, y) and b.value <= 0


def apply_fact(q, fact):
    k, a = fact.kind, fact.args
    if k == "Bound":
        b, ws = a
        proof.require(implies(q, bound_row(b), ws), "unjustified bound fact")
        return replace(q, bounds=(b,) + q.bounds)
    if k == "Hull":
        x, y = a
        proof.require((x, y) in q.relus, "hull fact for an absent ReLU")
        return hull(q, x, y)
    if k in ("Phase_Active", "Phase_Inactive"):
        x, y, b, ws = a
        active = k == "Phase_Active"
        proof.require((x, y) in q.relus and (active_phase_bound if active else inactive_phase_bound)(x, y, b)
                      and implies(hull(q, x, y), bound_row(b), ws), "unjustified phase fact")
        atom = Atom("EQ", ((ONE, y), (-ONE, x)) if active else ((ONE, y),), ZERO)
        return HQuery((atom,) + q.linear, (proof.Bound(x, "L" if active else "U", ZERO),) + q.bounds, q.relus)
    if k == "Relu_Upper":
        x, y, u, b = a
        proof.require((x, y) in q.relus and proof.Bound(x, "U", u) in q.bounds and max(ZERO, u) <= b,
                      "unjustified ReLU upper fact")
        return replace(q, bounds=(proof.Bound(y, "U", b),) + q.bounds)
    if k in ("Relu_Aux_Upper", "Relu_Aux_Lower_Output_Upper"):
        x, y, aux, l, u, pos, neg = a
        expr = terms_lin(((ONE, y), (-ONE, x), (-ONE, aux)))
        premise = proof.Bound(x if k == "Relu_Aux_Upper" else aux, "L", l)
        ok = ((x, y) in q.relus and premise in q.bounds and implies(q, expr, pos) and
              implies(q, expr.scale(-ONE), neg))
        if k == "Relu_Aux_Upper":
            proof.require(ok and max(ZERO, -l) <= u, "unjustified ReLU auxiliary fact")
            return replace(q, bounds=(proof.Bound(aux, "U", u),) + q.bounds)
        proof.require(ok and l > 0 and u >= 0, "unjustified ReLU auxiliary-lower fact")
        return replace(q, bounds=(proof.Bound(y, "U", u),) + q.bounds)
    raise proof.ImportFailure("unknown fact")


# ---- Exact equality span with fixed variables, retaining row witnesses ----

class Span:
    """Equalities of q: its EQ atoms, and every variable whose tightest lower and
    upper bounds are equal. Each generator carries (positive row, negative row)."""

    def __init__(self, q):
        self.q, self.rows = q, normalize(q)
        generators, index = [], 0
        for atom in q.linear:
            if atom.kind == "EQ":
                generators.append((self.rows[index], index, index + 1))
                index += 2
            else:
                index += 1
        tight = tightest(q)
        for x in sorted({b.variable for b in q.bounds}):
            low, up = tight.get((x, "L")), tight.get((x, "U"))
            if low and up and low[0].value == up[0].value:
                generators.append((bound_row(up[0]), up[1], low[1]))
        self.basis = []
        for row, pos, neg in generators:
            self._insert(row, pos, neg)

    def _insert(self, row, pos, neg):
        vector, witness = row, {(pos, neg): ONE}
        for pivot, brow, bwit in self.basis:
            coefficient = coeff(vector, pivot)
            if coefficient:
                vector = vector.plus(brow, -coefficient)
                witness = add_witness(witness, bwit, -coefficient)
        pivot = first_key(vector)
        if pivot is not None:
            divisor = coeff(vector, pivot)
            self.basis.append((pivot, vector.scale(ONE / divisor),
                               {k: v / divisor for k, v in witness.items()}))

    def express(self, target):
        """Weights over the rows proving target <= 0 as an equality combination,
        allowing a nonpositive remaining constant; None if impossible."""
        vector, witness = target, {}
        for pivot, brow, bwit in self.basis:
            coefficient = coeff(vector, pivot)
            if coefficient:
                vector = vector.plus(brow, -coefficient)
                witness = add_witness(witness, bwit, coefficient)
        if vector.t or vector.c > 0:
            return None
        weights = [ZERO] * len(self.rows)
        for (pos, neg), a in witness.items():
            if a > 0:
                weights[pos] += a
            elif a < 0:
                weights[neg] -= a
        return weights

    def with_one_row(self, target, candidates):
        """target <= 0 from equalities plus one inequality row among candidates."""
        weights = self.express(target)
        if weights is not None:
            return weights
        for index in candidates:
            weights = self.express(target.plus(self.rows[index], -ONE))
            if weights is not None:
                weights[index] += ONE
                return weights
        return None


def coeff(lin, key):
    return lin.c if key == "const" else lin.t.get(key, ZERO)


def first_key(lin):
    if lin.t:
        return min(lin.t)
    return "const" if lin.c else None


def add_witness(witness, other, k):
    result = dict(witness)
    for key, a in other.items():
        result[key] = result.get(key, ZERO) + k * a
    return {key: a for key, a in result.items() if a}


def tightest(q):
    """(variable, kind) -> (tightest bound, its row index in normalize(q))."""
    offset = sum(2 if a.kind == "EQ" else 1 for a in q.linear)
    result = {}
    for i, b in enumerate(q.bounds):
        key = (b.variable, b.kind)
        old = result.get(key)
        if old is None or (b.value > old[0].value if b.kind == "L" else b.value < old[0].value):
            result[key] = (b, offset + i)
    return result


# ---- Exact re-derivation of the native tightenings ----

class Deriver:
    def __init__(self, q, relu_aux):
        self.q, self.facts, self.relu_aux = q, [], dict(relu_aux)   # (x, y) -> aux
        self.decided = {}

    def add(self, fact):
        proof.require(len(self.facts) < MAX_FACTS, "too many preprocessing facts")
        self.q = apply_fact(self.q, fact)
        self.facts.append(fact)

    def bound(self, x, kind):
        entry = tightest(self.q).get((x, kind))
        return entry[0].value if entry else None

    def crossing(self):
        tight = tightest(self.q)
        for (x, kind), (b, _) in sorted(tight.items()):
            if kind == "L" and (x, "U") in tight and b.value > tight[x, "U"][0].value:
                return x
        return None

    def propagate_rows(self):
        """processEquations, generalized to every linear row of the query.
        Bound facts prepend bounds only, so linear row indices stay valid."""
        changed = False
        rows = normalize(self.q)
        for index in range(len(rows) - len(self.q.bounds)):
            for x in sorted(rows[index].t):
                if self.row_bound(index, x):
                    changed = True
                    if self.crossing() is not None:
                        return True
        return changed

    def row_bound(self, index, x):
        rows, tight = normalize(self.q), tightest(self.q)
        row = rows[index]
        a = row.t[x]
        weights = [ZERO] * len(rows)
        weights[index] = ONE / abs(a)
        total = row.c
        for y, c in row.t.items():
            if y == x:
                continue
            kind = "L" if c > 0 else "U"
            entry = tight.get((y, kind))
            if entry is None:
                return False
            total += c * entry[0].value
            weights[entry[1]] += abs(c) / abs(a)
        if a > 0:
            candidate = proof.Bound(x, "U", -total / a)
        else:
            candidate = proof.Bound(x, "L", total / -a)
        current = tight.get((x, candidate.kind))
        if current is not None and (candidate.value <= current[0].value if candidate.kind == "L"
                                    else candidate.value >= current[0].value):
            return False
        self.add(Fact("Bound", (candidate, tuple(weights))))
        return True

    def phase(self, x, y, active):
        q = self.q
        span = Span(hull(q, x, y))
        tight = tightest(q)
        candidates = []
        if active:
            for var, strict in ((x, False), (y, True)):
                entry = tight.get((var, "L"))
                if entry and (entry[0].value > 0 or (not strict and entry[0].value == 0)):
                    candidates.append(entry[0])
            candidates.append(proof.Bound(x, "L", ZERO))
        else:
            for var in (x, y):
                entry = tight.get((var, "U"))
                if entry and entry[0].value <= 0:
                    candidates.append(entry[0])
        others = [i for i in range(len(span.rows)) if i < 2 or i >= len(span.rows) - len(q.bounds)]
        for b in candidates:
            weights = span.with_one_row(bound_row(b), others)
            if weights is not None and implies(hull(q, x, y), bound_row(b), weights):
                self.add(Fact("Phase_Active" if active else "Phase_Inactive", (x, y, b, tuple(weights))))
                self.decided[(x, y)] = active
                return True
        return False

    def relu_rules(self):
        """processConstraints: ReluConstraint::getEntailedTightenings, exactly."""
        changed = False
        for (x, y), aux in self.relu_aux.items():
            if (x, y) in self.decided:
                continue
            lx, ux, ly, uy = (self.bound(x, "L"), self.bound(x, "U"),
                              self.bound(y, "L"), self.bound(y, "U"))
            la, ua = self.bound(aux, "L"), self.bound(aux, "U")
            if (lx is not None and lx >= 0) or (ly is not None and ly > 0) or (ua is not None and ua <= 0):
                if self.phase(x, y, True):
                    changed = True
                    continue
            if (ux is not None and ux <= 0) or (uy is not None and uy <= 0):
                if self.phase(x, y, False):
                    changed = True
                    continue
            if la is not None and la > 0:
                pos, neg = self.aux_witnesses(x, y, aux)
                if pos is not None:
                    self.add(Fact("Relu_Aux_Lower_Output_Upper", (x, y, aux, la, ZERO, pos, neg)))
                    changed = True
                    if self.phase(x, y, False):
                        continue
            if ux is not None and (uy is None or max(ZERO, ux) < uy):
                self.add(Fact("Relu_Upper", (x, y, ux, max(ZERO, ux))))
                changed = True
            if lx is not None and (ua is None or max(ZERO, -lx) < ua):
                pos, neg = self.aux_witnesses(x, y, aux)
                if pos is not None:
                    self.add(Fact("Relu_Aux_Upper", (x, y, aux, lx, max(ZERO, -lx), pos, neg)))
                    changed = True
            if self.crossing() is not None:
                return True
        return changed

    def aux_witnesses(self, x, y, aux):
        span = Span(self.q)
        expr = terms_lin(((ONE, y), (-ONE, x), (-ONE, aux)))
        pos, neg = span.express(expr), span.express(expr.scale(-ONE))
        if pos is None or neg is None:
            return None, None
        return tuple(pos), tuple(neg)

    def run(self):
        for x, y in self.relu_aux:
            self.add(Fact("Hull", (x, y)))
        for _ in range(MAX_ROUNDS):
            changed = self.propagate_rows()
            if self.crossing() is None:
                changed = self.relu_rules() or changed
            if self.crossing() is not None or not changed:
                break
        return self


# ---- Projection onto the preprocessed query ----

def parse_map(obj, n, slacks, relus):
    proof.fields(obj, ("format", "input_variables", "slacks", "relu_auxiliaries", "result"),
                 ("preprocessed_variables", "variables"))
    proof.require(obj["format"] == MAP_FORMAT, "unsupported preprocessing record format")
    proof.require((obj["input_variables"], obj["slacks"], obj["relu_auxiliaries"]) == (n, slacks, relus),
                  "preprocessing record disagrees with the file's variables, inequalities or ReLUs")
    proof.require(obj["result"] in ("preprocessed", "infeasible"), "unknown preprocessing result")
    if obj["result"] == "infeasible":
        proof.require("variables" not in obj and "preprocessed_variables" not in obj,
                      "an infeasible preprocessing record has no variable map")
        return None
    total = n + slacks + relus
    count = obj["preprocessed_variables"]
    proof.require(type(count) is int and 0 < count <= total, "invalid preprocessed variable count")
    entries = proof.array(obj["variables"])
    proof.require(len(entries) == total, "the preprocessing record must list every variable")
    sigma = [None] * count
    for i, entry in enumerate(entries):
        proof.require(type(entry) is dict and entry.get("old") == i and len(entry) == 2,
                      "invalid preprocessing variable entry")
        if "new" in entry:
            j = proof.index(entry["new"], count)
            proof.require(sigma[j] is None, "two variables map to one preprocessed variable")
            sigma[j] = i
        elif "fixed" in entry:
            proof.rational(entry["fixed"])
        else:
            proof.require("merged" in entry, "invalid preprocessing variable entry")
            proof.index(entry["merged"], total)
    proof.require(None not in sigma, "a preprocessed variable has no source")
    return tuple(sigma)


def rename(lin, sigma):
    result = Lin(lin.c)
    for x, a in lin.t.items():
        result = result.plus(Lin(ZERO, {sigma[x] if x < len(sigma) else x: a}))
    return result


def projection_rows(q, target_query, sigma):
    """A witness over normalize(q) for every renamed row of the target."""
    span = Span(q)
    rows = normalize(q)
    bound_rows = list(range(len(rows) - len(q.bounds), len(rows)))
    inequality_rows, index = [], 0
    for atom in q.linear:
        if atom.kind == "EQ":
            index += 2
        else:
            inequality_rows.append(index)
            index += 1
    result = []
    for row in normalize(target_query):
        target = rename(row, sigma)
        weights = span.with_one_row(target, bound_rows + inequality_rows)
        proof.require(weights is not None and implies(q, target, weights),
                      "a preprocessed constraint is not exactly implied by the original query")
        result.append(tuple(weights))
    return tuple(result)


def relu_links(q, target_relus, sigma):
    span = Span(q)
    links = []
    for x2, y2 in target_relus:
        found = None
        for x, y in q.relus:
            same = [same_value(span, a, sigma[b] if b < len(sigma) else b) for a, b in ((x, x2), (y, y2))]
            if None not in same:
                found = (x, y, same[0], same[1])
                break
        proof.require(found is not None, "a preprocessed ReLU has no original counterpart")
        links.append(found)
    return tuple(links)


def same_value(span, a, b):
    if a == b:
        return ()
    difference = Lin(ZERO, {a: ONE, b: -ONE})
    pos, neg = span.express(difference), span.express(difference.scale(-ONE))
    return None if pos is None or neg is None else (tuple(pos), tuple(neg))


# ---- The complete reconstruction ----

@dataclass(frozen=True)
class Preprocessed:
    kind: str                       # "unsat", "infeasible" or "sat"
    file_query: HQuery
    slack_steps: tuple              # ((atom index, slack variable), ...)
    relu_steps: tuple               # ((x, y, aux, lower or None), ...)
    introduced: HQuery | None       # S2
    facts: tuple = ()
    sigma: tuple = ()
    rows: tuple = ()
    links: tuple = ()
    target: HQuery | None = None    # the projection target (preprocessed query or crossing pair)
    replay: object = None           # source.Replay for "unsat"
    crossing: tuple = ()            # (variable, lower, upper) for "infeasible"
    values: tuple = ()              # exact assignment for "sat"


def file_hquery(decoded):
    return HQuery(tuple(Atom(kind, tuple((Fraction(a), x) for a, x in terms), Fraction(rhs))
                        for kind, terms, rhs in decoded.linear),
                  tuple(decoded.bounds), tuple(decoded.relus))


def introductions(decoded):
    """The native variable layout: slacks n.., then ReLU auxiliaries."""
    q = file_hquery(decoded)
    n = max(q.variables(), default=-1) + 1
    slack_steps, s = [], q
    for i, atom in enumerate(q.linear):
        if atom.kind != "EQ":
            slack_steps.append((i, n + len(slack_steps)))
            s = introduce_inequality(s, i, slack_steps[-1][1])
    relu_steps, s2 = [], s
    for j, (x, y) in enumerate(q.relus):
        lower = next((b.value for b in q.bounds if b.variable == x and b.kind == "L"), None)
        aux = n + len(slack_steps) + j
        relu_steps.append((x, y, aux, lower))
        s2 = introduce_relu_aux(s2, x, y, aux, lower)
    return q, n, tuple(slack_steps), tuple(relu_steps), s2


def source_hquery(src):
    return HQuery(tuple(Atom("EQ", e.terms, e.scalar) for e in src.equations),
                  src.bounds, src.relus)


def exact_model(q, values):
    value = lambda x: values[x] if x < len(values) else ZERO
    for atom in q.linear:
        total = sum((a * value(x) for a, x in atom.terms), ZERO)
        ok = {"EQ": total == atom.rhs, "LE": total <= atom.rhs, "GE": total >= atom.rhs}[atom.kind]
        if not ok:
            return False
    return assignment.bounds_ok(values, q.bounds) and assignment.relu_ok(values, q.relus)


def reconstruct(decoded, loaded):
    """loaded: dict of (object, digest), keyed as import_marabou_query_file loads them."""
    q, n, slack_steps, relu_steps, s2 = introductions(decoded)
    record = parse_map(loaded["preprocessing"][0], n, len(slack_steps), len(relu_steps))
    if "assignment" in loaded:
        proof.require(record is not None and "certificate" not in loaded, "unexpected SAT artifacts")
        binary = assignment.parse_assignment(loaded["assignment"][0], n)
        values = binary
        if not exact_model(q, values):
            values = tuple(v.limit_denominator(assignment.REPAIR_DENOMINATOR) for v in binary)
            proof.require(all(abs(v - b) <= assignment.REPAIR_DISTANCE for v, b in zip(values, binary))
                          and exact_model(q, values),
                          "native assignment is not an exact model of the file's query")
        return Preprocessed("sat", q, slack_steps, relu_steps, None, values=values)
    derived = Deriver(s2, {(x, y): aux for x, y, aux, _ in relu_steps}).run()
    if record is None:
        proof.require(set(loaded) == {"preprocessing"}, "unexpected artifacts for infeasible preprocessing")
        variable = derived.crossing()
        proof.require(variable is not None,
                      "no exact contradiction reproduces native preprocessing's infeasibility")
        tight = tightest(derived.q)
        lower, upper = tight[variable, "L"][0].value, tight[variable, "U"][0].value
        target = HQuery((), (proof.Bound(0, "L", lower), proof.Bound(0, "U", upper)), ())
        sigma = (variable,)
        return Preprocessed("infeasible", q, slack_steps, relu_steps, s2, tuple(derived.facts), sigma,
                            projection_rows(derived.q, target, sigma), (), target,
                            crossing=(variable, lower, upper))
    proof.require("certificate" in loaded, "missing native certificate")
    obj = {k: v[0] for k, v in loaded.items()}
    replay = source.reconstruct(obj["source"], obj["steps"], obj["query"], obj["certificate"],
                                obj.get("phase_fixing"))
    proof.require(replay.source.n == len(record), "preprocessed query and record disagree")
    target = source_hquery(replay.source)
    rows = projection_rows(derived.q, target, record)
    links = relu_links(derived.q, target.relus, record)
    return Preprocessed("unsat", q, slack_steps, relu_steps, s2, tuple(derived.facts), record,
                        rows, links, target, replay)


# ---- HOL rendering ----

def hol_atom(atom):
    kind = {"EQ": "RatEq", "LE": "RatLe", "GE": "RatGe"}[atom.kind]
    return f"{kind} {proof.hol_expr(proof.Expr(ZERO, atom.terms))} {proof.hol_rat(atom.rhs)}"


def hol_hquery(q):
    return ("\\<lparr>rat_linear_atoms = " + proof.hol_list(hol_atom(a) for a in q.linear) + ",\n"
            "     rat_query_bounds = " + proof.hol_list(proof.hol_bound(b) for b in q.bounds) + ",\n"
            "     rat_relu_atoms = " + proof.hol_list(f"ReLU {x} {y}" for x, y in q.relus) + "\\<rparr>")


def hol_weights(ws):
    return proof.hol_list(proof.hol_rat(w) for w in ws)


def hol_fact(fact):
    k, a = fact.kind, fact.args
    if k == "Bound":
        return f"Fact_Bound ({proof.hol_bound(a[0])}) {hol_weights(a[1])}"
    if k == "Hull":
        return f"Fact_Hull {a[0]} {a[1]}"
    if k in ("Phase_Active", "Phase_Inactive"):
        return f"Fact_{k} {a[0]} {a[1]} ({proof.hol_bound(a[2])}) {hol_weights(a[3])}"
    if k == "Relu_Upper":
        return f"Fact_Relu_Upper {a[0]} {a[1]} {proof.hol_rat(a[2])} {proof.hol_rat(a[3])}"
    return (f"Fact_{k} {a[0]} {a[1]} {a[2]} {proof.hol_rat(a[3])} {proof.hol_rat(a[4])} "
            f"{hol_weights(a[5])} {hol_weights(a[6])}")


def hol_link(link):
    x, y, wx, wy = link
    return f"Relu_Link {x} {y} {proof.hol_list(hol_weights(w) for w in wx)} " \
           f"{proof.hol_list(hol_weights(w) for w in wy)}"


def hol_projection(result):
    return ("Projection\n    " + proof.hol_list(hol_fact(f) for f in result.facts) + "\n    " +
            proof.hol_list(str(v) for v in result.sigma) + "\n    " +
            proof.hol_list(hol_weights(w) for w in result.rows) + "\n    " +
            proof.hol_list(hol_link(link) for link in result.links))


def hol_relu_steps(steps):
    return proof.hol_list(f"ReLU_Aux_Step {x} {y} {a} " +
                          ("None" if lower is None else f"(Some {proof.hol_rat(lower)})")
                          for x, y, a, lower in steps)


CHAIN = '''
text \\<open>
  Native preprocessing. The file's query gets the native slack and ReLU
  auxiliary introductions (checked, with native variable numbering), then
  checked facts re-derive the native tightenings exactly, and the projection
  shows that every constraint of {target_name} is implied under the recorded
  variable renaming. None of the preprocessing record is trusted.
  Preprocessing record SHA-256: {map_hash}
\\<close>

definition imported_file_query :: rat_query where
  "imported_file_query = {file_query}"

definition imported_slack_steps :: "inequality_aux_step list" where
  "imported_slack_steps = {slack_steps}"

definition imported_relu_aux_steps :: "relu_aux_step list" where
  "imported_relu_aux_steps = {relu_steps}"

definition imported_introduced_query :: rat_query where
  "imported_introduced_query = {introduced}"

lemma imported_introductions_match:
  "(case rat_introduce_inequality_aux_sequence imported_file_query imported_slack_steps of
      None \\<Rightarrow> None
    | Some P \\<Rightarrow> rat_introduce_relu_aux_sequence P imported_relu_aux_steps) =
    Some imported_introduced_query"
  by code_simp
{target_lemmas}
definition imported_projection :: projection where
  "imported_projection = {projection}"

lemma imported_projection_checked:
  "check_projection imported_introduced_query imported_projection {target_name}"
  by code_simp

theorem imported_file_query_unsatisfiable:
  "unsatisfiable (embed_query imported_file_query)"
proof -
  obtain P where slacks: "rat_introduce_inequality_aux_sequence imported_file_query imported_slack_steps = Some P"
      and relus: "rat_introduce_relu_aux_sequence P imported_relu_aux_steps = Some imported_introduced_query"
    using imported_introductions_match by (auto split: option.splits)
  have "unsatisfiable (embed_query imported_introduced_query)"
    by (rule check_projection_unsatisfiable[OF imported_projection_checked {target_unsat}])
  then have "unsatisfiable (embed_query P)"
    using relu_aux_sequence_unsatisfiable_iff[OF relus] by simp
  then show ?thesis
    using inequality_aux_sequence_unsatisfiable_iff[OF slacks] by simp
qed
'''


def render_chain(result, map_hash, target_name, target_lemmas, target_unsat):
    return CHAIN.format(
        map_hash=map_hash, file_query=hol_hquery(result.file_query),
        slack_steps=proof.hol_list(f"({i}, {s})" for i, s in result.slack_steps),
        relu_steps=hol_relu_steps(result.relu_steps), introduced=hol_hquery(result.introduced),
        projection=hol_projection(result), target_name=target_name,
        target_lemmas=target_lemmas, target_unsat=target_unsat)


IMPORTS = ('"Marabou_Verification.Preprocessing_Projection" '
           '"Marabou_Verification.Inequality_Auxiliary_Sequence"\n'
           '    "Marabou_Verification.ReLU_Auxiliary_Sequence" "Marabou_Verification.Tableau_Auxiliary_Sequence"')


def render_theory(name, result, hashes):
    proof.require(re.fullmatch(r"[A-Z][A-Za-z0-9_]*", name) is not None, "invalid theory name")
    if result.kind == "unsat":
        h = hashes
        base = source.render_theory(name, result.replay, h["source"], h["steps"], h["query"],
                                    h["certificate"])
        base = re.sub(r'  imports [^\n]*\n', f"  imports {IMPORTS}\n", base, count=1)
        chain = render_chain(result, h["preprocessing"], "imported_source_query", "",
                             "imported_source_query_unsatisfiable")
        return base.replace("\nend\n", chain + "\nend\n")
    if result.kind == "infeasible":
        variable, lower, upper = result.crossing
        target_lemmas = f'''
definition imported_crossing_query :: rat_query where
  "imported_crossing_query = {hol_hquery(result.target)}"

text \\<open>
  Native preprocessing reported infeasibility without a proof. The facts
  derive {proof.hol_rat(lower)} <= x{variable} <= {proof.hol_rat(upper)} exactly.
\\<close>

lemma imported_crossing_query_unsatisfiable:
  "unsatisfiable (embed_query imported_crossing_query)"
  by (rule check_certificate_sound) code_simp
'''.replace("(rule check_certificate_sound) code_simp",
            "(rule check_certificate_sound[of _ \"Linear_Unsat [1, 1]\"]) code_simp")
        header = f'''theory {name}
  imports {IMPORTS}
begin
'''
        chain = render_chain(result, hashes["preprocessing"], "imported_crossing_query", target_lemmas,
                             "imported_crossing_query_unsatisfiable")
        return header + chain + "\nend\n"
    values = proof.hol_list(f"({i}, {proof.hol_rat(v)})" for i, v in enumerate(result.values))
    return f'''theory {name}
  imports "Marabou_Verification.Rational_Assignment"
begin

text \\<open>
  Generated by the untrusted preprocessing adapter. The native run used
  Marabou's preprocessing; Engine::extractSolution mapped its solution back
  to the file's variables. The code_simp proof checks every atom exactly.
  Assignment SHA-256: {hashes["assignment"]}
\\<close>

definition imported_file_query :: rat_query where
  "imported_file_query = {hol_hquery(result.file_query)}"

definition imported_assignment :: rat_assignment where
  "imported_assignment = {values}"

lemma imported_file_assignment_checked:
  "check_rat_assignment imported_file_query imported_assignment"
  by code_simp

theorem imported_file_query_model:
  "satisfies_query (assignment_valuation imported_assignment) (embed_query imported_file_query)"
  by (rule check_rat_assignment_sound[OF imported_file_assignment_checked])

end
'''
