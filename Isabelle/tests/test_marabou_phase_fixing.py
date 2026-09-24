#!/usr/bin/env python3
"""ReLU phases fixed before solve(): record parsing, exact justification, necessity."""
import copy
from fractions import Fraction
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as proof
import import_marabou_query_file as adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
UNSAT = ("phase_active_unsat", "phase_inactive_unsat", "phase_chain_unsat")


def data(example):
    return (ISABELLE / "examples" / (example + ".mqx")).read_bytes()


def loaded(example):
    return adapter.load_artifacts(FIXTURES / ("file_" + example))


def certificate(example):
    return adapter.reconstruct(data(example), loaded(example)).replay.after.certificate


class RecordTests(unittest.TestCase):
    def instance(self, example="phase_active_unsat"):
        return proof.parse_instance(loaded(example)["query"][0])

    def record(self, example="phase_active_unsat"):
        return copy.deepcopy(loaded(example)["phase_fixing"][0])

    def test_saved_records_are_the_native_valid_splits(self):
        expected = {"phase_active_unsat": (0, 1, 3, True), "phase_inactive_unsat": (0, 1, 3, False),
                    "phase_chain_unsat": (0, 1, 5, False), "phase_fixed_sat": (0, 1, 3, True)}
        for example, (x, y, aux, active) in expected.items():
            with self.subTest(example=example):
                fixes = proof.parse_phase_fixing(self.record(example), self.instance(example))
                self.assertEqual(fixes, (proof.PhaseFix(x, y, aux, active),))

    def test_malformed_records_are_rejected(self):
        instance = self.instance()
        mutations = []
        for key, value in (("format", "other"), ("fixed", []), ("fixed", {}), ("extra", 1)):
            record = self.record()
            record[key] = value
            mutations.append(record)
        item_changes = (("phase", "fixed"), ("phase", "inactive"), ("input", 2), ("output", 0),
                        ("auxiliary", 2), ("input", -1), ("input", True), ("bounds", []),
                        ("bounds", [{"var": 0, "type": "L", "value": 0}]),
                        ("bounds", [{"var": 0, "type": "L", "value": 0},
                                    {"var": 3, "type": "U", "value": 1}]),
                        ("bounds", [{"var": 0, "type": "L", "value": 0},
                                    {"var": 3, "type": "X", "value": 0}]),
                        ("bounds", [{"var": 0, "type": "L", "value": 0},
                                    {"var": 3, "type": "U", "value": 0.0}]))
        for key, value in item_changes:
            record = self.record()
            record["fixed"][0][key] = value
            mutations.append(record)
        record = self.record()
        record["fixed"][0]["extra"] = 0
        mutations.append(record)
        record = self.record()
        record["fixed"].append(copy.deepcopy(record["fixed"][0]))
        mutations.append(record)
        for record in mutations:
            with self.subTest(record=record), self.assertRaises(proof.ImportFailure):
                proof.parse_phase_fixing(record, instance)


class JustificationTests(unittest.TestCase):
    def test_certificates_start_with_the_checked_phase(self):
        for example, active, bound in (
                ("phase_active_unsat", True, proof.Bound(1, "L", Fraction(3, 2))),
                ("phase_inactive_unsat", False, proof.Bound(0, "U", Fraction(-1, 2))),
                ("phase_chain_unsat", False, proof.Bound(0, "U", Fraction(-1, 2)))):
            with self.subTest(example=example):
                cert = certificate(example)
                self.assertIsInstance(cert, proof.ReluFix)
                self.assertEqual((cert.x, cert.y, cert.active, cert.bound), (0, 1, active, bound))
                hol = proof.hol_certificate(cert)
                self.assertTrue(hol.startswith("Relu_Fix_" + ("Active" if active else "Inactive")))

    def test_root_fix_feeds_later_native_lemmas(self):
        cert = certificate("phase_chain_unsat").child
        kinds = []
        while not isinstance(cert, proof.Leaf):
            kinds.append(type(cert).__name__)
            cert = cert.child
        self.assertEqual(kinds, ["LinearBound", "ReluAuxUpper", "LinearBound", "ReluUpper"])

    def test_native_proofs_need_the_fixed_phase(self):
        # Without the record the unexplained split bounds are missing.
        for example in UNSAT:
            artifacts = loaded(example)
            del artifacts["phase_fixing"]
            with self.subTest(example=example), self.assertRaises(proof.ImportFailure):
                adapter.reconstruct(data(example), artifacts)

    def test_wrong_phase_is_rejected(self):
        for example in UNSAT:
            artifacts = loaded(example)
            item = artifacts["phase_fixing"][0]["fixed"][0]
            active = item["phase"] == "active"
            x, y, aux = item["input"], item["output"], item["auxiliary"]
            item["phase"] = "inactive" if active else "active"
            item["bounds"] = ([{"var": x, "type": "U", "value": 0}, {"var": y, "type": "U", "value": 0}]
                              if active else
                              [{"var": x, "type": "L", "value": 0}, {"var": aux, "type": "U", "value": 0}])
            with self.subTest(example=example), self.assertRaises(proof.ImportFailure):
                adapter.reconstruct(data(example), artifacts)

    def test_epsilon_phase_decisions_are_not_trusted(self):
        # Natively, an input upper bound within epsilon of zero fixes the
        # inactive phase. Exactly, 10^-12 does not, and no premise is found.
        fix = proof.PhaseFix(0, 1, 3, False)
        for upper, accepted in ((Fraction(1, 10 ** 12), False), (Fraction(0), True)):
            query = loaded("phase_inactive_unsat")["query"][0]
            query["upperBounds"][0] = upper
            instance = proof.parse_instance(query)
            bounds = {(b.variable, b.kind): b for b in instance.query.bounds}
            with self.subTest(upper=upper):
                if accepted:
                    self.assertEqual(proof.phase_premise(instance, instance.query, bounds, fix)[0],
                                     proof.Bound(0, "U", upper))
                else:
                    with self.assertRaisesRegex(proof.ImportFailure, "no exact justification"):
                        proof.phase_premise(instance, instance.query, bounds, fix)

    def test_active_premise_through_the_hull_row(self):
        # f - b - aux = 0 with aux <= 0 and a negative lower bound on f:
        # b >= 0 needs the ReLU's valid inequality f >= 0.
        n = 3
        query = proof.Query((proof.Expr(proof.ZERO, ((proof.ONE, 1), (-proof.ONE, 0), (-proof.ONE, 2))),),
                            (proof.Bound(0, "L", Fraction(-1)), proof.Bound(0, "U", Fraction(2)),
                             proof.Bound(1, "L", Fraction(-1)), proof.Bound(1, "U", Fraction(2)),
                             proof.Bound(2, "L", Fraction(0)), proof.Bound(2, "U", Fraction(0))),
                            ((0, 1),))
        instance = proof.Instance(n, query, ((0, 1, 2, 2),))
        bounds = {(b.variable, b.kind): b for b in query.bounds}
        bound, weights = proof.phase_premise(instance, query, bounds, proof.PhaseFix(0, 1, 2, True))
        self.assertEqual(bound, proof.Bound(0, "L", Fraction(0)))
        self.assertEqual(weights[0], 1)


class SatTests(unittest.TestCase):
    def test_sat_needs_no_justification_but_rejects_malformed_records(self):
        replay = adapter.reconstruct(data("phase_fixed_sat"), loaded("phase_fixed_sat"))
        self.assertEqual(replay.kind, "sat")
        artifacts = loaded("phase_fixed_sat")
        artifacts["phase_fixing"][0]["fixed"][0]["phase"] = "unknown"
        with self.assertRaises(proof.ImportFailure):
            adapter.reconstruct(data("phase_fixed_sat"), artifacts)

    def test_linear_files_cannot_carry_a_record(self):
        artifacts = adapter.load_artifacts(FIXTURES / "solver_linear")
        artifacts["phase_fixing"] = loaded("phase_active_unsat")["phase_fixing"]
        with self.assertRaisesRegex(proof.ImportFailure, "needs ReLUs"):
            adapter.reconstruct((ISABELLE / "examples/linear_unsat.mqx").read_bytes(), artifacts)


class TheoryTests(unittest.TestCase):
    def test_generated_theories_contain_the_checked_fixes(self):
        for example in UNSAT:
            name = dict(adapter.FULL_ARTIFACT_EXAMPLES)[example]
            theory = (ISABELLE / (name + ".thy")).read_text()
            with self.subTest(example=example):
                self.assertIn("Relu_Fix_", theory)
                self.assertIn("imported_before_relu_query_unsatisfiable", theory)
            example_theory = (ISABELLE / (adapter.example_theory_name(example) + ".thy")).read_text()
            self.assertIn("query_file_unsatisfiable", example_theory)


if __name__ == "__main__":
    unittest.main()
