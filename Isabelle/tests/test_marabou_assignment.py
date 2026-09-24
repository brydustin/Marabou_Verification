#!/usr/bin/env python3
"""Exact SAT assignments: native capture replay, provenance and adversarial import tests."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_assignment as adapter
import import_marabou_json as proof

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
STEM = "solver_relu_sat"
ORDER = ("_source.json", "_steps.json", "_query.json", "_assignment.json",
         "_before_relu.json", "_relu_steps.json")
KEYS = ("source", "steps", "query", "assignment", "before", "introductions")


def native_loaded():
    return [proof.load_json(FIXTURES / (STEM + suffix)) for suffix in ORDER]


def native_inputs():
    return [obj for obj, _ in native_loaded()]


def entry(i, q):
    return {"var": i, "value": q, "hex": float(q).hex()}


class AssignmentImportTests(unittest.TestCase):
    def rejects(self, inputs, message="."):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            adapter.reconstruct(*inputs)

    def test_native_sat_capture_replays_and_regenerates(self):
        loaded = native_loaded()
        replay = adapter.reconstruct(*(obj for obj, _ in loaded))
        hashes = {k: h for k, (_, h) in zip(KEYS, loaded)}
        name = "Imported_Marabou_Native_Relu_Sat"
        self.assertEqual(adapter.render_theory(name, replay, hashes),
                         (ISABELLE / (name + ".thy")).read_text())
        self.assertEqual(replay.reconstruction, adapter.EXACT)
        half = Fraction(1, 2)
        self.assertEqual(replay.assignment,
                         (half, half, -2, 0, half, -2, half, 0, 2, 0, 0, 0, 0, 0))
        self.assertEqual(replay.instance.n, 14)
        self.assertEqual(replay.before.n, 7)
        self.assertEqual([(s.x, s.y, s.auxiliary, s.lower) for s in replay.introductions],
                         [(0, 1, 7, -2), (2, 3, 8, -2)])
        # One ReLU active (f = b), one inactive (g = 0 with c < 0).
        values = replay.assignment
        self.assertTrue(values[1] == values[0] > 0 and values[3] == 0 > values[2])

    def test_native_sat_run_report(self):
        report = json.loads((FIXTURES / (STEM + "_run.json")).read_text())
        for field in ("proof_production", "initialization_succeeded", "solve_return",
                      "snapshot_before_relu_introduction", "introduction_list_before_solve",
                      "source_snapshot_before_initialization", "relu_phase_unfixed_before_solve",
                      "initial_snapshot_matches_tableau_and_ground_bounds"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi"):
            self.assertFalse(report[field], field)
        for field, value in (("scenario", "relu_sat"), ("exit_code", "SAT"),
                             ("native_relu_introductions", 2), ("variables_before_relu_introduction", 7),
                             ("input_variables", 9), ("processed_variables", 14),
                             ("assignment_variables", 14), ("proposed_introductions", 5)):
            self.assertEqual(report[field], value, field)

    def test_native_sat_provenance(self):
        provenance = json.loads((FIXTURES / (STEM + "_provenance.json")).read_text())
        self.assertEqual(provenance["scenario"], "relu_sat")
        self.assertNotIn("certificate_sha256", provenance)
        self.assertEqual(provenance["marabou_revision"], "1c2f4788c32e2f4e407c356b763a8025c5578722")
        for key, path in (
            ("source_query_sha256", FIXTURES / (STEM + "_source.json")),
            ("introduction_list_sha256", FIXTURES / (STEM + "_steps.json")),
            ("processed_query_sha256", FIXTURES / (STEM + "_query.json")),
            ("assignment_sha256", FIXTURES / (STEM + "_assignment.json")),
            ("before_relu_query_sha256", FIXTURES / (STEM + "_before_relu.json")),
            ("relu_introduction_sequence_sha256", FIXTURES / (STEM + "_relu_steps.json")),
            ("run_report_sha256", FIXTURES / (STEM + "_run.json")),
            ("solver_log_sha256", FIXTURES / (STEM + ".log")),
            ("capture_script_sha256", ISABELLE / "tools/capture_marabou_solver.py"),
            ("importer_sha256", ISABELLE / "tools/import_marabou_json.py"),
            ("source_importer_sha256", ISABELLE / "tools/import_marabou_source.py"),
            ("assignment_importer_sha256", ISABELLE / "tools/import_marabou_assignment.py"),
            ("relu_sequence_importer_sha256", ISABELLE / "tools/import_marabou_relu_sequence.py"),
            ("cmake_sha256", ISABELLE / "tools/solver_capture/CMakeLists.txt"),
        ):
            self.assertEqual(provenance[key], hashlib.sha256(path.read_bytes()).hexdigest(), key)
        for relative, digest in provenance["compiled_sources"].items():
            self.assertEqual(hashlib.sha256((ISABELLE.parent / relative).read_bytes()).hexdigest(),
                             digest, relative)

    def test_changed_value_is_rejected(self):
        inputs = native_inputs()
        inputs[3]["values"][1] = entry(1, Fraction(1, 4))
        self.rejects(inputs, "not an exact model")

    def test_relu_violation_with_every_row_and_bound_satisfied_is_rejected(self):
        values = [Fraction(v) for v in ("1/2", "1/2", "-1/4", "1/2", "1/2", "-1/4", "1", "0", "3/4")]
        inputs = native_inputs()
        inputs[3]["values"] = [entry(i, q) for i, q in enumerate(values + [Fraction(0)] * 5)]
        replay_query = proof.parse_instance(inputs[2])
        relaxed = proof.Instance(replay_query.n, proof.Query(replay_query.query.equations,
                                                             replay_query.query.bounds, ()), ())
        padded = tuple(values + [Fraction(0)] * 5)
        self.assertTrue(adapter.processed_model(relaxed, padded))
        self.assertFalse(adapter.processed_model(replay_query, padded))
        self.rejects(inputs, "not an exact model")

    def test_consistent_binary_values_are_used_exactly(self):
        # b=f=z=y moved together by about 1e-13 is still an exact model.
        inputs = native_inputs()
        near = Fraction(float(Fraction(1, 2) + Fraction(1, 10**13)))
        self.assertNotEqual(near.denominator, 2)
        for i in (0, 1, 4, 6):
            inputs[3]["values"][i] = entry(i, near)
        replay = adapter.reconstruct(*inputs)
        self.assertEqual(replay.reconstruction, adapter.EXACT)
        self.assertEqual(replay.assignment[0], near)

    def test_near_miss_is_repaired_only_if_the_exact_check_accepts(self):
        inputs = native_inputs()
        near = Fraction(float(Fraction(1, 2) + Fraction(1, 10**13)))
        inputs[3]["values"][0] = entry(0, near)
        replay = adapter.reconstruct(*inputs)
        self.assertEqual(replay.reconstruction, adapter.REPAIRED)
        self.assertEqual(replay.assignment[0], Fraction(1, 2))
        self.assertIn("simplest rationals", adapter.render_theory(
            "Repaired", replay, {k: "0" * 64 for k in KEYS}))

    def test_far_miss_is_not_repaired(self):
        inputs = native_inputs()
        inputs[3]["values"][0] = entry(0, Fraction(1, 2) + Fraction(1, 1000))
        self.rejects(inputs, "no nearby small-denominator repair")

    def test_decimal_and_hex_must_denote_the_same_double(self):
        inputs = native_inputs()
        inputs[3]["values"][0]["value"] = Fraction(1, 4)
        self.rejects(inputs, "disagree")

    def test_malformed_hex_values_are_rejected(self):
        for token in ("inf", "nan", "0x1p", "0X1P-1", " 0x1p-1", "0x1p-99999", 0.5, "1.0"):
            inputs = native_inputs()
            inputs[3]["values"][0]["hex"] = token
            with self.subTest(token=token):
                self.rejects(inputs, "hexadecimal")

    def test_nonfinite_hex_overflow_is_rejected(self):
        inputs = native_inputs()
        inputs[3]["values"][0]["hex"] = "0x1p+9999"
        self.rejects(inputs, "nonfinite")

    def test_assignment_shape_is_strict(self):
        mutations = [
            ("format", lambda a: a.update(format="marabou-assignment-v2"), "format"),
            ("count", lambda a: a.update(variables=13), "exactly the processed variables"),
            ("bool", lambda a: a.update(variables=True), "exactly the processed variables"),
            ("missing", lambda a: a["values"].pop(), "every processed variable"),
            ("order", lambda a: a["values"].reverse(), "in order"),
            ("extra field", lambda a: a["values"][0].update(extra=1), "unknown"),
            ("missing field", lambda a: a["values"][0].pop("hex"), "missing"),
        ]
        for name, mutate, message in mutations:
            inputs = native_inputs()
            mutate(inputs[3])
            with self.subTest(name=name):
                self.rejects(inputs, message)

    def test_query_substitution_is_rejected(self):
        inputs = native_inputs()
        inputs[2]["upperBounds"][6] = Fraction(1, 4)
        self.rejects(inputs, "does not match")
        inputs = native_inputs()
        inputs[4]["upperBounds"][6] = Fraction(1, 4)
        self.rejects(inputs, "does not match")

    def test_before_query_requires_its_introductions(self):
        inputs = native_inputs()
        self.rejects(inputs[:5] + [None], "requires")
        self.rejects(inputs[:4] + [None, inputs[5]], "requires")

    def test_unsat_source_cannot_be_witnessed(self):
        bundle = [proof.load_json(FIXTURES / ("solver_relu_aux_inactive" + s))[0]
                  for s in ("_source.json", "_steps.json", "_query.json")]
        # aux=w=0 violates w>=1/4 in the UNSAT source; its SAT relaxation accepts it.
        values = [Fraction(v) for v in ("0", "1/4", "1/4", "0", "1/4", "0", "0", "0")]
        assignment = {"format": "marabou-assignment-v1", "variables": 8,
                      "values": [entry(i, q) for i, q in enumerate(values)]}
        self.rejects(bundle + [assignment], "not an exact model")
        relaxed = copy.deepcopy(bundle)
        relaxed[0]["lowerBounds"][3] = 0
        relaxed[2]["lowerBounds"][3] = 0
        replay = adapter.reconstruct(*relaxed, assignment)
        self.assertEqual(replay.reconstruction, adapter.EXACT)
        self.assertIsNone(replay.before)


if __name__ == "__main__":
    unittest.main()
