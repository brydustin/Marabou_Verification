#!/usr/bin/env python3
"""Native introduction binding and adversarial replay tests; HOL checks soundness."""
import contextlib
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as proof
import import_marabou_source as source
import import_marabou_relu_intro as adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
STEM = "solver_relu_intro"
SUFFIXES = ("_before_relu.json", "_relu_step.json", "_source.json",
            "_steps.json", "_query.json", ".json")
FLAGS = ("--before-relu", "--relu-step", "--source", "--steps", "--query", "--certificate")


def load_bundle():
    return [proof.load_json(FIXTURES / (STEM + suffix)) for suffix in SUFFIXES]


def bundle():
    return [obj for obj, _ in load_bundle()]


class NativeReluIntroductionTests(unittest.TestCase):
    def rejects(self, inputs, message="."):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            adapter.reconstruct(*inputs)

    def test_native_capture_replays_and_regenerates(self):
        loaded = load_bundle()
        replay = adapter.reconstruct(*(obj for obj, _ in loaded))
        name = "Imported_Marabou_Native_Relu_Intro"
        self.assertEqual(adapter.render_theory(name, replay, *(h for _, h in loaded)),
                         (ISABELLE / (name + ".thy")).read_text())
        self.assertEqual((replay.before.n, replay.after.source.n, replay.after.instance.n),
                         (4, 5, 8))
        self.assertEqual(replay.before.relu_metadata, ((0, 1),))
        self.assertEqual(replay.after.source.relu_metadata, ((0, 1, 4),))
        self.assertEqual(replay.introduction, adapter.Introduction(0, 1, 4, Fraction(-2)))
        self.assertEqual(replay.after.steps, ((0, 5), (1, 6), (2, 7)))
        self.assertEqual(replay.after.source.equations[-1],
                         source.Equation(((1, 1), (-1, 0), (-1, 4)), 0))
        self.assertEqual(replay.after.source.bounds[-2:],
                         (proof.Bound(4, "L", 0), proof.Bound(4, "U", 2)))
        cert = replay.after.certificate
        self.assertIsInstance(cert, proof.LinearBound)
        self.assertIsInstance(cert.child, proof.ReluAuxUpper)
        self.assertIsInstance(cert.child.child, proof.LinearBound)
        self.assertIsInstance(cert.child.child.child, proof.ReluUpper)
        self.assertIsInstance(cert.child.child.child.child, proof.Leaf)

    def test_run_records_native_introduction_and_solver_evidence(self):
        report = json.loads((FIXTURES / (STEM + "_run.json")).read_text())
        for field in ("snapshot_before_relu_introduction", "source_snapshot_before_initialization",
                      "introduction_list_before_solve", "proof_production", "initialization_succeeded",
                      "initial_snapshot_matches_tableau_and_ground_bounds",
                      "relu_phase_unfixed_before_solve"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi", "solve_return"):
            self.assertFalse(report[field], field)
        for field, value in (("native_relu_introductions", 1), ("variables_before_relu_introduction", 4),
                             ("input_variables", 5), ("processed_variables", 8),
                             ("proposed_introductions", 3), ("plc_lemmas_before_solve", 0),
                             ("plc_lemmas_after_solve", 2), ("explained_leaves", 1),
                             ("delegated_leaves", 0), ("root_children", 0), ("exit_code", "UNSAT")):
            self.assertEqual(report[field], value, field)
        self.assertGreater(report["main_loop_iterations"], 0)

    def test_additional_provenance_hashes(self):
        provenance = json.loads((FIXTURES / (STEM + "_provenance.json")).read_text())
        for key, path in (
            ("before_relu_query_sha256", FIXTURES / (STEM + "_before_relu.json")),
            ("relu_introduction_sha256", FIXTURES / (STEM + "_relu_step.json")),
            ("relu_intro_importer_sha256", ISABELLE / "tools/import_marabou_relu_intro.py"),
        ):
            self.assertEqual(provenance[key], hashlib.sha256(path.read_bytes()).hexdigest())

    def test_plain_query_cannot_be_used_as_an_already_introduced_source(self):
        with self.assertRaisesRegex(proof.ImportFailure, "format"):
            source.parse_source(bundle()[0])

    def test_reject_absent_or_reversed_relu(self):
        for value in ([], [{"constraintType": 0, "vars": [1, 0]}]):
            inputs = bundle()
            inputs[0]["constraints"] = value
            self.rejects(inputs)

    def test_reject_already_auxiliary_or_multiple_relus(self):
        for value in ([{"constraintType": 0, "vars": [0, 1, 2]}],
                      [{"constraintType": 0, "vars": [0, 1]},
                       {"constraintType": 0, "vars": [2, 3]}]):
            inputs = bundle()
            inputs[0]["constraints"] = value
            self.rejects(inputs)

    def test_reject_wrong_selected_relu(self):
        for field, value in (("input", 1), ("output", 2)):
            inputs = bundle()
            inputs[1][field] = value
            self.rejects(inputs, "selected ReLU is absent")

    def test_reject_occupied_auxiliary(self):
        for variable in range(4):
            inputs = bundle()
            inputs[1]["auxiliary"] = variable
            self.rejects(inputs, "not fresh")

    def test_reject_wrong_finite_lower_premise(self):
        for value in (-3, 0, Fraction(-2) + Fraction(1, 10**20)):
            inputs = bundle()
            inputs[1]["lower"] = value
            self.rejects(inputs, "lower bound is absent")

    def test_reject_inexact_or_missing_lower(self):
        for value in (None, True, "-2", -2.0, float("inf"), float("nan")):
            inputs = bundle()
            inputs[1]["lower"] = value
            self.rejects(inputs, "exact JSON number")

    def test_reject_noninteger_and_out_of_range_step_indices(self):
        for field in ("input", "output", "auxiliary"):
            for value in (True, Fraction(1), "1", -1, proof.MAX_VARS + 1):
                inputs = bundle()
                inputs[1][field] = value
                with self.subTest(field=field, value=value):
                    self.rejects(inputs)

    def test_reject_unknown_fields_or_schemas(self):
        for i, key, value in ((0, "format", "marabou-source-query-v1"),
                              (1, "format", "marabou-relu-aux-introduction-v2"),
                              (0, "assumed", []), (1, "upper", 2), (1, "trusted", True)):
            inputs = bundle()
            inputs[i][key] = value
            self.rejects(inputs)
        inputs = bundle()
        del inputs[1]["lower"]
        self.rejects(inputs)

    def test_reject_changed_before_equation(self):
        for field in ("scalar", "coefficient"):
            inputs = bundle()
            if field == "scalar":
                inputs[0]["equations"][0]["scalar"] = Fraction(1, 10**20)
            else:
                inputs[0]["equations"][0]["addends"][0]["val"] = -1
            self.rejects(inputs, "independent after query")

    def test_reject_changed_before_bound(self):
        inputs = bundle()
        inputs[0]["lowerBounds"][3] = 0
        self.rejects(inputs, "independent after query")

    def test_reject_changed_native_auxiliary_equation(self):
        for field in ("scalar", "coefficient", "variable", "missing"):
            inputs = bundle()
            equation = inputs[2]["equations"][-1]
            if field == "scalar":
                equation["scalar"] = 1
            elif field == "coefficient":
                equation["addends"][-1]["val"] = 1
            elif field == "variable":
                equation["addends"][-1]["var"] = 2
            else:
                inputs[2]["equations"].pop()
            self.rejects(inputs, "independent after query")

    def test_reject_changed_native_auxiliary_bounds(self):
        for field, value in (("lowerBounds", -1), ("lowerBounds", 1),
                             ("upperBounds", 1), ("upperBounds", 3)):
            inputs = bundle()
            inputs[2][field][4] = value
            self.rejects(inputs, "independent after query")

    def test_reject_changed_old_atom_in_after_query(self):
        for field in ("bound", "equation", "metadata"):
            inputs = bundle()
            if field == "bound":
                inputs[2]["lowerBounds"][0] = -1
            elif field == "equation":
                inputs[2]["equations"][0]["scalar"] = 1
            else:
                inputs[2]["constraints"][0]["vars"][2] = 3
            self.rejects(inputs, "independent after query")

    def test_reject_stronger_cap_even_with_matching_later_snapshots(self):
        inputs = bundle()
        for i in (2, 4, 5):
            inputs[i]["upperBounds"][4] = 1
        self.rejects(inputs, "independent after query")

    def test_reject_bad_tableau_introductions_after_valid_relu_step(self):
        for field in ("missing", "reuse"):
            inputs = bundle()
            if field == "missing":
                inputs[3]["steps"].pop()
            else:
                inputs[3]["steps"][0]["variable"] = 4
            self.rejects(inputs)

    def test_reject_substituted_processed_query_or_proof_header(self):
        for i in (4, 5):
            inputs = bundle()
            inputs[i]["lowerBounds"][3] = 0
            self.rejects(inputs)

    def test_reject_corrupt_propagation_or_terminal_evidence(self):
        for field in ("lemma", "explanation", "leaf"):
            inputs = bundle()
            native_proof = inputs[5]["proof"]
            if field == "lemma":
                native_proof["lemmas"][0]["bound"] = 1
            elif field == "explanation":
                native_proof["lemmas"][0]["expl"][0]["val"] = 0
            else:
                native_proof["contradiction"][0]["val"] = 0
            self.rejects(inputs)

    def test_relaxed_sat_queries_still_require_a_valid_proof(self):
        inputs = bundle()
        for i in (0, 2, 4, 5):
            inputs[i]["lowerBounds"][3] = 0
        # Both introductions are consistent with this explicit real/rational model.
        values = (Fraction(-1, 2), 0, Fraction(-1, 2), 0, Fraction(1, 2), 0, 0, 0)
        for i, plain in ((0, True), (2, False)):
            query = source.parse_source(inputs[i], plain_relu=plain)
            self.assertTrue(all(sum(c * values[v] for c, v in e.terms) == e.scalar
                                for e in query.equations))
            self.assertTrue(all(values[y] == max(0, values[x]) for x, y in query.relus))
            self.assertTrue(all(b.value <= values[b.variable] if b.kind == "L"
                                else values[b.variable] <= b.value for b in query.bounds))
        processed = proof.parse_instance(inputs[4]).query
        self.assertTrue(all(e.constant + sum(c * values[v] for c, v in e.terms) == 0
                            for e in processed.equations))
        self.assertTrue(all(b.value <= values[b.variable] if b.kind == "L"
                            else values[b.variable] <= b.value for b in processed.bounds))
        self.assertTrue(all(values[y] == max(0, values[x]) for x, y in processed.relus))
        self.rejects(inputs, "PLC conclusion is too strong")

    def test_cli_preserves_all_six_inputs_and_existing_root(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / f"Input{i}.thy" for i in range(6)]
            for path, suffix in zip(paths, SUFFIXES):
                path.write_bytes((FIXTURES / (STEM + suffix)).read_bytes())
            arguments = [item for flag, path in zip(FLAGS, paths) for item in (flag, str(path))]
            for path in paths:
                original = path.read_bytes()
                with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                    adapter.main(arguments + ["--output", str(path)])
                self.assertEqual(path.read_bytes(), original)
            output = Path(directory) / "Replay.thy"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(adapter.main(arguments + ["--output", str(output), "--session"]), 0)
            self.assertIn("imported_before_relu_query_unsatisfiable", output.read_text())
            self.assertIn("quick_and_dirty = false", (output.parent / "ROOT").read_text())
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                adapter.main(arguments + ["--output", str(output), "--session"])

    def test_renderer_rejects_name_digest_and_import_injection(self):
        loaded = load_bundle()
        replay = adapter.reconstruct(*(obj for obj, _ in loaded))
        hashes = [h for _, h in loaded]
        with self.assertRaises(proof.ImportFailure):
            adapter.render_theory('Replay"\nend', replay, *hashes)
        for i in range(6):
            invalid = hashes.copy()
            invalid[i] = '0"\nend'
            with self.assertRaises(proof.ImportFailure):
                adapter.render_theory("Replay", replay, *invalid)
        with self.assertRaises(proof.ImportFailure):
            source.render_theory("Replay", replay.after, *hashes[2:],
                                 extra_imports=('Bad"\nend',))


if __name__ == "__main__":
    unittest.main()
