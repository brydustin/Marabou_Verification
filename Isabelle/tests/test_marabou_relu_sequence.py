#!/usr/bin/env python3
"""Finite native introduction replay, provenance and rejection regressions."""
import contextlib
import copy
from dataclasses import replace
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
import import_marabou_relu_sequence as adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
STEM = "solver_relu_sequence"
SUFFIXES = ("_before_relu.json", "_relu_steps.json", "_source.json",
            "_steps.json", "_query.json", ".json")
FLAGS = ("--before-relu", "--relu-steps", "--source", "--steps", "--query", "--certificate")


def load_bundle(directory=FIXTURES):
    return [proof.load_json(directory / (STEM + suffix)) for suffix in SUFFIXES]


def bundle():
    return [obj for obj, _ in load_bundle()]


class ReLUSequenceImportTests(unittest.TestCase):
    def rejects(self, inputs, message="."):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            adapter.reconstruct(*inputs)

    def test_two_native_introductions_replay_and_regenerate(self):
        loaded = load_bundle()
        replay = adapter.reconstruct(*(obj for obj, _ in loaded))
        name = "Imported_Marabou_Native_Relu_Sequence"
        self.assertEqual(adapter.render_theory(name, replay, *(h for _, h in loaded)),
                         (ISABELLE / (name + ".thy")).read_text())
        self.assertEqual((replay.before.n, replay.after.source.n, replay.after.instance.n), (6, 8, 13))
        self.assertEqual(replay.introductions,
                         (adapter.Introduction(0, 1, 6, Fraction(-2)),
                          adapter.Introduction(2, 3, 7, Fraction(-2))))
        self.assertEqual(replay.after.source.relu_metadata, ((0, 1, 6), (2, 3, 7)))
        self.assertEqual(replay.after.steps, tuple((i, 8 + i) for i in range(5)))
        self.assertEqual(len(replay.before.equations), 3)
        self.assertEqual(len(replay.after.source.equations), 5)
        cert = replay.after.certificate
        for pair in ((0, 1), (2, 3)):
            self.assertIsInstance(cert, proof.LinearBound)
            self.assertIsInstance(cert.child, proof.ReluUpper)
            self.assertEqual((cert.child.x, cert.child.y), pair)
            cert = cert.child.child
        self.assertIsInstance(cert, proof.Leaf)

    def test_run_has_two_native_calls_and_two_solver_generated_lemmas(self):
        report = json.loads((FIXTURES / (STEM + "_run.json")).read_text())
        for field in ("snapshot_before_relu_introduction", "source_snapshot_before_initialization",
                      "introduction_list_before_solve", "proof_production", "initialization_succeeded",
                      "initial_snapshot_matches_tableau_and_ground_bounds",
                      "relu_phase_unfixed_before_solve"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi", "solve_return"):
            self.assertFalse(report[field], field)
        for field, value in (("native_relu_introductions", 2), ("variables_before_relu_introduction", 6),
                             ("input_variables", 8), ("processed_variables", 13),
                             ("proposed_introductions", 5), ("relu_constraints", 2),
                             ("plc_lemmas_before_solve", 0), ("plc_lemmas_after_solve", 2),
                             ("explained_leaves", 1), ("delegated_leaves", 0),
                             ("root_children", 0), ("exit_code", "UNSAT")):
            self.assertEqual(report[field], value, field)
        self.assertGreater(report["main_loop_iterations"], 0)

    def test_sequence_provenance_hashes(self):
        provenance = json.loads((FIXTURES / (STEM + "_provenance.json")).read_text())
        for key, path in (
            ("before_relu_query_sha256", FIXTURES / (STEM + "_before_relu.json")),
            ("relu_introduction_sequence_sha256", FIXTURES / (STEM + "_relu_steps.json")),
            ("relu_sequence_importer_sha256", ISABELLE / "tools/import_marabou_relu_sequence.py"),
        ):
            self.assertEqual(provenance[key], hashlib.sha256(path.read_bytes()).hexdigest())

    def test_empty_sequence_on_linear_capture(self):
        after, steps, query, evidence = [
            proof.load_json(FIXTURES / ("solver_linear" + suffix))[0]
            for suffix in SUFFIXES[2:]]
        before = copy.deepcopy(after)
        before["format"] = "marabou-plain-relu-query-v1"
        replay = adapter.reconstruct(before, {"format": "marabou-relu-aux-sequence-v1", "steps": []},
                                     after, steps, query, evidence)
        self.assertEqual(replay.introductions, ())
        self.assertEqual(replay.before, replay.after.source)

    def test_singleton_matches_earlier_native_capture(self):
        before, step, after, steps, query, evidence = [
            proof.load_json(FIXTURES / ("solver_relu_intro" + suffix))[0]
            for suffix in ("_before_relu.json", "_relu_step.json", *SUFFIXES[2:])]
        del step["format"]
        replay = adapter.reconstruct(before, {"format": "marabou-relu-aux-sequence-v1", "steps": [step]},
                                     after, steps, query, evidence)
        self.assertEqual(replay.introductions, (adapter.Introduction(0, 1, 4, Fraction(-2)),))

    def test_step_order_need_not_equal_constraint_order(self):
        inputs = bundle()
        entries = inputs[1]["steps"]
        entries.reverse()
        entries[0]["auxiliary"], entries[1]["auxiliary"] = 6, 7
        after = source.parse_source(inputs[2])
        def swap_aux(equation):
            return replace(equation, terms=tuple(
                (c, 13 - v if v in (6, 7) else v) for c, v in equation.terms))
        after = replace(after, equations=after.equations[:-2] + tuple(
            swap_aux(e) for e in reversed(after.equations[-2:])),
            relu_metadata=((0, 1, 7), (2, 3, 6)))
        result = adapter.check_introductions(inputs[1], source.parse_source(inputs[0], plain_relu=True), after)
        self.assertEqual(tuple((s.x, s.y, s.auxiliary) for s in result), ((2, 3, 6), (0, 1, 7)))

    def test_reject_empty_partial_or_extra_sequence_for_two_relus(self):
        for count in (0, 1, 3, proof.MAX_VARS + 1):
            inputs = bundle()
            inputs[1]["steps"] = (inputs[1]["steps"] * (count + 1))[:count]
            self.rejects(inputs)

    def test_reject_late_reuse_of_first_auxiliary(self):
        inputs = bundle()
        inputs[1]["steps"][1]["auxiliary"] = 6
        self.rejects(inputs, "not fresh")

    def test_reject_reuse_of_original_variable(self):
        for step in (0, 1):
            inputs = bundle()
            inputs[1]["steps"][step]["auxiliary"] = 4
            self.rejects(inputs, "not fresh")

    def test_reject_skipped_or_swapped_native_allocations(self):
        inputs = bundle()
        inputs[1]["steps"][0]["auxiliary"] = 7
        self.rejects(inputs, "native allocation")
        inputs = bundle()
        inputs[1]["steps"].reverse()
        self.rejects(inputs, "native allocation")

    def test_reject_repeated_relu_even_with_a_different_fresh_auxiliary(self):
        inputs = bundle()
        inputs[1]["steps"][1].update(input=0, output=1)
        self.rejects(inputs, "already introduced")

    def test_reject_absent_reversed_or_wrong_second_relu(self):
        for pair in ((3, 2), (0, 3), (6, 3)):
            inputs = bundle()
            inputs[1]["steps"][1].update(input=pair[0], output=pair[1])
            self.rejects(inputs, "selected plain ReLU")

    def test_reject_false_finite_premise_at_either_step(self):
        for step in (0, 1):
            inputs = bundle()
            inputs[1]["steps"][step]["lower"] = Fraction(-2) + Fraction(1, 10**20)
            self.rejects(inputs, "lower bound is absent")

    def test_reject_inexact_or_missing_finite_premise(self):
        for value in (None, -2.0, True, "-2", float("inf")):
            inputs = bundle()
            inputs[1]["steps"][1]["lower"] = value
            self.rejects(inputs, "exact JSON number")
        inputs = bundle()
        del inputs[1]["steps"][1]["lower"]
        self.rejects(inputs)

    def test_reject_noninteger_step_indices(self):
        for field in ("input", "output", "auxiliary"):
            for value in (True, Fraction(2), "2", -1, proof.MAX_VARS + 1):
                inputs = bundle()
                inputs[1]["steps"][1][field] = value
                with self.subTest(field=field, value=value):
                    self.rejects(inputs)

    def test_reject_unknown_schemas_or_fields(self):
        for i, field, value in ((0, "format", "marabou-source-query-v1"),
                                (1, "format", "marabou-relu-aux-sequence-v2"),
                                (1, "trusted", True)):
            inputs = bundle()
            inputs[i][field] = value
            self.rejects(inputs)
        for field in ("upper", "result", "format"):
            inputs = bundle()
            inputs[1]["steps"][1][field] = 0
            self.rejects(inputs)

    def test_reject_modified_before_atoms(self):
        for field in ("equation", "bound", "relu"):
            inputs = bundle()
            if field == "equation":
                inputs[0]["equations"][2]["scalar"] = 1
            elif field == "bound":
                inputs[0]["lowerBounds"][5] = 0
            else:
                inputs[0]["constraints"].pop()
            self.rejects(inputs)

    def test_reject_altered_result_of_either_introduction(self):
        for row in (3, 4):
            inputs = bundle()
            inputs[2]["equations"][row]["addends"][-1]["val"] = 1
            self.rejects(inputs, "independent after query")
        for variable in (6, 7):
            for field, value in (("lowerBounds", -1), ("upperBounds", 1)):
                inputs = bundle()
                inputs[2][field][variable] = value
                self.rejects(inputs, "independent after query")

    def test_reject_altered_old_atoms_or_metadata_in_after_snapshot(self):
        for field in ("equation", "bound", "metadata"):
            inputs = bundle()
            if field == "equation":
                inputs[2]["equations"][0]["scalar"] = 1
            elif field == "bound":
                inputs[2]["upperBounds"][0] = 0
            else:
                inputs[2]["constraints"][0]["vars"][2] = 7
            self.rejects(inputs, "independent after query")

    def test_reject_stronger_cap_even_with_matching_later_snapshots(self):
        inputs = bundle()
        for i in (2, 4, 5):
            inputs[i]["upperBounds"][7] = 1
        self.rejects(inputs, "independent after query")

    def test_reject_missing_or_colliding_tableau_steps_after_relu_sequence(self):
        for change in ("missing", "collision"):
            inputs = bundle()
            if change == "missing":
                inputs[3]["steps"].pop()
            else:
                inputs[3]["steps"][0]["variable"] = 7
            self.rejects(inputs)

    def test_reject_processed_or_proof_header_substitution(self):
        for i in (4, 5):
            inputs = bundle()
            inputs[i]["lowerBounds"][5] = 0
            self.rejects(inputs)

    def test_reject_corruption_of_either_relu_lemma_or_leaf(self):
        for step in (0, 1):
            inputs = bundle()
            inputs[5]["proof"]["lemmas"][step]["bound"] = -1
            self.rejects(inputs, "too strong")
            inputs = bundle()
            inputs[5]["proof"]["lemmas"][step]["expl"][0]["val"] = 0
            self.rejects(inputs)
        inputs = bundle()
        for term in inputs[5]["proof"]["contradiction"]:
            term["val"] = 0
        self.rejects(inputs)

    def test_reject_omitting_either_necessary_relu_lemma(self):
        for step in (0, 1):
            inputs = bundle()
            inputs[5]["proof"]["lemmas"].pop(step)
            self.rejects(inputs)

    def test_observed_output_lower_to_auxiliary_rule_now_replays(self):
        loaded = load_bundle(FIXTURES / "rejected_relu_chain")
        inputs = [obj for obj, _ in loaded]
        self.assertEqual(len(inputs[5]["proof"]["lemmas"]), 4)
        last = inputs[5]["proof"]["lemmas"][-1]
        self.assertEqual((last["affVar"], last["causVar"], last["causBound"]), (7, 3, "L"))
        cert = adapter.reconstruct(*inputs).after.certificate
        output_rules = []
        while not isinstance(cert, proof.Leaf):
            if isinstance(cert, proof.ReluOutputAuxUpper):
                output_rules.append(cert)
            cert = cert.child
        self.assertEqual(len(output_rules), 1)
        self.assertEqual((output_rules[0].x, output_rules[0].y, output_rules[0].auxiliary,
                          output_rules[0].output_lower, output_rules[0].auxiliary_upper),
                         (2, 3, 7, Fraction(1, 4), 0))

    def test_relaxed_sat_queries_cannot_replay_the_old_proof(self):
        inputs = bundle()
        for i in (0, 2, 4, 5):
            inputs[i]["lowerBounds"][5] = 0
        values = (Fraction(-1, 2), 0, Fraction(-1, 2), 0, Fraction(-1, 2), 0,
                  Fraction(1, 2), Fraction(1, 2), 0, 0, 0, 0, 0)
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
        self.rejects(inputs, "exact constant")

    def test_cli_preserves_all_inputs_and_existing_root(self):
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
            self.assertIn("check_after_relu_aux_sequence_sound", output.read_text())
            self.assertIn("quick_and_dirty = false", (output.parent / "ROOT").read_text())
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                adapter.main(arguments + ["--output", str(output), "--session"])

    def test_render_rejects_name_and_digest_injection(self):
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


if __name__ == "__main__":
    unittest.main()
