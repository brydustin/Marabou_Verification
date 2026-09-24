#!/usr/bin/env python3
"""Source/step binding and adversarial import tests; ROOT checks the HOL proofs."""
import contextlib
import copy
from fractions import Fraction
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as proof
import import_marabou_source as adapter


ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
SCENARIOS = ("linear", "relu", "relu_aux", "relu_aux_active", "relu_aux_inactive", "relu_split")
SUFFIXES = ("_source.json", "_steps.json", "_query.json", ".json")


def load_bundle(scenario="relu_split"):
    return [proof.load_json(FIXTURES / ("solver_" + scenario + suffix))
            for suffix in SUFFIXES]


def bundle(scenario="relu_split"):
    return [obj for obj, _ in load_bundle(scenario)]


class SourceImportTests(unittest.TestCase):
    def rejects(self, inputs, message=None):
        with self.assertRaisesRegex(proof.ImportFailure, message or "."):
            adapter.reconstruct(*inputs)

    def test_all_captured_sources_replay_and_regenerate(self):
        for scenario in SCENARIOS:
            with self.subTest(scenario=scenario):
                loaded = load_bundle(scenario)
                replay = adapter.reconstruct(*(obj for obj, _ in loaded))
                name = "Imported_Marabou_Source_" + scenario.title()
                self.assertEqual(
                    adapter.render_theory(name, replay, *(h for _, h in loaded)),
                    (ISABELLE / (name + ".thy")).read_text())
                report = json.loads((FIXTURES / ("solver_" + scenario + "_run.json")).read_text())
                self.assertTrue(report["source_snapshot_before_initialization"])
                self.assertTrue(report["introduction_list_before_solve"])
                self.assertEqual(replay.source.n, report["input_variables"])
                self.assertEqual(len(replay.source.equations), report["source_rows"])
                self.assertEqual(len(replay.steps), report["proposed_introductions"])

    def test_source_preserves_nonzero_scalars_and_native_term_order(self):
        replay = adapter.reconstruct(*bundle())
        self.assertEqual(replay.source.n, 9)
        self.assertEqual(tuple(e.scalar for e in replay.source.equations),
                         (Fraction(1, 4),) * 4 + (0,))
        self.assertEqual(replay.source.equations[-1].terms, ((1, 1), (-1, 0), (-1, 2)))
        self.assertEqual(replay.column_source.equations[-1].terms, ((-1, 0), (1, 1), (-1, 2)))
        self.assertEqual(replay.steps, ((0, 9), (1, 10), (2, 11), (3, 12), (4, 13)))
        self.assertIsInstance(replay.certificate, proof.Split)
        self.assertIsInstance(replay.certificate.active, proof.Leaf)
        self.assertIsInstance(replay.certificate.inactive, proof.Leaf)

    def test_reject_changed_source_scalar(self):
        inputs = bundle()
        inputs[0]["equations"][0]["scalar"] = Fraction(1, 4) + Fraction(1, 10**20)
        self.rejects(inputs, "independent processed query")

    def test_reject_changed_source_coefficient(self):
        inputs = bundle()
        inputs[0]["equations"][-1]["addends"][0]["val"] = -1
        self.rejects(inputs, "independent processed query")

    def test_reject_changed_source_bounds(self):
        for field in ("lowerBounds", "upperBounds"):
            inputs = bundle()
            inputs[0][field][0] = 0
            with self.subTest(field=field):
                self.rejects(inputs, "independent processed query")

    def test_reject_removed_source_equation(self):
        inputs = bundle()
        inputs[0]["equations"].pop()
        self.rejects(inputs)

    def test_reject_removed_or_reversed_source_relu(self):
        for change in ("remove", "reverse"):
            inputs = bundle()
            if change == "remove":
                inputs[0]["constraints"] = []
            else:
                inputs[0]["constraints"][0]["vars"] = [1, 0, 2]
            with self.subTest(change=change):
                self.rejects(inputs, "independent processed query")

    def test_reject_different_auxiliary_metadata(self):
        inputs = bundle()
        inputs[0]["constraints"][0]["vars"][2] = 3
        self.rejects(inputs, "metadata differ")

    def test_reject_empty_or_partial_introductions(self):
        for count in (0, 1, 4):
            inputs = bundle()
            inputs[1]["steps"] = inputs[1]["steps"][:count]
            with self.subTest(count=count):
                self.rejects(inputs)

    def test_reject_extra_introduction(self):
        inputs = bundle()
        inputs[1]["steps"].append({"equation": 0, "variable": 9})
        self.rejects(inputs, "not fresh")

    def test_reject_reuse_of_earlier_auxiliary(self):
        inputs = bundle()
        inputs[1]["steps"][-1]["variable"] = 9
        self.rejects(inputs, "not fresh")

    def test_reject_overwriting_original_variable(self):
        inputs = bundle()
        inputs[1]["steps"][0]["variable"] = 8
        self.rejects(inputs, "not fresh")

    def test_reject_wrong_or_stale_equation_selection(self):
        for index in (0, 5, -1):
            inputs = bundle()
            inputs[1]["steps"][-1]["equation"] = index
            with self.subTest(index=index):
                self.rejects(inputs)

    def test_reject_swapped_fresh_variables(self):
        inputs = bundle()
        inputs[1]["steps"][0]["variable"] = 10
        inputs[1]["steps"][1]["variable"] = 9
        self.rejects(inputs, "independent processed query")

    def test_reject_stronger_processed_query_even_with_matching_proof_header(self):
        inputs = bundle()
        inputs[2]["lowerBounds"][0] = inputs[3]["lowerBounds"][0] = 0
        self.rejects(inputs, "independent processed query")

    def test_reject_proof_header_substitution_after_valid_bridge(self):
        inputs = bundle()
        inputs[3]["lowerBounds"][0] = 0
        self.rejects(inputs, "certificate header does not match")

    def test_reject_corruption_of_either_proof_child_after_valid_bridge(self):
        for child in (0, 1):
            inputs = bundle()
            inputs[3]["proof"]["children"][child]["contradiction"][0]["val"] = 0
            with self.subTest(child=child):
                self.rejects(inputs)

    def test_relaxed_source_processed_and_header_still_need_valid_proof(self):
        # Exact model after relaxation: x=y=0 and scalar-fixed auxiliary z=0.
        # The introduction matches, but the old contradiction no longer holds.
        inputs = bundle("linear")
        for query in (inputs[0], inputs[2], inputs[3]):
            query["lowerBounds"][1] = 0
        self.rejects(inputs, "exact constant")

    def test_source_addend_permutation_is_preserved_for_hol_proof(self):
        inputs = bundle()
        inputs[0]["equations"][0]["addends"].reverse()
        replay = adapter.reconstruct(*inputs)
        self.assertNotEqual(replay.source.equations[0], replay.column_source.equations[0])
        self.assertEqual(replay.column_source, adapter.reconstruct(*bundle()).column_source)

    def test_schema_version_and_unknown_fields_are_rejected(self):
        for file_index, field, value in (
            (0, "format", "marabou-source-query-v2"),
            (1, "format", "marabou-fixed-aux-sequence-v2"),
            (0, "assumed_equations", []), (1, "trusted", True),
        ):
            inputs = bundle()
            inputs[file_index][field] = value
            with self.subTest(file=file_index, field=field):
                self.rejects(inputs)
        inputs = bundle()
        inputs[1]["steps"][0]["scalar"] = Fraction(1, 4)
        self.rejects(inputs, "unknown")

    def test_noninteger_and_out_of_range_dimensions_or_step_indices(self):
        for value in (True, Fraction(9), "9", -1, 0, proof.MAX_VARS + 1):
            inputs = bundle()
            inputs[0]["variables"] = value
            with self.subTest(dimension=value):
                self.rejects(inputs)
        for field in ("equation", "variable"):
            for value in (True, Fraction(1), "1", -1, proof.MAX_VARS + 1):
                inputs = bundle()
                inputs[1]["steps"][0][field] = value
                with self.subTest(field=field, index=value):
                    self.rejects(inputs)

    def test_source_sparse_and_bound_shape_rejections(self):
        for change in ("duplicate", "out_of_range", "missing_bound", "extra_bound"):
            inputs = bundle()
            terms = inputs[0]["equations"][0]["addends"]
            if change == "duplicate":
                terms.append(copy.deepcopy(terms[0]))
            elif change == "out_of_range":
                terms[0]["var"] = 9
            elif change == "missing_bound":
                inputs[0]["lowerBounds"].pop()
            else:
                inputs[0]["upperBounds"].append(1)
            with self.subTest(change=change):
                self.rejects(inputs)

    def test_source_rejects_unsupported_equations_and_constraints(self):
        inputs = bundle()
        inputs[0]["equations"][0]["type"] = "LE"
        self.rejects(inputs, "equalities")
        for variables in ([0, 1], [0, 1, 1], [0, 1, 2, 3]):
            inputs = bundle()
            inputs[0]["constraints"][0]["vars"] = variables
            with self.subTest(variables=variables):
                self.rejects(inputs, "distinct")
        inputs = bundle()
        inputs[0]["constraints"][0]["constraintType"] = True
        self.rejects(inputs)

    def test_source_values_must_be_exact_numbers(self):
        for value in (0.25, True, "1/4", None, float("nan"), float("inf")):
            inputs = bundle()
            inputs[0]["equations"][0]["scalar"] = value
            with self.subTest(value=value):
                self.rejects(inputs, "exact JSON number")

    def test_cli_and_input_overwrite_guards(self):
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / (f"Input{i}.thy") for i in range(4)]
            for path, suffix in zip(paths, SUFFIXES):
                path.write_bytes((FIXTURES / ("solver_relu_split" + suffix)).read_bytes())
            flags = [item for flag, path in zip(
                ("--source", "--steps", "--query", "--certificate"), paths)
                     for item in (flag, str(path))]
            for path in paths:
                original = path.read_bytes()
                with self.subTest(path=path.name), contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit):
                        adapter.main(flags + ["--output", str(path)])
                self.assertEqual(path.read_bytes(), original)
            output = Path(directory) / "Replay.thy"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(adapter.main(flags + ["--output", str(output), "--session"]), 0)
            self.assertIn("imported_source_query_unsatisfiable", output.read_text())
            self.assertIn("quick_and_dirty = false", (output.parent / "ROOT").read_text())
            with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit):
                adapter.main(flags + ["--output", str(output), "--session"])

    def test_render_rejects_name_or_digest_injection(self):
        loaded = load_bundle()
        replay = adapter.reconstruct(*(obj for obj, _ in loaded))
        hashes = [h for _, h in loaded]
        with self.assertRaises(proof.ImportFailure):
            adapter.render_theory('Replay"\\nend', replay, *hashes)
        for i in range(4):
            corrupt = hashes.copy()
            corrupt[i] = "not a digest"
            with self.subTest(digest=i), self.assertRaises(proof.ImportFailure):
                adapter.render_theory("Replay", replay, *corrupt)


if __name__ == "__main__":
    unittest.main()
