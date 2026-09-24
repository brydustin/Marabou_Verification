#!/usr/bin/env python3
"""Native preprocessing: record parsing, re-derived facts, projection, tampering."""
import contextlib
import copy
from fractions import Fraction
import io
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import capture_marabou_solver as driver
import exact_query_text as text
import import_marabou_json as proof
import import_marabou_preprocessing as pre
import import_marabou_query_file as adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
B = proof.Bound


def data(example):
    return (ISABELLE / "examples" / (example + ".mqx")).read_bytes()


def loaded(example):
    return adapter.load_artifacts(FIXTURES / ("file_" + example))


def result(example, artifacts=None, file_bytes=None):
    return adapter.reconstruct(file_bytes or data(example), artifacts or loaded(example)).replay


class ExampleTests(unittest.TestCase):
    def test_each_example_takes_its_route(self):
        expected = {"preprocess_split_unsat": "unsat", "preprocess_eliminate_unsat": "unsat",
                    "preprocess_inequality_unsat": "infeasible", "preprocess_mixed_sat": "sat"}
        self.assertEqual({e for e, _ in adapter.PREPROCESSED_EXAMPLES}, set(expected))
        for example, kind in expected.items():
            with self.subTest(example=example):
                self.assertEqual(result(example).kind, kind)

    def test_elimination_example_merges_fixes_and_renumbers(self):
        record = loaded("preprocess_eliminate_unsat")["preprocessing"][0]
        kinds = {tuple(sorted(set(entry) - {"old"}))[0] for entry in record["variables"]}
        self.assertEqual(kinds, {"new", "merged", "fixed"})
        r = result("preprocess_eliminate_unsat")
        self.assertEqual(len(r.sigma), record["preprocessed_variables"])
        eliminated = {e["old"] for e in record["variables"] if "new" not in e}
        # The ReLU input x0 is merged into its copy x9, and x10 is fixed.
        self.assertEqual(eliminated, {0, 10})
        self.assertFalse(eliminated & set(r.sigma))
        self.assertEqual(r.sigma[-1], 11)   # the native ReLU auxiliary, renumbered
        (x, y, wx, wy), = r.links
        self.assertEqual((x, y, len(wx), wy), (0, 1, 2, ()))   # x0 = x9 needs a proof

    def test_native_slacks_and_auxiliaries_are_introduced_in_native_order(self):
        r = result("preprocess_inequality_unsat")
        self.assertEqual(r.slack_steps, ((0, 3), (1, 4)))
        self.assertEqual(r.relu_steps, ((1, 2, 5, None),))
        variable, lower, upper = r.crossing
        self.assertGreater(lower, upper)
        r = result("preprocess_mixed_sat")
        self.assertEqual([s for _, s in r.slack_steps], [4, 5])

    def test_generated_theories_state_the_chain(self):
        for example, replay in adapter.PREPROCESSED_EXAMPLES:
            theory = (ISABELLE / (replay + ".thy")).read_text()
            with self.subTest(example=example):
                if example.endswith("sat") and not example.endswith("unsat"):
                    self.assertIn("imported_file_query_model", theory)
                else:
                    self.assertIn("check_projection imported_introduced_query imported_projection", theory)
                    self.assertIn("theorem imported_file_query_unsatisfiable", theory)


class RecordTests(unittest.TestCase):
    def test_malformed_records_are_rejected(self):
        base = loaded("preprocess_eliminate_unsat")["preprocessing"][0]
        decoded = text.decode(data("preprocess_eliminate_unsat"))
        _, n, slacks, relus, _ = pre.introductions(decoded)
        pre.parse_map(base, n, len(slacks), len(relus))
        mutations = []
        for key, value in (("format", "other"), ("input_variables", n + 1), ("slacks", 1),
                           ("relu_auxiliaries", 0), ("result", "maybe"), ("preprocessed_variables", 0),
                           ("variables", [])):
            record = copy.deepcopy(base)
            record[key] = value
            mutations.append(record)
        record = copy.deepcopy(base)
        record["variables"][0] = {"old": 1, "new": 0}
        mutations.append(record)
        record = copy.deepcopy(base)
        news = [e for e in record["variables"] if "new" in e]
        news[1]["new"] = news[0]["new"]
        mutations.append(record)
        record = copy.deepcopy(base)
        record["variables"][0]["extra"] = 1
        mutations.append(record)
        record = copy.deepcopy(base)
        record["result"] = "infeasible"
        mutations.append(record)
        for record in mutations:
            with self.subTest(record=record), self.assertRaises(proof.ImportFailure):
                pre.parse_map(record, n, len(slacks), len(relus))


class TamperingTests(unittest.TestCase):
    def test_unimplied_preprocessed_bounds_are_rejected(self):
        # Native tolerances could snap or round a bound; the exact check refuses it.
        for example in ("preprocess_split_unsat", "preprocess_eliminate_unsat"):
            artifacts = loaded(example)
            artifacts["source"][0]["upperBounds"][3] = Fraction(1, 2)
            with self.subTest(example=example), self.assertRaises(proof.ImportFailure):
                result(example, artifacts)

    def test_wrong_renaming_is_rejected(self):
        artifacts = loaded("preprocess_eliminate_unsat")
        entries = [e for e in artifacts["preprocessing"][0]["variables"] if "new" in e]
        entries[0]["new"], entries[1]["new"] = entries[1]["new"], entries[0]["new"]
        with self.assertRaisesRegex(proof.ImportFailure, "not exactly implied|no original counterpart"):
            result("preprocess_eliminate_unsat", artifacts)

    def test_weakened_but_implied_file_is_still_proved(self):
        # Other rows already bound x3 by 3/4, so the checked chain still holds.
        weaker = data("preprocess_split_unsat").replace(b"upper x3 1\n", b"upper x3 2\n")
        self.assertEqual(result("preprocess_split_unsat", file_bytes=weaker).kind, "unsat")

    def test_changed_file_is_rejected(self):
        for example, old, new in (("preprocess_split_unsat", b"relu x0 x1\n", b""),
                                  ("preprocess_eliminate_unsat", b"upper x10 1/4\n", b"upper x10 1/2\n"),
                                  ("preprocess_inequality_unsat", b"<= -1\n", b"<= 0\n"),
                                  ("preprocess_mixed_sat", b"<= 3/2\n", b"<= 1/2\n")):
            changed = data(example).replace(old, new)
            self.assertNotEqual(changed, data(example))
            with self.subTest(example=example), self.assertRaises(proof.ImportFailure):
                result(example, file_bytes=changed)

    def test_artifact_sets_are_strict(self):
        artifacts = loaded("preprocess_split_unsat")
        del artifacts["certificate"]
        with self.assertRaises(proof.ImportFailure):
            result("preprocess_split_unsat", artifacts)
        artifacts = loaded("preprocess_inequality_unsat")
        artifacts["source"] = loaded("preprocess_split_unsat")["source"]
        with self.assertRaisesRegex(proof.ImportFailure, "unexpected or missing artifacts"):
            result("preprocess_inequality_unsat", artifacts)

    def test_perturbed_assignment_is_rejected(self):
        artifacts = loaded("preprocess_mixed_sat")
        entry = artifacts["assignment"][0]["values"][1]
        entry["value"], entry["hex"] = Fraction(3), "0x1.8p+1"
        with self.assertRaisesRegex(proof.ImportFailure, "not an exact model"):
            result("preprocess_mixed_sat", artifacts)


class DerivationTests(unittest.TestCase):
    def test_bound_facts_carry_exact_witnesses(self):
        q = pre.HQuery((pre.Atom("EQ", ((Fraction(1), 0), (Fraction(1), 1)), Fraction(1)),),
                       (B(0, "L", Fraction(0)), B(0, "U", Fraction(1, 4)), B(1, "L", Fraction(0)),
                        B(1, "U", Fraction(2))), ())
        d = pre.Deriver(q, {}).run()
        self.assertIn(B(1, "L", Fraction(3, 4)), d.q.bounds)
        self.assertIn(B(1, "U", Fraction(1)), d.q.bounds)
        for fact in d.facts:
            self.assertEqual(fact.kind, "Bound")

    def test_forged_facts_are_rejected(self):
        q = pre.HQuery((), (B(0, "L", Fraction(0)), B(0, "U", Fraction(1))), ((0, 1),))
        for fact in (pre.Fact("Bound", (B(0, "U", Fraction(1, 2)), (0, 1))),
                     pre.Fact("Hull", (1, 0)),
                     pre.Fact("Phase_Active", (0, 1, B(0, "L", Fraction(-1, 10 ** 12)), (0, 0, 1, 0))),
                     pre.Fact("Relu_Upper", (0, 1, Fraction(1), Fraction(1, 2)))):
            with self.subTest(fact=fact), self.assertRaises(proof.ImportFailure):
                pre.apply_fact(q, fact)

    def test_narrow_interval_is_not_snapped(self):
        # x0 in [0, 1e-6], x1 = x0 >= 1e-6: exact propagation fixes x0 = 1e-6.
        tiny = Fraction(1, 10 ** 6)
        q = pre.HQuery((pre.Atom("EQ", ((Fraction(1), 0), (Fraction(-1), 1)), Fraction(0)),),
                       (B(0, "L", Fraction(0)), B(0, "U", tiny), B(1, "L", tiny), B(1, "U", Fraction(1))), ())
        d = pre.Deriver(q, {}).run()
        self.assertIsNone(d.crossing())
        snapped = pre.HQuery(q.linear, (B(0, "L", Fraction(0)), B(0, "U", Fraction(0)),
                                        B(1, "L", tiny), B(1, "U", Fraction(1))), ())
        with self.assertRaisesRegex(proof.ImportFailure, "not exactly implied"):
            pre.projection_rows(d.q, snapped, (0, 1))


class PipelineTests(unittest.TestCase):
    def test_preprocessing_relaxes_only_the_bound_requirement(self):
        unbounded = data("preprocess_inequality_unsat")
        with self.assertRaisesRegex(proof.ImportFailure, "needs finite lower and upper bounds"):
            adapter.check_pipeline_support(unbounded)
        self.assertEqual(len(adapter.check_pipeline_support(unbounded, native_preprocessing=True).linear), 2)
        with self.assertRaisesRegex(proof.ImportFailure, "not exactly a binary double"):
            adapter.check_pipeline_support(unbounded.replace(b">= 3", b">= 0.1"), native_preprocessing=True)

    def test_preprocess_needs_a_query_file(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            driver.main(["--preprocess", "--output", "/nonexistent/out"])
        self.assertEqual(raised.exception.code, 2)

    def test_run_reports_name_the_preprocessing_mode(self):
        for example, _ in adapter.PREPROCESSED_EXAMPLES:
            report = (FIXTURES / f"file_{example}_run.json").read_text()
            with self.subTest(example=example):
                self.assertIn('"scenario": "file-preprocess"', report)
                self.assertIn('"preprocessing": true', report)


if __name__ == "__main__":
    unittest.main()
