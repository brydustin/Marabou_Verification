#!/usr/bin/env python3
"""Checked local preparation, native captures, original-byte binding and tampering."""
import copy
from dataclasses import replace
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import exact_query_text as text
import import_marabou_json as proof
import import_marabou_query_file as adapter
import prepare_inequalities as prep

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"


def data(result):
    return (ISABELLE / f"examples/inequality_relu_{result}.mqx").read_bytes()


def loaded(result):
    return adapter.load_artifacts(FIXTURES / f"file_inequality_relu_{result}")


class PreparationTests(unittest.TestCase):
    def test_le_ge_sequence_and_witnesses(self):
        original = adapter.check_pipeline_support(data("unsat"))
        query, steps = prep.prepare(original)
        self.assertEqual([(s.index, s.variable, s.cap) for s in steps], [(0, 2, 1), (1, 3, -1)])
        self.assertEqual(steps[0].weights, (1, 0, 0, 1, 0, 0, 0, 0))
        self.assertEqual(steps[1].weights, (0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0))
        self.assertEqual(prep.replay(original, prep.parse_record(prep.record(steps))), query)
        self.assertEqual(adapter.check_pipeline_support(prep.encode(query), equality_only=True), query)
        self.assertEqual(query.linear[0][1][-1], (1, 2))
        self.assertEqual(query.linear[1][1][-1], (1, 3))

    def test_mixed_signs_choose_correct_interval_endpoints(self):
        original = text.decode(data("unsat"))
        for kind, expected in (("LE", 11), ("GE", -3)):
            q = replace(original, linear=((kind, ((Fraction(2), 0), (Fraction(-3), 1)), Fraction(1)),))
            _, steps = prep.prepare(q)
            self.assertEqual(steps[0].cap, expected)

    def test_already_contradictory_interval_weakens_cap_to_zero(self):
        original = text.decode(data("unsat"))
        for kind, rhs in (("LE", -3), ("GE", 3)):
            q = replace(original, linear=((kind, ((Fraction(1), 0),), Fraction(rhs)),))
            _, steps = prep.prepare(q)
            self.assertEqual(steps[0].cap, 0)
            prep.replay(q, steps)

    def test_bounds_may_be_weakened_but_not_strengthened(self):
        original = text.decode(data("unsat"))
        _, steps = prep.prepare(original)
        prep.apply_step(original, replace(steps[0], cap=2))
        with self.assertRaisesRegex(proof.ImportFailure, "no exact linear implication"):
            prep.apply_step(original, replace(steps[0], cap=0))
        after_first = prep.apply_step(original, steps[0])
        prep.apply_step(after_first, replace(steps[1], cap=-2))
        with self.assertRaisesRegex(proof.ImportFailure, "no exact linear implication"):
            prep.apply_step(after_first, replace(steps[1], cap=0))

    def test_bad_step_and_late_collision_rejected(self):
        original = text.decode(data("unsat"))
        _, steps = prep.prepare(original)
        for step in (replace(steps[0], variable=0), replace(steps[0], index=9),
                     replace(steps[0], weights=()), replace(steps[0], weights=(-1,) + steps[0].weights[1:]),
                     replace(steps[0], weights=(0,) * len(steps[0].weights))):
            with self.subTest(step=step), self.assertRaises(proof.ImportFailure):
                prep.apply_step(original, step)
        for second in (replace(steps[1], variable=2), replace(steps[1], index=0)):
            with self.subTest(second=second), self.assertRaises(proof.ImportFailure):
                prep.replay(original, (steps[0], second))
        with self.assertRaisesRegex(proof.ImportFailure, "inequalities remain"):
            prep.replay(original, steps[:1])

    def test_strict_evidence_schema(self):
        _, steps = prep.prepare(text.decode(data("unsat")))
        valid = prep.record(steps)
        mutations = []
        for key, value in (("index", True), ("variable", -1), ("cap", 1.0),
                           ("cap", "1/0"), ("cap", "1e2"), ("cap", "nan"),
                           ("weights", ["-"]), ("extra", 0)):
            mutated = copy.deepcopy(valid)
            mutated["steps"][0][key] = value
            mutations.append(mutated)
        mutations += [{"format": prep.FORMAT, "steps": {}, "extra": 0},
                      {"format": "wrong", "steps": []}]
        for mutated in mutations:
            with self.subTest(mutated=mutated), self.assertRaises(proof.ImportFailure):
                prep.parse_record(mutated)

    def test_zero_coefficient_variable_still_counts_for_freshness(self):
        original = text.decode(data("unsat"))
        q = replace(original, linear=(("LE", ((Fraction(0), 9),), Fraction(0)),))
        with self.assertRaisesRegex(proof.ImportFailure, "not fresh"):
            prep.introduce(q, 0, 9)


class NativeBindingTests(unittest.TestCase):
    def test_both_solver_results_replay(self):
        for result in ("sat", "unsat"):
            replay = adapter.reconstruct(data(result), loaded(result))
            self.assertEqual((replay.kind, replay.relus), (result, True))
            self.assertEqual(len(replay.inequality_steps), 2)

    def test_preparation_artifacts_are_mandatory(self):
        for key in ("inequalities", "prepared"):
            artifacts = loaded("unsat")
            del artifacts[key]
            with self.subTest(key=key), self.assertRaisesRegex(proof.ImportFailure, "need both"):
                adapter.reconstruct(data("unsat"), artifacts)
        artifacts = loaded("unsat")
        artifacts["unknown"] = ({}, "")
        with self.assertRaisesRegex(proof.ImportFailure, "unexpected or missing"):
            adapter.reconstruct(data("unsat"), artifacts)

    def test_original_file_mutation_is_rejected(self):
        for old, new in ((b"<= -1", b"<= 0"), (b">= 1", b">= 0"),
                         (b"lower x0 -2", b"lower x0 -3"), (b"relu x0 x1", b"relu x1 x0")):
            with self.subTest(old=old), self.assertRaises(proof.ImportFailure):
                adapter.reconstruct(data("unsat").replace(old, new), loaded("unsat"))

    def test_prepared_file_mutation_is_rejected(self):
        artifacts = loaded("unsat")
        raw, digest = artifacts["prepared"]
        artifacts["prepared"] = (raw.replace(b"upper x2 1", b"upper x2 2"), digest)
        with self.assertRaisesRegex(proof.ImportFailure, "prepared file differs"):
            adapter.reconstruct(data("unsat"), artifacts)

    def test_tampered_cap_or_witness_is_rejected(self):
        for key, value in (("cap", "0"), ("weights", ["0"] * 8), ("variable", 0)):
            artifacts = loaded("unsat")
            artifacts["inequalities"][0]["steps"][0][key] = value
            with self.subTest(key=key), self.assertRaises(proof.ImportFailure):
                adapter.reconstruct(data("unsat"), artifacts)

    def test_native_evidence_and_translation_are_bound_together(self):
        for key in ("before", "source", "query"):
            artifacts = loaded("unsat")
            artifacts[key] = loaded("sat")[key]
            with self.subTest(key=key), self.assertRaises(proof.ImportFailure):
                adapter.reconstruct(data("unsat"), artifacts)
        artifacts = loaded("unsat")
        artifacts["introductions"][0]["steps"][0]["auxiliary"] = 3
        with self.assertRaises(proof.ImportFailure):
            adapter.reconstruct(data("unsat"), artifacts)

    def test_generated_theories_match(self):
        for name, theory in adapter.full_artifact_example_theories(ISABELLE).items():
            with self.subTest(name=name):
                self.assertEqual((ISABELLE / name).read_text(), theory)

    def test_native_provenance_matches_current_inputs(self):
        for result in ("sat", "unsat"):
            prefix = FIXTURES / f"file_inequality_relu_{result}"
            provenance = json.loads(Path(str(prefix) + "_provenance.json").read_text())
            self.assertEqual(provenance["result"], result)
            self.assertEqual(provenance["query_file_sha256"], hashlib.sha256(data(result)).hexdigest())
            for key, (_, digest) in loaded(result).items():
                self.assertEqual(provenance[f"{key}_sha256"], digest)
            for key, filename in (("capture_script", "capture_marabou_solver.py"),
                                  ("query_file_importer", "import_marabou_query_file.py"),
                                  ("inequality_preparer", "prepare_inequalities.py")):
                self.assertEqual(provenance[key + "_sha256"],
                                 hashlib.sha256((ISABELLE / "tools" / filename).read_bytes()).hexdigest())
            for relative, digest in provenance["compiled_sources"].items():
                self.assertEqual(hashlib.sha256((ISABELLE.parent / relative).read_bytes()).hexdigest(), digest)
            for key, suffix in (("run_report", "_run.json"), ("solver_log", ".log")):
                self.assertEqual(provenance[key + "_sha256"],
                                 hashlib.sha256(Path(str(prefix) + suffix).read_bytes()).hexdigest())


if __name__ == "__main__":
    unittest.main()
