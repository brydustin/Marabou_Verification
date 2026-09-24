#!/usr/bin/env python3
"""Native initial-basis records: strict parsing and the generated HOL checks."""
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_initial_basis as bases
import import_marabou_json as proof
import import_marabou_source as source_adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"


def record(stem):
    return proof.load_json(FIXTURES / (stem + "_initial_basis.json"))[0]


def source(stem):
    return source_adapter.parse_source(proof.load_json(FIXTURES / (stem + "_source.json"))[0])


class GeneratedTheoryTests(unittest.TestCase):
    def test_theory_is_current_and_registered(self):
        text = (ISABELLE / (bases.THEORY + ".thy")).read_text(encoding="utf-8")
        self.assertEqual(text, bases.render())
        self.assertIn(f"    {bases.THEORY}\n", (ISABELLE / "ROOT").read_text())
        self.assertEqual(bases.main(["--check"]), 0)

    def test_every_distinct_record_is_checked(self):
        recorded = sorted(p.name[:-len("_initial_basis.json")]
                          for p in FIXTURES.glob("*_initial_basis.json"))
        self.assertEqual(recorded, sorted(bases.RUNS))
        text = bases.render()
        for stem in bases.RUNS:
            with self.subTest(stem=stem):
                self.assertIn(f"lemma {stem}_native_initial_basis:", text)
                self.assertIn("by code_simp", text)

    def test_records_partition_the_variables(self):
        for stem in bases.RUNS:
            with self.subTest(stem=stem):
                src = source(stem)
                basic, nonbasic = bases.parse_basis(record(stem), src)
                self.assertEqual(len(basic), len(src.equations))
                # Native numbers the nonbasics in increasing order.
                self.assertEqual(list(nonbasic), sorted(nonbasic))


class ParsingTests(unittest.TestCase):
    def test_malformed_records_are_rejected(self):
        stem = "solver_relu_split"
        base, src = record(stem), source(stem)
        bases.parse_basis(base, src)
        mutations = []
        for key, value in (("format", "other"), ("source_variables", src.n + 1), ("rows", 0),
                           ("basic", []), ("nonbasic", base["nonbasic"][:-1]),
                           ("source_variables", True)):
            changed = copy.deepcopy(base)
            changed[key] = value
            mutations.append(changed)
        changed = copy.deepcopy(base)
        changed["basic"][0] = changed["nonbasic"][0]
        mutations.append(changed)
        changed = copy.deepcopy(base)
        changed["basic"][0] = src.n + len(src.equations)
        mutations.append(changed)
        changed = copy.deepcopy(base)
        changed["extra"] = 1
        mutations.append(changed)
        for obj in mutations:
            with self.subTest(obj=obj), self.assertRaises(proof.ImportFailure):
                bases.parse_basis(obj, src)

    def test_wrong_orders_are_refuted_in_hol(self):
        # A swapped but well-formed order passes parsing; the HOL example
        # theory proves that the selection does not produce it.
        text = (ISABELLE / "Tableau_Initialization_Examples.thy").read_text(encoding="utf-8")
        self.assertIn("solver_relu_split_source)) \\<noteq>", text)
        swapped = copy.deepcopy(record("solver_relu_split"))
        swapped["basic"][0], swapped["basic"][1] = swapped["basic"][1], swapped["basic"][0]
        bases.parse_basis(swapped, source("solver_relu_split"))

if __name__ == "__main__":
    unittest.main()
