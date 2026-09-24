#!/usr/bin/env python3
"""Exact query text fixtures: regeneration, byte identity with HOL, exporter strictness."""
import contextlib
from fractions import Fraction
import hashlib
import io
from pathlib import Path
import re
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import exact_query_text as exporter
import import_marabou_json as proof
import import_marabou_source as source

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
THEORY = ISABELLE / (exporter.THEORY + ".thy")


def theory_bytes(text, scenario):
    match = re.search(rf'"solver_{scenario}_text = \[([0-9,\s]*)\]"', text)
    return bytes(int(b) for b in match.group(1).replace("\n", " ").split(","))


class ExactQueryTextTests(unittest.TestCase):
    def test_fixture_texts_match_regeneration(self):
        texts = exporter.fixture_texts(FIXTURES)
        self.assertEqual(len(texts), 10)
        for scenario, data in texts.items():
            with self.subTest(scenario=scenario):
                self.assertEqual((FIXTURES / f"solver_{scenario}.mqx").read_bytes(), data)

    def test_theory_matches_regeneration(self):
        texts = exporter.fixture_texts(FIXTURES)
        self.assertEqual(exporter.render_theory(texts), THEORY.read_text())

    def test_theory_literals_are_the_file_bytes(self):
        text = THEORY.read_text()
        for scenario, *_ in exporter.SCENARIOS:
            data = (FIXTURES / f"solver_{scenario}.mqx").read_bytes()
            with self.subTest(scenario=scenario):
                self.assertEqual(theory_bytes(text, scenario), data)
                self.assertIn(f"({len(data)} bytes, SHA-256 {hashlib.sha256(data).hexdigest()})", text)

    def test_every_scenario_theorem_is_stated_about_decoded_bytes(self):
        text = THEORY.read_text()
        for scenario, _, theory, constant, kind in exporter.SCENARIOS:
            name = f"solver_{scenario}_text"
            with self.subTest(scenario=scenario):
                self.assertIn(f'"decode_query {name} = Some {theory}.{constant}"\n  by code_simp', text)
                suffix = "unsatisfiable" if kind == "unsat" else "model"
                self.assertIn(f"theorem {name}_{suffix}:", text)
        self.assertEqual(sum(kind == "sat" for *_, kind in exporter.SCENARIOS), 1)

    def test_texts_are_canonical_ascii(self):
        for path in sorted(FIXTURES.glob("solver_*.mqx")):
            data = path.read_bytes()
            with self.subTest(path=path.name):
                self.assertTrue(data.startswith(exporter.HEADER + b"\n") and data.endswith(b"\n"))
                self.assertTrue(all(b == 10 or 32 <= b < 127 for b in data))
                lines = data.split(b"\n")[1:-1]
                self.assertTrue(lines and all(line and b"  " not in line and not line.endswith(b" ")
                                              for line in lines))

    def test_encoder_mirrors_hol_encode_query_example(self):
        # Exact_Query_Format_Examples.encode_sat_rat_query states the HOL side.
        src = source.Source(2, (source.Equation(((1, 0), (1, 1)), Fraction(2)),),
                            (proof.Bound(0, "L", Fraction(-1)), proof.Bound(0, "U", Fraction(1))),
                            ((0, 1),))
        self.assertEqual(exporter.encode(src),
                         b"marabou-exact-query-v1\neq 1 x0 1 x1 = 2\nlower x0 -1\nupper x0 1\nrelu x0 x1\n")

    def test_exact_values_and_fractions(self):
        src = source.Source(1, (source.Equation(((Fraction(-3, 4), 0),), Fraction(1, 10)),),
                            (proof.Bound(0, "L", Fraction(-2, 4)),), ())
        self.assertEqual(exporter.encode(src),
                         b"marabou-exact-query-v1\neq -3/4 x0 = 1/10\nlower x0 -1/2\n")

    def test_changed_json_value_changes_the_text(self):
        obj, _ = proof.load_json(FIXTURES / "solver_relu_chain_before_relu.json")
        original = exporter.encode(exporter.load_query(obj))
        obj["upperBounds"][4] = Fraction(-1, 4)
        changed = exporter.encode(exporter.load_query(obj))
        self.assertNotEqual(original, changed)
        self.assertIn(b"upper x4 -1/4\n", changed)

    def test_unsupported_json_is_rejected(self):
        processed, _ = proof.load_json(FIXTURES / "solver_relu_chain_query.json")
        with self.assertRaisesRegex(proof.ImportFailure, "unsupported query format"):
            exporter.load_query(processed)
        obj, _ = proof.load_json(FIXTURES / "solver_relu_chain_before_relu.json")
        obj["format"] = "marabou-source-query-v1"
        with self.assertRaisesRegex(proof.ImportFailure, "source ReLU"):
            exporter.load_query(obj)

    def test_cli_arguments_are_strict(self):
        query = str(FIXTURES / "solver_relu_chain_before_relu.json")
        with tempfile.TemporaryDirectory() as tmp:
            for argv in (["--query", query, "--output", str(Path(tmp) / "q.txt")],
                         ["--query", query],
                         ["--fixtures", tmp, "--query", query]):
                with self.subTest(argv=argv), contextlib.redirect_stderr(io.StringIO()):
                    with self.assertRaises(SystemExit) as raised:
                        exporter.main(argv)
                    self.assertEqual(raised.exception.code, 1)
            output = Path(tmp) / "chain.mqx"
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(exporter.main(["--query", query, "--output", str(output)]), 0)
            self.assertEqual(output.read_bytes(), (FIXTURES / "solver_relu_chain.mqx").read_bytes())


if __name__ == "__main__":
    unittest.main()
