#!/usr/bin/env python3
"""Query-file workflow: pre-checks, capture binding, example theories and provenance."""
import contextlib
import hashlib
import io
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import capture_marabou_solver as driver
import exact_query_text as text
import import_marabou_json as proof
import import_marabou_query_file as adapter

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
EXAMPLES = ISABELLE / "examples"
HEADER = "marabou-exact-query-v1"


def lines(*body):
    return "".join(line + "\n" for line in (HEADER, *body)).encode()


def example(name):
    return (EXAMPLES / (name + ".mqx")).read_bytes()


def scenario_artifacts(scenario):
    return adapter.load_artifacts(FIXTURES / ("solver_" + scenario))


class MirrorDecoderTests(unittest.TestCase):
    """The untrusted mirror must agree with the decisions proved in
    Exact_Query_Format_Examples; it only gives earlier, readable rejections."""

    def test_rejections_proved_in_hol(self):
        rejected = [b"", HEADER.encode(), lines()[:-1], "marabou-exact-query-v2\n".encode(),
                    lines(""), lines("relu  x0 x1"), lines("relu x0 x1 "), lines("RELU x0 x1"),
                    lines("relu x0"), lines("eq 1 x0 <= 0"), lines("eq 1 x0 1 = 0"),
                    lines("lower x 1"), lines("lower x-1 1"), lines("lower y0 1"),
                    lines("lower x0 1/0"), lines("lower x0 1."), lines("lower x0 .5"),
                    lines("lower x0 1e3"), lines("lower x0 +1"), lines("lower x0 --1"),
                    lines("lower x0 1/2/3"), lines("lower x0 1.5/2"), lines("lower x0 -"),
                    HEADER.encode() + b"\r\n", lines() + b"relu x0\tx1\n", lines() + b"lower x0 1\xc8\n"]
        for data in rejected:
            with self.subTest(data=data):
                self.assertIsNone(text.decode(data))

    def test_acceptances_proved_in_hol(self):
        self.assertEqual(text.decode(lines()), text.DecodedQuery((), (), ()))
        decoded = text.decode(lines("relu x0 x1", "eq 1 x0 1 x1 = 2", "lower x0 -1",
                                    "le 0.25 x2 -3/4 x0 <= -0", "upper x0 1", "ge >= 1.50"))
        self.assertEqual(decoded.relus, ((0, 1),))
        self.assertEqual(decoded.linear, (("EQ", ((1, 0), (1, 1)), 2),
                                          ("LE", ((proof.Fraction(1, 4), 2), (proof.Fraction(-3, 4), 0)), 0),
                                          ("GE", (), proof.Fraction(3, 2))))
        self.assertEqual(decoded.bounds, (proof.Bound(0, "L", -1), proof.Bound(0, "U", 1)))
        self.assertEqual(text.decode(lines("lower x0 0.50")), text.decode(lines("lower x0 2/4")))
        self.assertNotEqual(text.decode(lines("lower x0 1/2")), text.decode(lines("lower x0 1/4")))


class PipelineSupportTests(unittest.TestCase):
    def rejects(self, data, message):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            adapter.check_pipeline_support(data)

    def test_example_rejections_have_specific_reasons(self):
        self.rejects(example("rejected_not_double"), "1/10 is not exactly a binary double")
        self.rejects(example("rejected_unbounded"), "x0 needs finite lower and upper bounds")

    def test_other_pipeline_restrictions(self):
        base = ("eq 1 x0 -1 x1 = 0", "lower x0 0", "upper x0 1", "lower x1 0", "upper x1 1")
        self.rejects(b"not a query\n", "not a marabou-exact-query-v1 file")
        self.rejects(lines("lower x0 0", "upper x0 1"), "at least one linear constraint")
        self.rejects(lines("eq = 0"), "at least one variable")
        self.rejects(lines("eq 1 x0 1 x0 = 0", *base[1:]), "repeated variable")
        self.rejects(lines(*base, "lower x0 0"), "exactly one lower and one upper")
        self.rejects(lines(*base, "relu x1 x1"), "distinct input and output")
        self.rejects(lines(*base[:-1], "upper x1 1e0"), "not a marabou-exact-query-v1 file")
        self.rejects(lines(*base, "lower x5000 0"), "variable index too large")
        big = "1" + "0" * 400
        self.rejects(lines(*base[:-1], f"upper x1 {big}"), "not exactly a binary double")
        self.assertEqual(len(adapter.check_pipeline_support(lines(*base)).bounds), 4)

    def test_accepted_examples(self):
        for name, relus in (("relu_chain_unsat", 2), ("relu_sat", 2), ("linear_unsat", 0)):
            with self.subTest(name=name):
                self.assertEqual(len(adapter.check_pipeline_support(example(name)).relus), relus)
        self.assertEqual(adapter.check_pipeline_support(example("inequality_linear_sat")).linear[0][0], "LE")


class CaptureBindingTests(unittest.TestCase):
    def rejects(self, data, loaded, message):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            adapter.reconstruct(data, loaded)

    def test_reordered_decimal_file_binds_to_the_capture(self):
        file_replay = adapter.reconstruct(example("relu_chain_unsat"), scenario_artifacts("relu_chain"))
        self.assertEqual((file_replay.kind, file_replay.relus), ("unsat", True))
        self.assertNotEqual(example("relu_chain_unsat"), (FIXTURES / "solver_relu_chain.mqx").read_bytes())

    def test_sat_and_linear_examples_bind(self):
        self.assertEqual(adapter.reconstruct(example("relu_sat"), scenario_artifacts("relu_sat")).kind, "sat")
        linear = adapter.reconstruct(example("linear_unsat"), scenario_artifacts("linear"))
        self.assertEqual((linear.kind, linear.relus), ("unsat", False))

    def test_mutated_files_do_not_bind(self):
        data = example("relu_chain_unsat")
        loaded = scenario_artifacts("relu_chain")
        for mutated in (data.replace(b"upper x4 -0.5\n", b"upper x4 -0.25\n"),
                        data + b"lower x6 0\nupper x6 0\n",
                        data.replace(b"eq 1 x3 -1 x5 = 0\n", b"eq 1 x3 -1 x5 = 1/4\n")):
            with self.subTest(mutated=mutated[-40:]):
                self.rejects(mutated, loaded, "differs from the query the file denotes")
        self.rejects(data.replace(b"relu x2 x3\n", b""), loaded, "differs from the query")

    def test_artifact_sets_must_match_the_file(self):
        loaded = scenario_artifacts("relu_chain")
        self.rejects(example("linear_unsat"), loaded, "only they do")
        linear = scenario_artifacts("linear")
        self.rejects(example("relu_chain_unsat"), linear, "only they do")
        both = dict(scenario_artifacts("linear"))
        both["assignment"] = scenario_artifacts("relu_sat")["assignment"]
        self.rejects(example("linear_unsat"), both, "exactly one of a certificate")
        neither = {k: v for k, v in scenario_artifacts("linear").items() if k != "certificate"}
        self.rejects(example("linear_unsat"), neither, "exactly one of a certificate")

    def test_tampered_capture_is_rejected_by_the_importers(self):
        loaded = scenario_artifacts("relu_chain")
        certificate, _ = loaded["certificate"]
        certificate["proof"]["lemmas"].pop(0)  # the leaf needs the first lemma's bound
        with self.assertRaisesRegex(proof.ImportFailure, "exact constant"):
            adapter.reconstruct(example("relu_chain_unsat"), loaded)
        loaded = scenario_artifacts("relu_chain")
        loaded["query"][0]["upperBounds"][4] = proof.Fraction(-1, 4)
        with self.assertRaisesRegex(proof.ImportFailure, "does not match"):
            adapter.reconstruct(example("relu_chain_unsat"), loaded)

    def test_rendering_rejects_bad_names_and_references(self):
        file_replay = adapter.reconstruct(example("linear_unsat"), scenario_artifacts("linear"))
        for name, replay, reference in (("bad name", "R", "q.mqx"), ("T", "R", "../q.mqx"),
                                        ("T", "R", "q.txt"), ("T", "r-x", "q.mqx")):
            with self.subTest(name=name, reference=reference):
                with self.assertRaises(proof.ImportFailure):
                    adapter.render_theorem_theory(name, replay, file_replay, reference)


class ExampleTheoryTests(unittest.TestCase):
    def test_example_theories_match_regeneration(self):
        for name, theory in adapter.example_theories(ISABELLE).items():
            with self.subTest(name=name):
                self.assertEqual((ISABELLE / name).read_text(), theory)

    def test_example_theories_state_theorems_about_file_bytes(self):
        for example_name, _, replay in adapter.EXAMPLES:
            theory = (ISABELLE / (adapter.example_theory_name(example_name) + ".thy")).read_text()
            data = example(example_name)
            with self.subTest(example=example_name):
                self.assertIn(f'external_file "examples/{example_name}.mqx"', theory)
                self.assertIn(hashlib.sha256(data).hexdigest(), theory)
                self.assertIn(f"decodes_like query_file {replay}.", theory)
                self.assertIn("query_file_model" if example_name == "relu_sat" else
                              "query_file_unsatisfiable", theory)

    def test_file_runs_reproduced_the_scenario_artifacts(self):
        keys = {"source": "_source.json", "steps": "_steps.json", "query": "_query.json",
                "certificate": ".json", "assignment": "_assignment.json",
                "before": "_before_relu.json", "introductions": "_relu_steps.json"}
        for example_name, scenario, _ in adapter.EXAMPLES:
            provenance = json.loads((FIXTURES / f"file_{example_name}_provenance.json").read_text())
            report = json.loads((FIXTURES / f"file_{example_name}_run.json").read_text())
            with self.subTest(example=example_name):
                self.assertEqual(provenance["scenario"], "file")
                self.assertEqual(provenance["query_file_sha256"],
                                 hashlib.sha256(example(example_name)).hexdigest())
                self.assertEqual(provenance["exit_code"], report["exit_code"])
                self.assertEqual(provenance["run_report_sha256"],
                                 hashlib.sha256((FIXTURES / f"file_{example_name}_run.json").read_bytes()).hexdigest())
                self.assertEqual(provenance["solver_log_sha256"],
                                 hashlib.sha256((FIXTURES / f"file_{example_name}.log").read_bytes()).hexdigest())
                present = [k for k in keys if f"{k}_sha256" in provenance]
                self.assertTrue({"source", "steps", "query"} <= set(present))
                for key in present:
                    fixture = FIXTURES / (f"solver_{scenario}" + keys[key])
                    self.assertEqual(provenance[f"{key}_sha256"],
                                     hashlib.sha256(fixture.read_bytes()).hexdigest(), key)
                for tool, path in (("capture_script_sha256", "tools/capture_marabou_solver.py"),
                                   ("query_file_importer_sha256", "tools/import_marabou_query_file.py"),
                                   ("exact_text_sha256", "tools/exact_query_text.py"),
                                   ("importer_sha256", "tools/import_marabou_json.py"),
                                   ("source_importer_sha256", "tools/import_marabou_source.py")):
                    self.assertEqual(provenance[tool],
                                     hashlib.sha256((ISABELLE / path).read_bytes()).hexdigest(), tool)
                for relative, digest in provenance["compiled_sources"].items():
                    self.assertEqual(hashlib.sha256((ISABELLE.parent / relative).read_bytes()).hexdigest(),
                                     digest, relative)


class FullArtifactExampleTests(unittest.TestCase):
    """Files whose complete native artifact set is saved as file_<example>_*."""

    def test_theories_match_regeneration(self):
        theories = adapter.full_artifact_example_theories(ISABELLE)
        self.assertEqual(len(theories),
                         2 * len(adapter.FULL_ARTIFACT_EXAMPLES + adapter.PREPROCESSED_EXAMPLES))
        for name, theory in theories.items():
            with self.subTest(name=name):
                self.assertEqual((ISABELLE / name).read_text(), theory)
                self.assertIn(f"    {name[:-4]}\n", (ISABELLE / "ROOT").read_text())

    def test_provenance_matches_the_saved_run_and_current_tools(self):
        for example_name, _ in adapter.FULL_ARTIFACT_EXAMPLES + adapter.PREPROCESSED_EXAMPLES:
            prefix = FIXTURES / f"file_{example_name}"
            provenance = json.loads(Path(str(prefix) + "_provenance.json").read_text())
            with self.subTest(example=example_name):
                self.assertEqual(provenance["scenario"], "file")
                self.assertEqual(provenance["query_file_sha256"],
                                 hashlib.sha256(example(example_name)).hexdigest())
                loaded = adapter.load_artifacts(prefix)
                self.assertEqual({k for k in provenance if k.endswith("_sha256") and
                                  k[:-7] in dict(adapter.ARTIFACTS) | {"prepared": None}},
                                 {k + "_sha256" for k in loaded})
                self.assertEqual(provenance["native_preprocessing"], "preprocessing" in loaded)
                for key, (_, digest) in loaded.items():
                    self.assertEqual(provenance[f"{key}_sha256"], digest, key)
                for key, suffix in (("run_report", "_run.json"), ("solver_log", ".log")):
                    self.assertEqual(provenance[key + "_sha256"],
                                     hashlib.sha256(Path(str(prefix) + suffix).read_bytes()).hexdigest())
                for tool, path in (("capture_script_sha256", "capture_marabou_solver.py"),
                                   ("query_file_importer_sha256", "import_marabou_query_file.py"),
                                   ("exact_text_sha256", "exact_query_text.py"),
                                   ("importer_sha256", "import_marabou_json.py"),
                                   ("source_importer_sha256", "import_marabou_source.py"),
                                   ("assignment_importer_sha256", "import_marabou_assignment.py"),
                                   ("relu_sequence_importer_sha256", "import_marabou_relu_sequence.py"),
                                   ("inequality_preparer_sha256", "prepare_inequalities.py"),
                                   ("preprocessing_importer_sha256", "import_marabou_preprocessing.py")):
                    self.assertEqual(provenance[tool], hashlib.sha256(
                        (ISABELLE / "tools" / path).read_bytes()).hexdigest(), tool)
                for relative, digest in provenance["compiled_sources"].items():
                    self.assertEqual(hashlib.sha256((ISABELLE.parent / relative).read_bytes()).hexdigest(),
                                     digest, relative)


class DriverTests(unittest.TestCase):
    def test_unsupported_file_is_rejected_before_building(self):
        with tempfile.TemporaryDirectory() as tmp:
            output = Path(tmp) / "out"
            stderr = io.StringIO()
            with contextlib.redirect_stderr(stderr), self.assertRaises(SystemExit) as raised:
                driver.main(["--query-file", str(EXAMPLES / "rejected_not_double.mqx"),
                             "--output", str(output)])
            self.assertEqual(raised.exception.code, 1)
            self.assertIn("not exactly a binary double", stderr.getvalue())
            self.assertFalse(output.exists())
            self.assertNotIn("logs are in", stderr.getvalue())

    def test_scenario_and_file_modes_are_exclusive(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as raised:
            driver.main(["--scenario", "linear", "--query-file", str(EXAMPLES / "linear_unsat.mqx"),
                         "--output", "/nonexistent/out"])
        self.assertEqual(raised.exception.code, 2)


if __name__ == "__main__":
    unittest.main()
