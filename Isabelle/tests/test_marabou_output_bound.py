#!/usr/bin/env python3
"""Exact positive-output propagation, preserved evidence and guard regressions."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as proof
import import_marabou_relu_sequence as sequence

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
SUFFIXES = ("_before_relu.json", "_relu_steps.json", "_source.json", "_steps.json", "_query.json", ".json")


def native_bundle():
    return [proof.load_json(FIXTURES / ("solver_relu_chain" + suffix)) for suffix in SUFFIXES]


def output_fixture(lower=Fraction(1, 4)):
    """Hand-constructed adapter test, not a solver capture."""
    query = {
        "tableau": [[{"var": i, "val": a} for i, a in ((1, 1), (0, -1), (2, -1), (3, -1))]],
        "lowerBounds": [-2, lower, Fraction(1, 4), 0],
        "upperBounds": [2, 2, 2, 0],
        "constraints": [{"constraintType": 0, "vars": [0, 1, 2, 3]}],
    }
    evidence = copy.deepcopy(query)
    evidence["proof"] = {
        "lemmas": [{"affVar": 2, "affBound": "U", "bound": 0, "causVar": 1,
                    "causBound": "L", "constraint": 0, "expl": []}],
        "contradiction": [2],
    }
    return query, evidence


def rule_nodes(cert):
    while not isinstance(cert, proof.Leaf):
        yield cert
        cert = cert.child


class OutputBoundImportTests(unittest.TestCase):
    def rejects(self, query, evidence, message="."):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            proof.reconstruct(query, evidence)

    def test_full_native_chain_replays_and_regenerates(self):
        loaded = native_bundle()
        replay = sequence.reconstruct(*(obj for obj, _ in loaded))
        name = "Imported_Marabou_Native_Relu_Chain"
        self.assertEqual(sequence.render_theory(name, replay, *(h for _, h in loaded)),
                         (ISABELLE / (name + ".thy")).read_text())
        nodes = list(rule_nodes(replay.after.certificate))
        self.assertEqual([type(n) for n in nodes], [
            proof.LinearBound, proof.ReluUpper, proof.LinearBound, proof.ReluAuxUpper,
            proof.LinearBound, proof.ReluUpper, proof.LinearBound, proof.ReluOutputAuxUpper])
        self.assertEqual(nodes[-2].bound, proof.Bound(3, "L", Fraction(1, 4)))
        self.assertEqual((nodes[-1].x, nodes[-1].y, nodes[-1].auxiliary,
                          nodes[-1].output_lower, nodes[-1].auxiliary_upper), (2, 3, 7, Fraction(1, 4), 0))
        self.assertEqual(nodes[3].auxiliary_upper, Fraction(250001, 1000000))
        self.assertEqual(nodes[5].output_upper, Fraction(1750001, 1000000))
        self.assertEqual(nodes[5].input_upper, Fraction(-1, 4))

    def test_new_native_data_match_unchanged_preserved_trial(self):
        old = FIXTURES / "rejected_relu_chain"
        for suffix in SUFFIXES:
            self.assertEqual((FIXTURES / ("solver_relu_chain" + suffix)).read_bytes(),
                             (old / ("solver_relu_sequence" + suffix)).read_bytes())

    def test_native_run_and_sequence_provenance(self):
        report = json.loads((FIXTURES / "solver_relu_chain_run.json").read_text())
        for field in ("proof_production", "initialization_succeeded", "snapshot_before_relu_introduction",
                      "introduction_list_before_solve", "source_snapshot_before_initialization",
                      "initial_snapshot_matches_tableau_and_ground_bounds",
                      "relu_phase_unfixed_before_solve"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi", "solve_return"):
            self.assertFalse(report[field], field)
        for field, value in (("exit_code", "UNSAT"), ("native_relu_introductions", 2),
                             ("variables_before_relu_introduction", 6), ("input_variables", 8),
                             ("processed_variables", 13), ("proposed_introductions", 5),
                             ("plc_lemmas_before_solve", 0), ("plc_lemmas_after_solve", 4),
                             ("explained_leaves", 1), ("delegated_leaves", 0)):
            self.assertEqual(report[field], value, field)
        provenance = json.loads((FIXTURES / "solver_relu_chain_provenance.json").read_text())
        for key, path in (
            ("before_relu_query_sha256", FIXTURES / "solver_relu_chain_before_relu.json"),
            ("relu_introduction_sequence_sha256", FIXTURES / "solver_relu_chain_relu_steps.json"),
            ("relu_sequence_importer_sha256", ISABELLE / "tools/import_marabou_relu_sequence.py"),
        ):
            self.assertEqual(provenance[key], hashlib.sha256(path.read_bytes()).hexdigest())

    def test_ground_output_premise_uses_output_not_input_bound(self):
        instance, cert = proof.reconstruct(*output_fixture())
        self.assertIsInstance(cert, proof.ReluOutputAuxUpper)
        self.assertEqual(cert.output_lower, Fraction(1, 4))
        self.assertEqual(instance.query.bounds[0], proof.Bound(0, "L", -2))
        self.assertIsInstance(cert.child, proof.Leaf)

    def test_exact_tiny_positive_premise_is_accepted(self):
        _, cert = proof.reconstruct(*output_fixture(Fraction(1, 10**20)))
        self.assertEqual(cert.output_lower, Fraction(1, 10**20))

    def test_zero_and_negative_output_premises_are_rejected(self):
        for lower in (0, Fraction(-1, 10**20), -1):
            self.rejects(*output_fixture(lower), "strictly positive")

    def test_zero_boundary_has_an_exact_model(self):
        query, evidence = output_fixture(0)
        instance = proof.parse_instance(query)
        values = (-1, 0, 1, 0)
        self.assertTrue(all(e.constant + sum(c * values[v] for c, v in e.terms) == 0
                            for e in instance.query.equations))
        self.assertTrue(all(b.value <= values[b.variable] if b.kind == "L"
                            else values[b.variable] <= b.value for b in instance.query.bounds))
        self.assertEqual(values[1], max(0, values[0]))
        self.rejects(query, evidence, "strictly positive")

    def test_positive_input_bound_cannot_substitute_for_zero_output_premise(self):
        query, evidence = output_fixture(0)
        query["lowerBounds"][0] = evidence["lowerBounds"][0] = Fraction(1, 2)
        self.rejects(query, evidence, "strictly positive")

    def test_negative_auxiliary_conclusion_is_rejected_without_tolerance(self):
        query, evidence = output_fixture()
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(-1, 10**20)
        self.rejects(query, evidence, "too strong")

    def test_weaker_nonnegative_conclusion_is_checked(self):
        query, evidence = output_fixture()
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(1, 8)
        _, cert = proof.reconstruct(query, evidence)
        self.assertEqual(cert.auxiliary_upper, Fraction(1, 8))
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(1, 4)
        self.rejects(query, evidence, "exact constant")

    def test_equation_cannot_be_supplied_by_metadata(self):
        query, evidence = output_fixture()
        for obj in (query, evidence):
            obj["tableau"][0] = [{"var": 0, "val": 0}]
        self.rejects(query, evidence, "cannot reconstruct")

    def test_equation_requires_both_fixed_tableau_bounds(self):
        for field, value in (("lowerBounds", -1), ("upperBounds", 1)):
            query, evidence = output_fixture()
            query[field][3] = evidence[field][3] = value
            self.rejects(query, evidence, "cannot reconstruct")

    def test_incorrect_auxiliary_equation_coefficient_is_rejected(self):
        query, evidence = output_fixture()
        for obj in (query, evidence):
            obj["tableau"][0][2]["val"] = -2
        self.rejects(query, evidence, "cannot reconstruct")

    def test_wrong_auxiliary_and_missing_relu_are_rejected(self):
        query, evidence = output_fixture()
        evidence["proof"]["lemmas"][0]["affVar"] = 3
        self.rejects(query, evidence, "unique")
        query, evidence = output_fixture()
        query["constraints"] = evidence["constraints"] = []
        self.rejects(query, evidence, "unique")

    def test_ambiguous_input_output_roles_are_rejected(self):
        query, evidence = output_fixture()
        for obj in (query, evidence):
            obj["constraints"].append({"constraintType": 0, "vars": [1, 0, 2, 3]})
        self.rejects(query, evidence, "unique")

    def test_other_directions_and_auxiliary_causes_remain_unsupported(self):
        for field, value in (("affBound", "L"), ("causBound", "U"), ("causVar", 3)):
            query, evidence = output_fixture()
            evidence["proof"]["lemmas"][0][field] = value
            self.rejects(query, evidence)

    def test_no_lemma_or_bad_child_cannot_certify_the_small_query(self):
        query, evidence = output_fixture()
        evidence["proof"]["lemmas"] = []
        self.rejects(query, evidence, "exact constant")
        query, evidence = output_fixture()
        evidence["proof"]["contradiction"] = [{"var": 0, "val": 0}]
        self.rejects(query, evidence, "exact constant")

    def test_invalid_native_output_premise_is_not_skipped(self):
        loaded = native_bundle()
        query, evidence = [copy.deepcopy(obj) for obj, _ in loaded[-2:]]
        for explanation in ([], [{"var": 2, "val": 0}]):
            evidence["proof"]["lemmas"][-1]["expl"] = explanation
            self.rejects(query, evidence, "strictly positive")

    def test_native_linear_premise_does_not_become_a_ground_bound(self):
        loaded = native_bundle()
        query, evidence = [copy.deepcopy(obj) for obj, _ in loaded[-2:]]
        extra = copy.deepcopy(evidence["proof"]["lemmas"][-1])
        extra["expl"] = []
        evidence["proof"]["lemmas"].append(extra)
        self.rejects(query, evidence, "strictly positive")

    def test_preserved_last_lemma_is_checked_even_though_the_prefix_can_close(self):
        loaded = native_bundle()
        query, evidence = [copy.deepcopy(obj) for obj, _ in loaded[-2:]]
        evidence["proof"]["lemmas"].pop()
        _, cert = proof.reconstruct(query, evidence)
        self.assertFalse(any(isinstance(node, proof.ReluOutputAuxUpper) for node in rule_nodes(cert)))
        # The full original bundle is nevertheless imported without filtering.
        self.assertEqual(len(loaded[-1][0]["proof"]["lemmas"]), 4)

    def test_coherent_sat_relaxation_rejects_the_native_chain(self):
        inputs = [obj for obj, _ in native_bundle()]
        for i in (0, 2, 4, 5):
            inputs[i]["lowerBounds"][5] = 0
        with self.assertRaisesRegex(proof.ImportFailure, "strictly positive"):
            sequence.reconstruct(*inputs)

    def independent_split(self):
        query, evidence = output_fixture()
        for obj in (query, evidence):
            obj["tableau"].append([{"var": i, "val": a}
                                   for i, a in ((5, 1), (4, -1), (6, -1), (7, -1))])
            obj["lowerBounds"].extend([-1, 0, 0, 0])
            obj["upperBounds"].extend([1, 1, 2, 0])
            obj["constraints"].append({"constraintType": 0, "vars": [4, 5, 6, 7]})
        children = [copy.deepcopy(evidence["proof"]), copy.deepcopy(evidence["proof"])]
        children[0]["split"] = [{"var": 4, "val": 0, "bound": "L"}, {"var": 6, "val": 0, "bound": "U"}]
        children[1]["split"] = [{"var": 4, "val": 0, "bound": "U"}, {"var": 5, "val": 0, "bound": "U"}]
        evidence["proof"] = {"children": children}
        return query, evidence

    def test_output_rule_replays_in_both_independent_split_children(self):
        _, cert = proof.reconstruct(*self.independent_split())
        self.assertIsInstance(cert, proof.Split)
        for child in (cert.active, cert.inactive):
            self.assertIsInstance(child, proof.ReluOutputAuxUpper)
            self.assertEqual(child.output_lower, Fraction(1, 4))
            self.assertIsInstance(child.child, proof.Leaf)

    def test_output_bound_cannot_leak_to_a_sibling(self):
        query, evidence = self.independent_split()
        evidence["proof"]["children"][1]["lemmas"] = []
        self.rejects(query, evidence, "exact constant")


if __name__ == "__main__":
    unittest.main()
