#!/usr/bin/env python3
"""Exact positive-auxiliary propagation, native capture and guard regressions."""
import copy
from fractions import Fraction
import json
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as proof
import import_marabou_source as source

ISABELLE = Path(__file__).resolve().parents[1]
FIXTURES = ISABELLE / "tests/fixtures/marabou"
STEM = "solver_relu_aux_inactive"
SUFFIXES = ("_source.json", "_steps.json", "_query.json", ".json")


def native_bundle():
    return [proof.load_json(FIXTURES / (STEM + suffix)) for suffix in SUFFIXES]


def aux_fixture(lower=Fraction(1, 4)):
    """Hand-constructed adapter test, not a solver capture.

    b=x0, f=x1, aux=x2, tableau auxiliary x3; f - b - aux - x3 = 0.
    """
    query = {
        "tableau": [[{"var": i, "val": a} for i, a in ((1, 1), (0, -1), (2, -1), (3, -1))]],
        "lowerBounds": [-2, Fraction(1, 4), lower, 0],
        "upperBounds": [2, 2, 2, 0],
        "constraints": [{"constraintType": 0, "vars": [0, 1, 2, 3]}],
    }
    evidence = copy.deepcopy(query)
    evidence["proof"] = {
        "lemmas": [{"affVar": 1, "affBound": "U", "bound": 0, "causVar": 2,
                    "causBound": "L", "constraint": 0, "expl": []}],
        "contradiction": [1],
    }
    return query, evidence


def rule_nodes(cert):
    while not isinstance(cert, proof.Leaf):
        yield cert
        cert = cert.child


class AuxLowerBoundImportTests(unittest.TestCase):
    def rejects(self, query, evidence, message="."):
        with self.assertRaisesRegex(proof.ImportFailure, message):
            proof.reconstruct(query, evidence)

    def test_native_capture_replays_and_regenerates(self):
        loaded = native_bundle()
        replay = source.reconstruct(*(obj for obj, _ in loaded))
        name = "Imported_Marabou_Source_Relu_Aux_Inactive"
        self.assertEqual(source.render_theory(name, replay, *(h for _, h in loaded)),
                         (ISABELLE / (name + ".thy")).read_text())
        nodes = list(rule_nodes(replay.certificate))
        self.assertEqual([type(n) for n in nodes], [proof.LinearBound, proof.ReluAuxLowerOutputUpper])
        self.assertEqual(nodes[0].bound, proof.Bound(0, "L", Fraction(1, 4)))
        rule = nodes[1]
        self.assertEqual((rule.x, rule.y, rule.auxiliary, rule.auxiliary_lower, rule.output_upper),
                         (1, 2, 0, Fraction(1, 4), 0))
        self.assertEqual(replay.steps, ((0, 5), (1, 6), (2, 7)))

    def test_native_evidence_is_the_unfiltered_auxiliary_to_output_lemma(self):
        evidence = native_bundle()[-1][0]
        self.assertEqual(evidence["constraints"], [{"constraintType": 0, "vars": [1, 2, 0, 7]}])
        lemmas = evidence["proof"]["lemmas"]
        self.assertEqual(len(lemmas), 1)
        self.assertEqual({k: lemmas[0][k] for k in ("causVar", "causBound", "affVar", "affBound", "constraint")},
                         {"causVar": 0, "causBound": "L", "affVar": 2, "affBound": "U", "constraint": 0})
        self.assertEqual(lemmas[0]["bound"], 0)
        self.assertEqual(lemmas[0]["expl"], [{"var": 0, "val": -1}])
        self.assertEqual(set(evidence["proof"]), {"lemmas", "contradiction"})

    def test_native_run_report(self):
        report = json.loads((FIXTURES / (STEM + "_run.json")).read_text())
        for field in ("proof_production", "initialization_succeeded", "introduction_list_before_solve",
                      "source_snapshot_before_initialization", "relu_phase_unfixed_before_solve",
                      "initial_snapshot_matches_tableau_and_ground_bounds"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi", "solve_return", "snapshot_before_relu_introduction"):
            self.assertFalse(report[field], field)
        for field, value in (("scenario", "relu_aux_inactive"), ("exit_code", "UNSAT"),
                             ("native_relu_introductions", 0), ("input_variables", 5),
                             ("processed_variables", 8), ("proposed_introductions", 3),
                             ("plc_lemmas_before_solve", 0), ("plc_lemmas_after_solve", 1),
                             ("root_children", 0), ("search_splits", 0),
                             ("explained_leaves", 1), ("delegated_leaves", 0)):
            self.assertEqual(report[field], value, field)

    def test_native_lemma_is_needed_by_its_leaf(self):
        query, evidence = [copy.deepcopy(obj) for obj, _ in native_bundle()[-2:]]
        evidence["proof"]["lemmas"] = []
        self.rejects(query, evidence, "exact constant")

    def test_invalid_native_auxiliary_premise_is_not_skipped(self):
        for explanation in ([], [{"var": 0, "val": 0}]):
            query, evidence = [copy.deepcopy(obj) for obj, _ in native_bundle()[-2:]]
            evidence["proof"]["lemmas"][0]["expl"] = explanation
            with self.subTest(explanation=explanation):
                self.rejects(query, evidence, "strictly positive")

    def test_native_linear_premise_does_not_become_a_ground_bound(self):
        query, evidence = [copy.deepcopy(obj) for obj, _ in native_bundle()[-2:]]
        extra = copy.deepcopy(evidence["proof"]["lemmas"][0])
        extra["expl"] = []
        evidence["proof"]["lemmas"].append(extra)
        self.rejects(query, evidence, "strictly positive")

    def test_coherent_sat_relaxation_rejects_the_native_bundle(self):
        # w>=0 instead of 1/4 admits aux=w=0, b=f=t=1/4 (proved in HOL).
        inputs = [obj for obj, _ in native_bundle()]
        inputs[0]["lowerBounds"][3] = 0
        for obj in inputs[2:]:
            obj["lowerBounds"][3] = 0
        with self.assertRaisesRegex(proof.ImportFailure, "strictly positive"):
            source.reconstruct(*inputs)

    def test_ground_auxiliary_premise_bounds_the_output(self):
        instance, cert = proof.reconstruct(*aux_fixture())
        self.assertIsInstance(cert, proof.ReluAuxLowerOutputUpper)
        self.assertEqual((cert.x, cert.y, cert.auxiliary), (0, 1, 2))
        self.assertEqual((cert.auxiliary_lower, cert.output_upper), (Fraction(1, 4), 0))
        self.assertIsInstance(cert.child, proof.Leaf)
        self.assertEqual(instance.query.bounds[2], proof.Bound(1, "L", Fraction(1, 4)))

    def test_exact_tiny_positive_premise_is_accepted(self):
        _, cert = proof.reconstruct(*aux_fixture(Fraction(1, 10**20)))
        self.assertEqual(cert.auxiliary_lower, Fraction(1, 10**20))

    def test_zero_and_negative_auxiliary_premises_are_rejected(self):
        for lower in (0, Fraction(-1, 10**20), -1):
            with self.subTest(lower=lower):
                self.rejects(*aux_fixture(lower), "strictly positive")

    def test_zero_boundary_has_an_exact_model(self):
        query, evidence = aux_fixture(0)
        instance = proof.parse_instance(query)
        values = (1, 1, 0, 0)
        self.assertTrue(all(e.constant + sum(c * values[v] for c, v in e.terms) == 0
                            for e in instance.query.equations))
        self.assertTrue(all(b.value <= values[b.variable] if b.kind == "L"
                            else values[b.variable] <= b.value for b in instance.query.bounds))
        self.assertEqual(values[1], max(0, values[0]))
        self.rejects(query, evidence, "strictly positive")

    def test_input_or_output_bounds_cannot_substitute_for_the_auxiliary_premise(self):
        for variable in (0, 1):
            query, evidence = aux_fixture(0)
            query["lowerBounds"][variable] = evidence["lowerBounds"][variable] = Fraction(1, 2)
            with self.subTest(variable=variable):
                self.rejects(query, evidence, "strictly positive")

    def test_negative_output_conclusion_is_rejected_without_tolerance(self):
        query, evidence = aux_fixture()
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(-1, 10**20)
        self.rejects(query, evidence, "too strong")

    def test_weaker_nonnegative_conclusion_is_checked(self):
        query, evidence = aux_fixture()
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(1, 8)
        _, cert = proof.reconstruct(query, evidence)
        self.assertEqual(cert.output_upper, Fraction(1, 8))
        evidence["proof"]["lemmas"][0]["bound"] = Fraction(1, 4)
        self.rejects(query, evidence, "exact constant")

    def test_equation_cannot_be_supplied_by_metadata(self):
        query, evidence = aux_fixture()
        for obj in (query, evidence):
            obj["tableau"][0] = [{"var": 0, "val": 0}]
        self.rejects(query, evidence, "cannot reconstruct")

    def test_equation_requires_both_fixed_tableau_bounds(self):
        for field, value in (("lowerBounds", -1), ("upperBounds", 1)):
            query, evidence = aux_fixture()
            query[field][3] = evidence[field][3] = value
            with self.subTest(field=field):
                self.rejects(query, evidence, "cannot reconstruct")

    def test_incorrect_auxiliary_equation_coefficient_is_rejected(self):
        query, evidence = aux_fixture()
        for obj in (query, evidence):
            obj["tableau"][0][2]["val"] = -2
        self.rejects(query, evidence, "cannot reconstruct")

    def test_wrong_affected_variable_and_missing_relu_are_rejected(self):
        for affected in (0, 2, 3):
            query, evidence = aux_fixture()
            evidence["proof"]["lemmas"][0]["affVar"] = affected
            with self.subTest(affected=affected):
                self.rejects(query, evidence, "unique")
        query, evidence = aux_fixture()
        query["constraints"] = evidence["constraints"] = []
        self.rejects(query, evidence, "unique")

    def test_ambiguous_auxiliary_and_input_roles_are_rejected(self):
        # A second ReLU b=x2, f=x0, aux=x1 makes the same lemma also read as
        # input-lower -> auxiliary-upper; the adapter must not choose one.
        query, evidence = aux_fixture()
        for obj in (query, evidence):
            obj["constraints"].append({"constraintType": 0, "vars": [2, 0, 1, 3]})
        self.rejects(query, evidence, "unique")

    def test_other_directions_remain_unsupported(self):
        for field, value, message in (("affBound", "L", "unsupported PLC lemma"),
                                      ("causBound", "U", "input/output")):
            query, evidence = aux_fixture()
            evidence["proof"]["lemmas"][0][field] = value
            with self.subTest(field=field):
                self.rejects(query, evidence, message)

    def test_no_lemma_or_bad_child_cannot_certify_the_small_query(self):
        query, evidence = aux_fixture()
        evidence["proof"]["lemmas"] = []
        self.rejects(query, evidence, "exact constant")
        query, evidence = aux_fixture()
        evidence["proof"]["contradiction"] = [{"var": 0, "val": 0}]
        self.rejects(query, evidence, "exact constant")

    def test_generated_constructor_syntax(self):
        _, cert = proof.reconstruct(*aux_fixture())
        # Each equation direction also uses one fixed bound of tableau auxiliary x3.
        self.assertEqual(proof.hol_certificate(cert),
                         "Relu_Aux_Lower_Output_Upper 0 1 2 (1 / 4) 0 [1, 0, 0, 0, 0, 0, 0, 0, 0, 1]\n"
                         "    [0, 1, 0, 0, 0, 0, 0, 0, 1, 0]\n"
                         "    (Linear_Unsat [0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0])")

    def independent_split(self):
        query, evidence = aux_fixture()
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

    def test_rule_replays_in_both_independent_split_children(self):
        _, cert = proof.reconstruct(*self.independent_split())
        self.assertIsInstance(cert, proof.Split)
        for child in (cert.active, cert.inactive):
            self.assertIsInstance(child, proof.ReluAuxLowerOutputUpper)
            self.assertEqual(child.auxiliary_lower, Fraction(1, 4))
            self.assertIsInstance(child.child, proof.Leaf)

    def test_output_bound_cannot_leak_to_a_sibling(self):
        query, evidence = self.independent_split()
        evidence["proof"]["children"][1]["lemmas"] = []
        self.rejects(query, evidence, "exact constant")


if __name__ == "__main__":
    unittest.main()
