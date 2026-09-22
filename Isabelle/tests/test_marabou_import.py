#!/usr/bin/env python3
"""Adversarial parsing/reconstruction tests; HOL replay is checked by ROOT."""
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
import import_marabou_json as adapter


FIXTURES = Path(__file__).parent / "fixtures/marabou"
ISABELLE = Path(__file__).resolve().parents[1]
FIXTURE_TYPES = {
    "linear": adapter.Leaf, "relu": adapter.Split, "nested": adapter.Split,
    "propagation": adapter.ReluUpper, "propagation_positive": adapter.ReluUpper,
    "propagation_chain": adapter.ReluUpper, "propagation_tree": adapter.Split,
    "explained_negative": adapter.LinearBound, "explained_positive": adapter.LinearBound,
    "solver_linear": adapter.Leaf, "solver_relu": adapter.LinearBound,
    "solver_relu_aux": adapter.LinearBound, "solver_relu_aux_active": adapter.LinearBound,
}


def fixture(name):
    query, _ = adapter.load_json(FIXTURES / (name + "_query.json"))
    proof, _ = adapter.load_json(FIXTURES / (name + ".json"))
    return query, proof


class ImportTests(unittest.TestCase):
    def parse_text(self, text):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "input.json"
            path.write_text(text, encoding="utf-8")
            return adapter.load_json(path)[0]

    def test_exact_decimal_decoding(self):
        self.assertEqual(self.parse_text('[0.1, -1.25, 1e-20]'),
                         [Fraction(1, 10), Fraction(-5, 4), Fraction(1, 10**20)])

    def test_reject_malformed_json(self):
        for text in ('{"x": 1, "x": 2}', '[NaN]', '[Infinity]', '[-Infinity]',
                     '[1e9999999]', '[1,]', '["unterminated]'):
            with self.subTest(text=text), self.assertRaises(adapter.ImportFailure):
                self.parse_text(text)

    def test_all_source_writer_fixtures_reconstruct(self):
        for name, kind in FIXTURE_TYPES.items():
            with self.subTest(name=name):
                instance, cert = adapter.reconstruct(*fixture(name))
                self.assertTrue(instance.n > 0)
                self.assertIsInstance(cert, kind)

    def test_checked_in_theories_match_regeneration(self):
        for name in FIXTURE_TYPES:
            with self.subTest(name=name):
                query, q_hash = adapter.load_json(FIXTURES / (name + "_query.json"))
                proof, p_hash = adapter.load_json(FIXTURES / (name + ".json"))
                instance, cert = adapter.reconstruct(query, proof)
                theory_name = "Imported_Marabou_" + name.title()
                self.assertEqual(adapter.render_theory(theory_name, instance, cert, q_hash, p_hash),
                                 (ISABELLE / (theory_name + ".thy")).read_text())

    def test_independent_query_binding(self):
        query, proof = fixture("linear")
        proof["upperBounds"][0] = Fraction(1, 8)
        with self.assertRaisesRegex(adapter.ImportFailure, "does not match"):
            adapter.reconstruct(query, proof)

    def test_solver_capture_provenance(self):
        for scenario in ("linear", "relu", "relu_aux", "relu_aux_active"):
            with self.subTest(scenario=scenario):
                stem = "solver_" + scenario
                provenance = json.loads((FIXTURES / (stem + "_provenance.json")).read_text())
                self.assertEqual(provenance["scenario"], scenario)
                for key, suffix in (
                    ("processed_query_sha256", "_query.json"),
                    ("certificate_sha256", ".json"),
                    ("run_report_sha256", "_run.json"),
                    ("solver_log_sha256", ".log"),
                ):
                    self.assertEqual(provenance[key],
                                     hashlib.sha256((FIXTURES / (stem + suffix)).read_bytes()).hexdigest())
                self.assertEqual(provenance["marabou_revision"], "1c2f4788c32e2f4e407c356b763a8025c5578722")
                for relative, digest in provenance["compiled_sources"].items():
                    self.assertEqual(hashlib.sha256((ISABELLE.parent / relative).read_bytes()).hexdigest(),
                                     digest, relative)
                self.assertEqual(provenance["capture_script_sha256"],
                                 hashlib.sha256((ISABELLE / "tools/capture_marabou_solver.py").read_bytes()).hexdigest())
                self.assertEqual(provenance["importer_sha256"],
                                 hashlib.sha256((ISABELLE / "tools/import_marabou_json.py").read_bytes()).hexdigest())
                self.assertEqual(provenance["cmake_sha256"],
                                 hashlib.sha256((ISABELLE / "tools/solver_capture/CMakeLists.txt").read_bytes()).hexdigest())

    def test_solver_capture_is_a_solve_result_with_a_fixed_auxiliary(self):
        report = json.loads((FIXTURES / "solver_linear_run.json").read_text())
        self.assertTrue(report["initialization_succeeded"])
        self.assertTrue(report["proof_production"])
        self.assertFalse(report["preprocessing"])
        self.assertFalse(report["solve_return"])
        self.assertEqual(report["exit_code"], "UNSAT")
        self.assertGreater(report["main_loop_iterations"], 0)
        self.assertEqual(report["explained_leaves"], 1)
        self.assertEqual(report["delegated_leaves"], 0)
        instance, cert = adapter.reconstruct(*fixture("solver_linear"))
        self.assertEqual(instance.n, report["processed_variables"])
        self.assertEqual(len(instance.query.equations), report["processed_rows"])
        self.assertIn(adapter.Bound(2, "L", Fraction(0)), instance.query.bounds)
        self.assertIn(adapter.Bound(2, "U", Fraction(0)), instance.query.bounds)
        self.assertIsInstance(cert, adapter.Leaf)

    def test_corrupt_solver_certificate_is_rejected(self):
        for weight in (0, -1):
            query, proof = fixture("solver_linear")
            proof["proof"]["contradiction"][0]["val"] = weight
            with self.subTest(weight=weight), self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
                adapter.reconstruct(query, proof)

    def test_solver_capture_cannot_drop_the_auxiliary_bound(self):
        # With z >= -1 instead of z = 0, x=1/4, y=1/2, z=-1/4 is a model.
        query, proof = fixture("solver_linear")
        query["lowerBounds"][2] = proof["lowerBounds"][2] = -1
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_solver_relu_evidence_was_produced_during_solve(self):
        report = json.loads((FIXTURES / "solver_relu_run.json").read_text())
        for field in ("initialization_succeeded", "proof_production",
                      "relu_phase_unfixed_before_solve",
                      "initial_snapshot_matches_tableau_and_ground_bounds"):
            self.assertTrue(report[field], field)
        for field in ("preprocessing", "deepsoi", "solve_return"):
            self.assertFalse(report[field], field)
        self.assertEqual(report["exit_code"], "UNSAT")
        self.assertEqual(report["plc_lemmas_before_solve"], 0)
        self.assertEqual(report["plc_lemmas_after_solve"], 1)
        self.assertEqual(report["relu_constraints"], 1)
        self.assertEqual(report["explained_leaves"], 1)
        self.assertEqual(report["delegated_leaves"], 0)
        self.assertEqual(report["root_children"], 0)
        self.assertEqual(report["simplex_steps"], 0)

    def test_solver_relu_reconstructs_an_explained_nonlinear_step(self):
        query, proof = fixture("solver_relu")
        self.assertEqual(proof["proof"]["lemmas"], [{
            "affVar": 1, "affBound": "U", "bound": 0,
            "causVar": 0, "causBound": "U", "constraint": 0,
            "expl": [{"var": 0, "val": -1}],
        }])
        instance, cert = adapter.reconstruct(query, proof)
        self.assertEqual(instance.n, 8)
        self.assertEqual(instance.query.relus, ((0, 1),))
        self.assertNotIn(adapter.Bound(0, "U", Fraction(-1, 2)), instance.query.bounds)
        self.assertIsInstance(cert, adapter.LinearBound)
        self.assertEqual(cert.bound, adapter.Bound(0, "U", Fraction(-1, 2)))
        self.assertIsInstance(cert.child, adapter.ReluUpper)
        self.assertEqual((cert.child.x, cert.child.y, cert.child.input_upper, cert.child.output_upper),
                         (0, 1, Fraction(-1, 2), 0))
        self.assertIsInstance(cert.child.child, adapter.Leaf)

    def test_solver_relu_missing_lemma_or_explanation_is_rejected(self):
        for omission in ("lemma", "explanation"):
            query, proof = fixture("solver_relu")
            if omission == "lemma":
                proof["proof"]["lemmas"] = []
            else:
                proof["proof"]["lemmas"][0]["expl"] = []
            with self.subTest(omission=omission), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_solver_relu_corrupt_explanation_is_rejected(self):
        for explanation in ([{"var": 0, "val": 0}], [{"var": 0, "val": 1}],
                            [{"var": 1, "val": -1}]):
            query, proof = fixture("solver_relu")
            proof["proof"]["lemmas"][0]["expl"] = explanation
            with self.subTest(explanation=explanation), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_solver_relu_stronger_conclusion_is_rejected_exactly(self):
        query, proof = fixture("solver_relu")
        proof["proof"]["lemmas"][0]["bound"] = Fraction(-1, 10**20)
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_solver_relu_corrupt_terminal_contradiction_is_rejected(self):
        for combination in ([{"var": 2, "val": 0}], [{"var": 2, "val": -1}],
                            [{"var": 0, "val": 1}]):
            query, proof = fixture("solver_relu")
            proof["proof"]["contradiction"] = combination
            with self.subTest(combination=combination), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_solver_relu_relaxed_satisfiable_query_rejects_certificate(self):
        # Now b=z=-1/2, f=w=0, aux=1/2, slacks=0 is a full ReLU model.
        query, proof = fixture("solver_relu")
        query["lowerBounds"][3] = proof["lowerBounds"][3] = 0
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_auxiliary_solver_captures_have_native_lemmas(self):
        for name, count in (("solver_relu_aux", 2), ("solver_relu_aux_active", 1)):
            with self.subTest(name=name):
                report = json.loads((FIXTURES / (name + "_run.json")).read_text())
                self.assertTrue(report["initialization_succeeded"])
                self.assertTrue(report["proof_production"])
                self.assertTrue(report["relu_phase_unfixed_before_solve"])
                self.assertTrue(report["initial_snapshot_matches_tableau_and_ground_bounds"])
                self.assertFalse(report["solve_return"])
                self.assertEqual(report["exit_code"], "UNSAT")
                self.assertEqual(report["plc_lemmas_before_solve"], 0)
                self.assertEqual(report["plc_lemmas_after_solve"], count)
                self.assertEqual(report["delegated_leaves"], 0)
                self.assertEqual(report["root_children"], 0)

    def test_auxiliary_negative_premise_and_equation_witnesses(self):
        instance, cert = adapter.reconstruct(*fixture("solver_relu_aux"))
        self.assertEqual(cert.bound, adapter.Bound(0, "L", Fraction(-7, 4)))
        adapter.validate_implication(instance.query, instance.n, cert.bound, cert.weights)
        rule = cert.child
        self.assertIsInstance(rule, adapter.ReluAuxUpper)
        self.assertEqual((rule.x, rule.y, rule.auxiliary), (0, 1, 4))
        self.assertEqual(rule.auxiliary_upper, Fraction(875001, 500000))
        query = instance.query.add_bound(cert.bound)
        expression = adapter.Expr(Fraction(0), ((Fraction(1), 1), (Fraction(-1), 0), (Fraction(-1), 4)))
        self.assertEqual(adapter.weighted_vector(query, instance.n, rule.positive),
                         expression.vector(instance.n))
        self.assertEqual(adapter.weighted_vector(query, instance.n, rule.negative),
                         expression.scale(-1).vector(instance.n))
        self.assertIsInstance(rule.child, adapter.LinearBound)
        self.assertIsInstance(rule.child.child, adapter.ReluUpper)

    def test_auxiliary_active_premise_and_terminal_leaf(self):
        _, cert = adapter.reconstruct(*fixture("solver_relu_aux_active"))
        self.assertEqual(cert.bound, adapter.Bound(0, "L", Fraction(1, 2)))
        self.assertIsInstance(cert.child, adapter.ReluAuxUpper)
        self.assertEqual(cert.child.auxiliary_upper, 0)
        self.assertIsInstance(cert.child.child, adapter.Leaf)

    def test_auxiliary_non_ground_premise_requires_explanation(self):
        for name in ("solver_relu_aux", "solver_relu_aux_active"):
            query, proof = fixture(name)
            proof["proof"]["lemmas"][0]["expl"] = []
            with self.subTest(name=name), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_auxiliary_lower_explanation_sign_and_row(self):
        for explanation in ([{"var": 0, "val": 0}], [{"var": 0, "val": 1}],
                            [{"var": 1, "val": -1}]):
            query, proof = fixture("solver_relu_aux_active")
            proof["proof"]["lemmas"][0]["expl"] = explanation
            with self.subTest(explanation=explanation), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_auxiliary_lower_explanation_keeps_tiny_coefficients(self):
        query, proof = fixture("solver_relu_aux_active")
        epsilon = Fraction(1, 10**20)
        proof["proof"]["lemmas"][0]["expl"][0]["val"] = -1 + epsilon
        _, cert = adapter.reconstruct(query, proof)
        self.assertEqual(cert.bound.value, Fraction(1, 2) - Fraction(3, 2) * epsilon)

    def test_auxiliary_lower_uses_correct_ground_bound_directions(self):
        for key, variable, value in (("upperBounds", 4, 3), ("lowerBounds", 3, 0)):
            query, proof = fixture("solver_relu_aux")
            query[key][variable] = proof[key][variable] = value
            with self.subTest(key=key, variable=variable), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)
        query, proof = fixture("solver_relu_aux")
        query["lowerBounds"][4] = proof["lowerBounds"][4] = 1
        _, cert = adapter.reconstruct(query, proof)
        self.assertEqual(cert.bound.value, Fraction(-7, 4))

    def test_auxiliary_empty_and_exact_zero_explanations(self):
        for explanation in ([], [{"var": 0, "val": 0}]):
            query, proof = fixture("solver_relu_aux")
            proof["proof"]["lemmas"][0]["expl"] = explanation
            proof["proof"]["lemmas"][0]["bound"] = 2
            _, cert = adapter.reconstruct(query, proof)
            if explanation:
                self.assertIsInstance(cert, adapter.LinearBound)
                cert = cert.child
            self.assertIsInstance(cert, adapter.ReluAuxUpper)
            self.assertEqual(cert.input_lower, -2)
            self.assertEqual(cert.auxiliary_upper, 2)

    def test_auxiliary_conclusion_is_checked_without_tolerance(self):
        for name, bound in (("solver_relu_aux", Fraction(7, 4)),
                            ("solver_relu_aux_active", Fraction(0))):
            query, proof = fixture(name)
            proof["proof"]["lemmas"][0]["bound"] = bound - Fraction(1, 10**20)
            with self.subTest(name=name), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)
        query, proof = fixture("solver_relu_aux_active")
        proof["proof"]["lemmas"][0]["bound"] = Fraction(1, 8)
        _, cert = adapter.reconstruct(query, proof)
        self.assertEqual(cert.child.auxiliary_upper, Fraction(1, 8))

    def test_auxiliary_metadata_does_not_establish_equation(self):
        query, proof = fixture("solver_relu_aux_active")
        for obj in (query, proof):
            obj["tableau"].pop()  # Remove f-b-aux-s=0; keep the metadata.
        with self.assertRaisesRegex(adapter.ImportFailure, "cannot reconstruct"):
            adapter.reconstruct(query, proof)

    def test_auxiliary_equation_requires_both_zero_slack_bounds(self):
        for key, value in (("lowerBounds", -1), ("upperBounds", 1)):
            query, proof = fixture("solver_relu_aux_active")
            query[key][7] = proof[key][7] = value
            with self.subTest(key=key), self.assertRaisesRegex(adapter.ImportFailure, "cannot reconstruct"):
                adapter.reconstruct(query, proof)

    def test_auxiliary_metadata_cannot_substitute_an_unlinked_variable(self):
        query, proof = fixture("solver_relu_aux_active")
        for obj in (query, proof):
            obj["constraints"][0]["vars"][2] = 5
        proof["proof"]["lemmas"][0]["affVar"] = 5
        with self.assertRaisesRegex(adapter.ImportFailure, "cannot reconstruct"):
            adapter.reconstruct(query, proof)

    def test_auxiliary_active_capture_requires_its_lemma(self):
        query, proof = fixture("solver_relu_aux_active")
        proof["proof"]["lemmas"] = []
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_auxiliary_relaxed_satisfiable_query_rejects_certificate(self):
        # b=z=f=1/2, aux=w=0, slacks=0 now satisfy the entire ReLU query.
        query, proof = fixture("solver_relu_aux_active")
        query["lowerBounds"][3] = proof["lowerBounds"][3] = 0
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_checked_lower_premise_is_not_a_native_ground_update(self):
        query, proof = fixture("solver_relu_aux_active")
        extra = copy.deepcopy(proof["proof"]["lemmas"][0])
        extra["expl"] = []
        proof["proof"]["lemmas"].append(extra)
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_auxiliary_conclusion_can_feed_a_later_explanation(self):
        query, proof = fixture("solver_relu_aux")
        extra = copy.deepcopy(proof["proof"]["lemmas"][0])
        extra["bound"] = Fraction(750001, 500000)
        proof["proof"]["lemmas"].insert(1, extra)
        _, cert = adapter.reconstruct(query, proof)
        second = cert.child.child
        self.assertIsInstance(second, adapter.LinearBound)
        self.assertEqual(second.bound.value, Fraction(-750001, 500000))
        self.assertIsInstance(second.child, adapter.ReluAuxUpper)

    def auxiliary_branch_fixture(self):
        query, proof = fixture("solver_relu_aux_active")
        for obj in (query, proof):
            obj["tableau"].append([{"var": i, "val": a} for i, a in
                                  ((8, -1), (9, 1), (10, -1), (11, -1))])
            obj["lowerBounds"].extend([-1, 0, 0, 0])
            obj["upperBounds"].extend([1, 1, 2, 0])
            obj["constraints"].append({"constraintType": 0, "vars": [8, 9, 10, 11]})
        active = copy.deepcopy(proof["proof"])
        inactive = copy.deepcopy(proof["proof"])
        active["split"] = [{"var": 8, "val": 0, "bound": "L"}, {"var": 10, "val": 0, "bound": "U"}]
        inactive["split"] = [{"var": 8, "val": 0, "bound": "U"}, {"var": 9, "val": 0, "bound": "U"}]
        proof["proof"] = {"children": [inactive, active]}
        return query, proof

    def test_auxiliary_evidence_under_independent_split(self):
        _, cert = adapter.reconstruct(*self.auxiliary_branch_fixture())
        for child in (cert.active, cert.inactive):
            self.assertEqual(child.bound, adapter.Bound(0, "L", Fraction(1, 2)))
            self.assertEqual(child.weights[:2], (0, 0))
            self.assertEqual(child.weights[3], 1)  # Negative original row 0, after phase equality.
            self.assertIsInstance(child.child, adapter.ReluAuxUpper)

    def test_auxiliary_evidence_cannot_leak_between_siblings(self):
        query, proof = self.auxiliary_branch_fixture()
        proof["proof"]["children"][0]["lemmas"] = []
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_bad_numeric_types(self):
        for value in (True, "0.25", 0.25, None, {"numerator": 1, "denominator": 0}):
            query, proof = fixture("linear")
            query["upperBounds"][0] = proof["upperBounds"][0] = value
            with self.subTest(value=value), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_bad_variable_indices(self):
        for value in (-1, 2, True, Fraction(0), "0"):
            query, proof = fixture("linear")
            query["tableau"][0][0]["var"] = proof["tableau"][0][0]["var"] = value
            with self.subTest(value=value), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_sparse_duplicate_rejected(self):
        query, proof = fixture("linear")
        for obj in (query, proof):
            obj["tableau"][0].append(copy.deepcopy(obj["tableau"][0][0]))
        with self.assertRaisesRegex(adapter.ImportFailure, "duplicate sparse"):
            adapter.reconstruct(query, proof)

    def test_wrong_dimensions(self):
        query, proof = fixture("linear")
        for obj in (query, proof):
            obj["lowerBounds"].pop()
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_unknown_fields_and_holes(self):
        for extra in ({"hole": True}, {"delegated": True}, {"sat": True},
                      {"lemma": "trusted"}):
            query, proof = fixture("linear")
            proof["proof"].update(extra)
            with self.subTest(extra=extra), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_empty_leaf_rejected(self):
        for bad in ({}, {"contradiction": []}, {"children": []}):
            query, proof = fixture("linear")
            proof["proof"] = bad
            with self.subTest(bad=bad), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_root_split_rejected(self):
        query, proof = fixture("linear")
        proof["proof"]["split"] = [{"var": 0, "val": -10, "bound": "U"}]
        with self.assertRaisesRegex(adapter.ImportFailure, "root split"):
            adapter.reconstruct(query, proof)

    def test_unproved_lemmas_rejected(self):
        query, proof = fixture("linear")
        proof["proof"]["lemmas"] = [{"affVar": 0, "affBound": "U", "bound": -10}]
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_propagation_evidence_is_needed(self):
        for name in ("propagation", "propagation_positive", "propagation_chain"):
            query, proof = fixture(name)
            proof["proof"]["lemmas"] = []
            with self.subTest(name=name), self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
                adapter.reconstruct(query, proof)

    def test_propagation_missing_fields_rejected(self):
        for field in ("affVar", "affBound", "bound", "causVar", "causBound", "constraint", "expl"):
            query, proof = fixture("propagation")
            del proof["proof"]["lemmas"][0][field]
            with self.subTest(field=field), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_propagation_unknown_fields_rejected(self):
        for extra in ({"trusted": True}, {"causVars": [0]}, {"expls": [[]]}, {"inputUpper": -1}):
            query, proof = fixture("propagation")
            proof["proof"]["lemmas"][0].update(extra)
            with self.subTest(extra=extra), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_other_propagation_rules_rejected(self):
        for field, value in (("constraint", 1), ("constraint", False),
                             ("causBound", "L"), ("affBound", "L")):
            query, proof = fixture("propagation")
            proof["proof"]["lemmas"][0][field] = value
            with self.subTest(field=field, value=value), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_invalid_nonempty_propagation_conclusions_rejected(self):
        for weight in (1, -1):
            query, proof = fixture("propagation")
            proof["proof"]["lemmas"][0]["expl"] = [{"var": 0, "val": weight}]
            with self.subTest(weight=weight), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_exact_zero_explanation_uses_ground_bound(self):
        query, proof = fixture("propagation")
        proof["proof"]["lemmas"][0]["expl"] = [{"var": 0, "val": 0}]
        _, cert = adapter.reconstruct(query, proof)
        self.assertIsInstance(cert, adapter.LinearBound)
        self.assertEqual(cert.bound, adapter.Bound(0, "U", Fraction(-1, 2)))
        self.assertIsInstance(cert.child, adapter.ReluUpper)

    def test_explained_premise_has_exact_value_and_witness(self):
        for name, upper in (("explained_positive", Fraction(1, 2)),
                            ("explained_negative", Fraction(-1, 2))):
            with self.subTest(name=name):
                instance, cert = adapter.reconstruct(*fixture(name))
                self.assertEqual(cert.bound, adapter.Bound(0, "U", upper))
                self.assertEqual(cert.weights[2], 1)  # -w times original row 1
                self.assertEqual(cert.weights[11], 2)  # 2 * upper(z)
                self.assertEqual(cert.weights[12], 1)  # lower(p)
                self.assertEqual(cert.weights[17], 1)  # upper(s)
                adapter.validate_implication(instance.query, instance.n, cert.bound, cert.weights)
                self.assertEqual(cert.child.input_upper, upper)

    def test_explanation_is_needed_for_non_ground_premise(self):
        for name in ("explained_negative", "explained_positive"):
            query, proof = fixture(name)
            proof["proof"]["lemmas"][0]["expl"] = []
            with self.subTest(name=name), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_explanation_schema_is_strict(self):
        bad_explanations = [
            None, {}, [0], [{"var": 1}], [{"var": 1, "val": -1, "trusted": True}],
            [{"var": 1, "val": -1}, {"var": 1, "val": -1}],
        ]
        bad_explanations += [[{"var": i, "val": -1}] for i in (-1, 2, 6, True, Fraction(1))]
        bad_explanations += [[{"var": 1, "val": x}] for x in (False, -1.0, "-1", None)]
        for explanation in bad_explanations:
            query, proof = fixture("explained_positive")
            proof["proof"]["lemmas"][0]["expl"] = explanation
            with self.subTest(explanation=explanation), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_explanation_sign_and_row_are_checked(self):
        for explanation in ([{"var": 1, "val": 0}], [{"var": 1, "val": 1}],
                            [{"var": 0, "val": -1}]):
            query, proof = fixture("explained_positive")
            proof["proof"]["lemmas"][0]["expl"] = explanation
            with self.subTest(explanation=explanation), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_explanation_does_not_drop_small_coefficients(self):
        query, proof = fixture("explained_positive")
        proof["proof"]["lemmas"][0]["expl"][0]["val"] = -1 + Fraction(1, 10**20)
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_negative_coefficient_uses_lower_ground_bound(self):
        query, proof = fixture("explained_positive")
        query["lowerBounds"][4] = proof["lowerBounds"][4] = Fraction(1, 4)
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)
        query, proof = fixture("explained_positive")
        query["upperBounds"][4] = proof["upperBounds"][4] = 100
        _, cert = adapter.reconstruct(query, proof)
        self.assertEqual(cert.bound.value, Fraction(1, 2))

    def test_linear_premise_does_not_update_native_ground_state(self):
        for explanation in ([], [{"var": 1, "val": Fraction(-1, 2)}]):
            query, proof = fixture("explained_positive")
            next_lemma = copy.deepcopy(proof["proof"]["lemmas"][0])
            next_lemma["expl"] = explanation
            proof["proof"]["lemmas"].append(next_lemma)
            with self.subTest(explanation=explanation), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def explained_branch_fixture(self):
        query, proof = fixture("explained_positive")
        for obj in (query, proof):
            obj["tableau"].append([{"var": i, "val": a} for i, a in
                                  ((7, -1), (8, 1), (9, -1), (10, -1))])
            obj["lowerBounds"].extend([-1, 0, 0, 0])
            obj["upperBounds"].extend([1, 1, 2, 0])
            obj["constraints"].append({"constraintType": 0, "vars": [7, 8, 9, 10]})
        active = copy.deepcopy(proof["proof"])
        inactive = copy.deepcopy(proof["proof"])
        active["split"] = [{"var": 7, "val": 0, "bound": "L"}, {"var": 9, "val": 0, "bound": "U"}]
        inactive["split"] = [{"var": 7, "val": 0, "bound": "U"}, {"var": 8, "val": 0, "bound": "U"}]
        proof["proof"] = {"children": [inactive, active]}
        return query, proof

    def test_explanation_indices_still_refer_to_original_rows_under_split(self):
        _, cert = adapter.reconstruct(*self.explained_branch_fixture())
        for child in (cert.active, cert.inactive):
            self.assertIsInstance(child, adapter.LinearBound)
            self.assertEqual(child.bound.value, Fraction(1, 2))
            self.assertEqual(child.weights[4], 1)
            self.assertEqual(child.weights[:4], (0, 0, 0, 0))

    def test_explained_premise_cannot_leak_between_siblings(self):
        query, proof = self.explained_branch_fixture()
        proof["proof"]["children"][0]["lemmas"][0]["expl"] = []
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_linear_implication_local_check_rejects_forged_weights(self):
        instance, cert = adapter.reconstruct(*fixture("explained_positive"))
        malformed = [cert.weights[:-1], cert.weights + (0,)]
        for i in (2, 11, 12, 17):
            weights = list(cert.weights)
            weights[i] = -1 if i == 2 else 0
            malformed.append(weights)
        for weights in malformed:
            with self.subTest(weights=weights), self.assertRaises(adapter.ImportFailure):
                adapter.validate_implication(instance.query, instance.n, cert.bound, weights)
        with self.assertRaisesRegex(adapter.ImportFailure, "no exact linear implication"):
            adapter.validate_implication(instance.query, instance.n,
                                         adapter.Bound(0, "U", Fraction(1, 2) - Fraction(1, 10**20)),
                                         cert.weights)

    def test_explained_lemmas_charge_two_nodes_to_limits(self):
        query, proof = fixture("explained_positive")
        proof["proof"]["lemmas"] *= adapter.MAX_DEPTH // 2 + 1
        with self.assertRaisesRegex(adapter.ImportFailure, "exceeds limits"):
            adapter.reconstruct(query, proof)

    def test_propagation_matches_exact_relu_pair(self):
        for x, y in ((1, 0), (2, 1), (0, 2), (3, 1)):
            query, proof = fixture("propagation")
            proof["proof"]["lemmas"][0].update(causVar=x, affVar=y)
            with self.subTest(pair=(x, y)), self.assertRaisesRegex(adapter.ImportFailure, "input/output"):
                adapter.reconstruct(query, proof)

    def test_propagation_indices_are_validated(self):
        for field in ("causVar", "affVar"):
            for value in (-1, 4, True, Fraction(1), "1"):
                query, proof = fixture("propagation")
                proof["proof"]["lemmas"][0][field] = value
                with self.subTest(field=field, value=value), self.assertRaises(adapter.ImportFailure):
                    adapter.reconstruct(query, proof)

    def test_propagation_without_relu_rejected(self):
        query, proof = fixture("propagation")
        query["constraints"] = proof["constraints"] = []
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_propagation_conclusion_never_uses_tolerance(self):
        for name, bound in (("propagation", -Fraction(1, 10**20)),
                            ("propagation_positive", Fraction(1, 2) - Fraction(1, 10**20))):
            query, proof = fixture(name)
            proof["proof"]["lemmas"][0]["bound"] = bound
            with self.subTest(name=name), self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
                adapter.reconstruct(query, proof)

    def test_weaker_propagation_conclusion_is_valid(self):
        query, proof = fixture("propagation_positive")
        proof["proof"]["lemmas"][0]["bound"] = Fraction(5, 8)
        _, cert = adapter.reconstruct(query, proof)
        self.assertEqual(cert.output_upper, Fraction(5, 8))

    def test_propagation_uses_current_input_bound(self):
        query, proof = fixture("propagation_positive")
        # With x0's upper bound changed to 1, x0 = x1 = 3/4 is a model.
        # The old output conclusion 1/2 must not survive this change.
        query["upperBounds"][0] = proof["upperBounds"][0] = 1
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_propagation_chain_cannot_use_future_premise(self):
        query, proof = fixture("propagation_chain")
        proof["proof"]["lemmas"].reverse()
        with self.assertRaisesRegex(adapter.ImportFailure, "too strong"):
            adapter.reconstruct(query, proof)

    def test_propagation_chain_checks_each_step(self):
        for missing in (0, 1):
            query, proof = fixture("propagation_chain")
            del proof["proof"]["lemmas"][missing]
            with self.subTest(missing=missing), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_propagation_does_not_leak_between_siblings(self):
        # Reconstruction visits active first. Inactive may not borrow its lemma.
        query, proof = fixture("propagation_tree")
        proof["proof"]["children"][0]["lemmas"] = []
        with self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
            adapter.reconstruct(query, proof)

    def test_propagation_on_removed_relu_rejected(self):
        query, proof = fixture("relu")
        _, propagation = fixture("propagation")
        proof["proof"]["children"][1]["lemmas"] = propagation["proof"]["lemmas"]
        with self.assertRaisesRegex(adapter.ImportFailure, "removed ReLU"):
            adapter.reconstruct(query, proof)

    def test_propagation_also_works_before_a_split(self):
        query, proof = fixture("propagation_tree")
        proof["proof"]["lemmas"] = proof["proof"]["children"][0]["lemmas"]
        for child in proof["proof"]["children"]:
            child["lemmas"] = []
        _, cert = adapter.reconstruct(query, proof)
        self.assertIsInstance(cert, adapter.ReluUpper)
        self.assertIsInstance(cert.child, adapter.Split)

    def test_propagation_counts_towards_resource_limits(self):
        query, proof = fixture("propagation")
        proof["proof"]["lemmas"] *= adapter.MAX_DEPTH + 1
        with self.assertRaisesRegex(adapter.ImportFailure, "exceeds limits"):
            adapter.reconstruct(query, proof)

    def test_branch_count(self):
        for count in (0, 1, 3):
            query, proof = fixture("relu")
            proof["proof"]["children"] = [proof["proof"]["children"][0]] * count
            with self.subTest(count=count), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_duplicate_phase_rejected(self):
        query, proof = fixture("relu")
        proof["proof"]["children"][1] = copy.deepcopy(proof["proof"]["children"][0])
        with self.assertRaisesRegex(adapter.ImportFailure, "both phases"):
            adapter.reconstruct(query, proof)

    def test_children_reordering(self):
        query, proof = fixture("relu")
        expected = adapter.reconstruct(query, proof)
        proof["proof"]["children"].reverse()
        self.assertEqual(adapter.reconstruct(query, proof), expected)

    def test_stronger_branch_assumption_rejected(self):
        query, proof = fixture("relu")
        proof["proof"]["children"][0]["split"][0]["val"] = -1
        with self.assertRaisesRegex(adapter.ImportFailure, "both phases"):
            adapter.reconstruct(query, proof)

    def test_extra_split_bound_rejected(self):
        query, proof = fixture("relu")
        proof["proof"]["children"][0]["split"].append({"var": 0, "val": -10, "bound": "U"})
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_unsupported_activation_rejected(self):
        query, proof = fixture("relu")
        for obj in (query, proof):
            obj["constraints"][0]["constraintType"] = 1
        with self.assertRaisesRegex(adapter.ImportFailure, "only ReLU"):
            adapter.reconstruct(query, proof)

    def test_missing_auxiliary_metadata_rejected(self):
        query, proof = fixture("relu")
        for obj in (query, proof):
            obj["constraints"][0]["vars"].pop()
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_bad_row_indices(self):
        for row in (-1, 1, True):
            query, proof = fixture("linear")
            proof["proof"]["contradiction"][0]["var"] = row
            with self.subTest(row=row), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_duplicate_row_index(self):
        query, proof = fixture("linear")
        proof["proof"]["contradiction"] *= 2
        with self.assertRaises(adapter.ImportFailure):
            adapter.reconstruct(query, proof)

    def test_corrupt_row_combination(self):
        for weight in (0, -1):
            query, proof = fixture("linear")
            proof["proof"]["contradiction"][0]["val"] = weight
            with self.subTest(weight=weight), self.assertRaisesRegex(adapter.ImportFailure, "exact constant"):
                adapter.reconstruct(query, proof)

    def test_zero_margin_and_small_positive_margin(self):
        # At x0 = x1 = 1/2 the query is satisfiable. No tolerance may turn
        # the zero or positive upper combination bound into a contradiction.
        for epsilon in (Fraction(0), Fraction(1, 10**20)):
            query, proof = fixture("linear")
            query["upperBounds"][0] = proof["upperBounds"][0] = Fraction(1, 2) + epsilon
            with self.subTest(epsilon=epsilon), self.assertRaises(adapter.ImportFailure):
                adapter.reconstruct(query, proof)

    def test_tiny_exact_contradiction(self):
        query, proof = fixture("linear")
        query["upperBounds"][0] = proof["upperBounds"][0] = Fraction(1, 2) - Fraction(1, 10**20)
        adapter.reconstruct(query, proof)

    def test_auxiliary_bound_is_not_an_assumption(self):
        query, proof = fixture("relu")
        # Disconnect aux from the ReLU: aux = tableauAux = 1, while b = f = 0
        # is a model. Blindly assuming the native active bound aux <= 0 would
        # let the forged row combination close this satisfiable active phase.
        for obj in (query, proof):
            obj["tableau"][0] = [{"var": 2, "val": 1}, {"var": 3, "val": -1}]
            obj["lowerBounds"][1] = 0
            obj["lowerBounds"][3] = 1
            obj["upperBounds"][3] = 1
        proof["proof"]["children"][1]["contradiction"][0]["val"] = 1
        with self.assertRaisesRegex(adapter.ImportFailure, "cannot reconstruct"):
            adapter.reconstruct(query, proof)

    def test_invalid_theory_name_cannot_inject_syntax(self):
        instance, cert = adapter.reconstruct(*fixture("linear"))
        with self.assertRaises(adapter.ImportFailure):
            adapter.render_theory('X\nbegin', instance, cert, "0" * 64, "0" * 64)

    def test_cli_separate_session(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory) / "Imported_Check.thy"
            result = adapter.main(["--query", str(FIXTURES / "linear_query.json"),
                                   "--certificate", str(FIXTURES / "linear.json"),
                                   "--output", str(output), "--session"])
            self.assertEqual(result, 0)
            self.assertTrue(output.exists())
            self.assertIn("quick_and_dirty = false", output.with_name("ROOT").read_text())


if __name__ == "__main__":
    unittest.main()
