#!/usr/bin/env python3
"""Native-free V11 source, model, claim, and manifest guards."""

from __future__ import annotations

import importlib.util
import unittest

import model as m
import protocol as p


class UnseenStaticTest(unittest.TestCase):
    def test_extrapolation_is_explicitly_outside_v10_fit(self) -> None:
        model = m.fit()
        self.assertEqual(m.canonical(model), m.FROZEN.read_bytes())
        self.assertEqual(len(model["allowed_log_pairs_and_calls"]), 4)
        self.assertIn("mixed-cost-v10-geometry-transfer-result.json",
                      model["excluded_from_training"])
        self.assertIn("paired-mixed-vs-direct-v1-result.json",
                      model["excluded_from_training"])
        self.assertEqual(model["training_artifacts"], list(m.v10.INPUTS))
        for calls, circuit, chip in model["allowed_log_pairs_and_calls"]:
            self.assertEqual(max(circuit, chip), 11)
            self.assertGreater(m.prediction(model, calls, (circuit, chip))[
                "proof_bytes_center"], 0)
        with self.assertRaises(ValueError):
            m.prediction(model, 1, (10, 10))
        with self.assertRaises(ValueError):
            m.prediction(model, 3, (9, 11))

    def test_four_fresh_sources_claims_and_oracles(self) -> None:
        value = p.prepare_value()
        self.assertEqual(set(value["source_roster"]), set(p.SOURCES))
        self.assertEqual(value["scored_claim_indices"], [1, 20])
        self.assertEqual(value["v11_model_sha256"], p.sha(p.MODEL.read_bytes()))
        seen_sources: set[str] = set()
        seen_claims: set[str] = set()
        for name, expected in value["source_roster"].items():
            spec = p.SOURCES[name]
            count = len(spec["rounds"])
            self.assertEqual(expected["call_count"], count)
            self.assertEqual(expected["chip_rounds"], list(spec["rounds"]))
            self.assertEqual(expected["source_sha256"], p.sha(p.source(name)))
            self.assertEqual(expected["expected_geometry"]["slots"], 1 + 2 * count)
            self.assertEqual(expected["expected_geometry"]["constraints"], 11 + 19 * count)
            self.assertEqual(expected["expected_geometry"]["slot_trace_logs"],
                             [11 if spec["gates"] else 9] +
                             [entry for rounds in spec["rounds"]
                              for entry in (rounds.bit_length() - 1, 4)])
            self.assertEqual(expected["expected_geometry"]["max_column_log_size"], 11)
            self.assertNotIn(expected["source_sha256"], seen_sources)
            seen_sources.add(expected["source_sha256"])
            for index in range(p.CLAIMS + 1):
                source, assignment, statement = p.case(name, index)
                self.assertEqual(source, p.source(name))
                self.assertEqual(expected["assignment_sha256"][index], p.sha(assignment))
                self.assertEqual(expected["statement_sha256"][index], p.sha(statement))
                for digest in (p.sha(assignment), p.sha(statement)):
                    self.assertNotIn(digest, seen_claims)
                    seen_claims.add(digest)
        self.assertEqual(len(seen_sources), 4)
        self.assertEqual(len(seen_claims), 8 * (p.CLAIMS + 1))

    def test_native_manifest_guard_checks_two_call_roster(self) -> None:
        spec = importlib.util.spec_from_file_location("v11_study", p.HERE / "study.py")
        self.assertIsNotNone(spec)
        self.assertIsNotNone(spec.loader)
        study = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(study)
        self.assertEqual(study.TRIALS[:2], ((0, 0), (0, 1)))
        self.assertEqual(len(study.TRIALS), p.CLAIMS + 2)
        expected = p.prepare_value()["source_roster"]["serial_surge_n2"]
        geometry = expected["expected_geometry"]
        manifest = {"schema": "s31-mixed-component-inspection-general-v3",
                    "source_sha256": expected["source_sha256"],
                    "call_count": 2, "slot_count": 5,
                    "interaction_pow_bits": 20, "pcs": {"fri_config": {"pow_bits": 26}},
                    "slots": [{"trace_log_size": log, "n_constraints": constraints}
                              for log, constraints in zip(geometry["slot_trace_logs"],
                                                          (11, 6, 13, 6, 13), strict=True)],
                    "calls": [{"rounds": rounds} for rounds in expected["chip_rounds"]],
                    "tree_columns": geometry["tree_columns"],
                    "total_constraints": geometry["constraints"],
                    "main_columns": geometry["tree_columns"][1],
                    "interaction_columns": geometry["tree_columns"][2],
                    "max_column_log_size": 11, "composition_log_size": 11,
                    "registry_manifest_sha256": "digest"}
        original = study.registry_manifest_digest
        study.registry_manifest_digest = lambda _: "digest"
        try:
            study.check_manifest(manifest, expected)
            changed_round = {**manifest, "calls": [{"rounds": 2048}, {"rounds": 32}]}
            changed_slot = {**manifest, "slots": [{**manifest["slots"][0],
                                                  "trace_log_size": 10}, *manifest["slots"][1:]]}
            for changed in (changed_round, changed_slot):
                with self.assertRaises(ValueError):
                    study.check_manifest(changed, expected)
        finally:
            study.registry_manifest_digest = original


if __name__ == "__main__":
    unittest.main()
