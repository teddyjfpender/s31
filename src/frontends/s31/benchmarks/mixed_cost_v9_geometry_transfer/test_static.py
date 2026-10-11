#!/usr/bin/env python3
"""Native-free controls for V9 geometry and fresh claim inventory."""

from __future__ import annotations

import importlib.util
import unittest

import protocol as p


class ProtocolStaticTest(unittest.TestCase):
    def test_three_orthogonal_sources_and_frozen_v8_prediction(self) -> None:
        value = p.prepare_value()
        self.assertEqual(set(value["source_roster"]), set(p.SOURCES))
        self.assertEqual(value["scored_claim_indices"], [1, 80])
        axes = {entry["geometry_axis"] for entry in value["source_roster"].values()}
        self.assertEqual(axes, {"gate", "chip", "both"})
        self.assertEqual(value["v8_model_sha256"], p.sha(p.MODEL.read_bytes()))
        all_source_hashes = set()
        all_claim_hashes = set()
        first_prediction = next(iter(value["source_roster"].values()))["prediction"]
        for name, entry in value["source_roster"].items():
            self.assertEqual(entry["call_count"], 1)
            self.assertEqual(entry["source_sha256"], p.sha(p.source(name)))
            self.assertEqual(entry["source_nodes"], 5 + p.SOURCES[name]["gates"])
            self.assertEqual(entry["chip_rounds"], p.SOURCES[name]["rounds"])
            self.assertEqual(entry["live_mul_chain"], p.SOURCES[name]["gates"])
            self.assertEqual(entry["expected_geometry"]["slot_trace_logs"],
                             [10 if p.SOURCES[name]["gates"] else 9,
                              10 if p.SOURCES[name]["rounds"] > 16 else 4, 4])
            all_source_hashes.add(entry["source_sha256"])
            self.assertEqual(len(entry["assignment_sha256"]), 81)
            self.assertEqual(len(entry["statement_sha256"]), 81)
            for index in range(81):
                source, assignment, statement = p.case(name, index)
                self.assertEqual(source, p.source(name))
                self.assertEqual(entry["assignment_sha256"][index], p.sha(assignment))
                self.assertEqual(entry["statement_sha256"][index], p.sha(statement))
            all_claim_hashes.update(entry["assignment_sha256"])
            all_claim_hashes.update(entry["statement_sha256"])
            self.assertEqual(entry["prediction"], first_prediction)
        self.assertEqual(len(all_source_hashes), 3)
        self.assertEqual(len(all_claim_hashes), 486)

    def test_runner_order_and_manifest_geometry_guard(self) -> None:
        spec = importlib.util.spec_from_file_location("v9_geometry_study", p.HERE / "study.py")
        self.assertIsNotNone(spec)
        self.assertIsNotNone(spec.loader)
        study = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(study)
        self.assertEqual(study.TRIALS[:2], ((0, 0), (0, 1)))
        self.assertEqual(study.TRIALS[2:], tuple((index, 0)
                                                  for index in range(1, p.CLAIMS + 1)))
        self.assertEqual(len(study.TRIALS), 82)
        baseline = {"schema": "s31-mixed-component-inspection-general-v3",
                    "source_sha256": "s", "call_count": 1, "slot_count": 3,
                    "interaction_pow_bits": 20,
                    "pcs": {"fri_config": {"pow_bits": 26}},
                    "slots": [{"trace_log_size": 10, "n_constraints": 11},
                              {"trace_log_size": 4, "n_constraints": 6},
                              {"trace_log_size": 4, "n_constraints": 13}],
                    "calls": [{"rounds": 16}],
                    "tree_columns": [8, 29, 36, 8], "total_constraints": 30,
                    "main_columns": 29, "interaction_columns": 36,
                    "max_column_log_size": 10, "composition_log_size": 10,
                    "registry_manifest_sha256": "digest"}
        expected = {"source_sha256": "s", "call_count": 1, "chip_rounds": 16,
                    "expected_geometry": {"slots": 3, "constraints": 30,
                                          "tree_columns": [8, 29, 36, 8],
                                          "slot_trace_logs": [10, 4, 4],
                                          "max_column_log_size": 10,
                                          "composition_log_size": 10}}
        original = study.registry_manifest_digest
        study.registry_manifest_digest = lambda _: "digest"
        try:
            study.check_manifest(baseline, expected)
            for changed in ({**baseline, "max_column_log_size": 9},
                            {**baseline, "slots": [{**baseline["slots"][0],
                                                  "trace_log_size": 9},
                                                 *baseline["slots"][1:]]},
                            {**baseline, "calls": [{"rounds": 1024}]}):
                with self.assertRaises(ValueError):
                    study.check_manifest(changed, expected)
        finally:
            study.registry_manifest_digest = original


if __name__ == "__main__":
    unittest.main()
