#!/usr/bin/env python3
"""Native-free controls for the clean V8 fit and fresh source inventory."""

from __future__ import annotations

import importlib.util
import unittest

import model
import protocol as p


class CalibratedModelTest(unittest.TestCase):
    def test_fit_uses_exact_clean_blocks_and_profile_widths(self) -> None:
        value = model.fit()
        self.assertEqual(len(value["fit_blocks"]), 8)
        self.assertEqual(set(value["fit_input_sha256"]), set(model.INPUTS))
        self.assertEqual([block["name"] for block in value["fit_blocks"]],
                         ["relay_n3", "relay_n7", "twist_n3", "twist_n7",
                          "scaled_seed_n1", "weighted_scan_n8",
                          "affine_seed_n1", "switchback_n8"])
        self.assertEqual(len(value["fri_source_exponential_scales_ns"]), 4)
        self.assertGreater(value["proof_relative_half_width_by_profile"]["small"],
                           value["proof_relative_half_width_by_profile"]["large"])
        self.assertGreater(value["proof_relative_half_width_by_profile"]["small"],
                           0.05)
        self.assertLess(value["proof_relative_half_width_by_profile"]["large"],
                        0.05)
        for count in (1, 8):
            predicted = model.prediction(value, count)
            q = predicted["warm_wall_quantile_ns"]
            self.assertLess(q["0.05"], q["0.5"])
            self.assertLess(q["0.5"], q["0.95"])
            band = predicted["source_rate_p50_envelope_ns"]
            self.assertLess(band[0], q["0.5"])
            self.assertLess(q["0.5"], band[1])

    def test_extreme_source_scale_changes_wall_forecast(self) -> None:
        value = model.fit()
        scales = value["fri_source_exponential_scales_ns"]
        self.assertGreater(model.wall_quantile(value, 8, 0.5, [max(scales)]),
                           model.wall_quantile(value, 8, 0.5, [min(scales)]))
        with self.assertRaises(ValueError):
            model.profile(5)


class ProtocolStaticTest(unittest.TestCase):
    def test_source_claims_and_prediction_are_frozen_before_zig(self) -> None:
        value = p.prepare_value()
        self.assertEqual(set(value["source_roster"]), set(p.NAMES))
        self.assertEqual(value["scored_claim_indices"], [1, 80])
        self.assertEqual([row["source_nodes"] for row in value["source_roster"].values()],
                         [5, 20])
        source_hashes = set()
        claims = set()
        for name, entry in value["source_roster"].items():
            self.assertEqual(entry["source_sha256"], p.sha(p.source(name)))
            source_hashes.add(entry["source_sha256"])
            self.assertEqual(len(entry["assignment_sha256"]), 81)
            self.assertEqual(len(entry["statement_sha256"]), 81)
            for index in range(81):
                source, assignment, statement = p.case(name, index)
                self.assertEqual(source, p.source(name))
                self.assertEqual(entry["assignment_sha256"][index], p.sha(assignment))
                self.assertEqual(entry["statement_sha256"][index], p.sha(statement))
            claims.update(entry["assignment_sha256"])
            claims.update(entry["statement_sha256"])
        self.assertEqual(len(source_hashes), 2)
        self.assertEqual(len(claims), 324)
        self.assertLess(value["source_roster"]["folded_seed_n1"]["prediction"]
                        ["proof_bytes_center"],
                        value["source_roster"]["braided_scan_n8"]["prediction"]
                        ["proof_bytes_center"])

    def test_runner_order_matches_frozen_cold_and_scored_design(self) -> None:
        spec = importlib.util.spec_from_file_location("v8_calibrated_study", p.HERE / "study.py")
        self.assertIsNotNone(spec)
        self.assertIsNotNone(spec.loader)
        runner = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(runner)
        self.assertEqual(runner.TRIALS[:2], ((0, 0), (0, 1)))
        self.assertEqual(runner.TRIALS[2:], tuple((index, 0)
                                                  for index in range(1, p.CLAIMS + 1)))
        self.assertEqual(len(runner.TRIALS), 82)


if __name__ == "__main__":
    unittest.main()
