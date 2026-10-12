#!/usr/bin/env python3
"""Native-free controls for the prospective v6 transfer inventory."""

from __future__ import annotations

import importlib.util
import unittest

import protocol as p


class ProtocolStaticTest(unittest.TestCase):
    def test_source_claims_and_prediction_are_frozen_before_zig(self) -> None:
        value = p.prepare_value()
        self.assertEqual(set(value["source_roster"]), set(p.NAMES))
        self.assertEqual(value["scored_claim_indices"], [1, 80])
        self.assertEqual([row["source_nodes"] for row in value["source_roster"].values()],
                         [4, 24])
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
        self.assertLess(value["source_roster"]["offset_seed_n1"]["prediction"]
                        ["proof_bytes_center"],
                        value["source_roster"]["crosswind_n8"]["prediction"]
                        ["proof_bytes_center"])

    def test_runner_order_matches_frozen_cold_and_scored_design(self) -> None:
        spec = importlib.util.spec_from_file_location("v6_transfer_study", p.HERE / "study.py")
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
