#!/usr/bin/env python3
"""Native-free checks for paired fresh-statement diagnostic admission."""

import unittest

from fresh_assignments import balanced_order, stage_time, summary


class FreshAssignmentDiagnostic(unittest.TestCase):
    def test_balanced_process_positions(self) -> None:
        workers = [16, 18, 24, 32]
        orders = [balanced_order(workers, index, 0) for index in range(4)]
        self.assertEqual([sorted(order) for order in orders], [workers] * 4)
        for position in range(4):
            self.assertEqual({order[position] for order in orders}, set(workers))

    def test_stage_record_admission(self) -> None:
        line = b'S31_MIXED_STAGE_V1 {"stages_ns":{"native_prove_including_setup_ns":17}}\n'
        self.assertEqual(stage_time(line, 20), 17)
        with self.assertRaisesRegex(ValueError, "exactly one"):
            stage_time(line + line, 20)
        with self.assertRaisesRegex(ValueError, "exceeds"):
            stage_time(line, 16)
        with self.assertRaisesRegex(ValueError, "duplicate JSON key"):
            stage_time(b'S31_MIXED_STAGE_V1 {"stages_ns":{},"stages_ns":{}}\n', 20)

    def test_summary_uses_statements_and_requires_complete_pairs(self) -> None:
        records = [
            {"shape": "control_n2", "assignment": assignment, "round": round_id,
             "workers": worker, "native_prove_including_setup_ns": value}
            for assignment, pair in enumerate(((10_000_000, 20_000_000),
                                                (20_000_000, 40_000_000)))
            for round_id in range(2)
            for worker, value in zip((16, 18), pair)
        ]
        report = summary(records, [16, 18], 2, 2)["control_n2"]
        self.assertEqual(report["distinct_statements"], 2)
        self.assertEqual(report["median_native_prove_including_setup_ms"],
                         {"16": 15, "18": 30})
        self.assertEqual(report["median_paired_ratio_to_worker_18"]["16"], .5)
        with self.assertRaisesRegex(ValueError, "incomplete paired assignment"):
            summary(records[:-1], [16, 18], 2, 2)


if __name__ == "__main__":
    unittest.main()
