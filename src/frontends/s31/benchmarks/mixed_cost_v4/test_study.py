"""Native-free tests of v4 measurement chronology and row selection."""

from __future__ import annotations

import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import study


class StudyV4Tests(unittest.TestCase):
    def test_trial_order_and_training_cut_are_fixed(self) -> None:
        self.assertEqual(study.TRIALS[:3], ((0, 0), (0, 1), (1, 0)))
        self.assertEqual(study.TRIALS[-1], (79, 0))
        self.assertEqual(len(study.TRIALS), 81)
        records = []
        for name, count in study.model.PROGRAMS.items():
            trials = []
            for ordinal, (index, repeat) in enumerate(study.TRIALS):
                trials.append({"ordinal": ordinal, "claim_index": index, "repeat": repeat,
                               "assignment_sha256": f"a-{name}-{index}-{repeat}",
                               "statement_sha256": f"s-{name}-{index}-{repeat}",
                               "first_verified_process_wall_ns": 100_000_000 if index == 0 else
                                   10_000_000 + count * 2_000_000 + index * 1000,
                               "partition_ns": {"fri_pow_ns": 1_000_000,
                                                "interaction_pow_ns": 100_000},
                               "proof_bytes": 1_000_000 if index == 0 else
                                   50_000 + count * 100 + index})
            records.append({"name": name, "call_count": count,
                            "source_sha256": name,
                            "trials": trials})
        value = study.model_from_training({"records": records}, "protocol", b"train")
        self.assertEqual(value["fit_rows"], 160)
        self.assertEqual(value["calibration_rows"], 156)
        self.assertEqual(value["proof_calibration_rank_1_based"], 142)
        self.assertLess(value["proof_intercept_bytes"], 100_000)
        self.assertEqual(len(value["training_assignment_sha256"]), 324)

    def test_manifest_rejects_changed_pow_and_geometry(self) -> None:
        protocol = {"manifest_interaction_pow_bits": 20, "manifest_fri_pow_bits": 26}
        source = {"source_sha256": "abc", "call_count": 3}
        manifest = {"schema": "s31-mixed-component-inspection-general-v3",
                    "source_sha256": "abc", "call_count": 3,
                    "interaction_pow_bits": 20, "pcs": {"fri_config": {"pow_bits": 26}},
                    "tree_columns": [8, 12, 16, 8], "main_columns": 12,
                    "interaction_columns": 16,
                    "calls": [{"call_id": i} for i in range(3)],
                    "slots": [{"n_constraints": 9} for _ in range(7)],
                    "slot_count": 7, "total_constraints": 63}
        study.check_manifest(manifest, source, protocol)
        with self.assertRaises(ValueError):
            study.check_manifest({**manifest, "interaction_pow_bits": 19}, source, protocol)
        with self.assertRaises(ValueError):
            study.check_manifest({**manifest, "slot_count": 0}, source, protocol)

    def test_prepare_and_anchor_refuse_unfrozen_work(self) -> None:
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(study, "PROTOCOL", Path(temp) / "protocol.json"), \
                 patch.object(study.v2, "git", return_value=b" M deps/stwo-zig\n"):
                with self.assertRaisesRegex(ValueError, "commit frontend"):
                    study.prepare()
        with self.assertRaisesRegex(ValueError, "full model SHA"):
            study.anchor_required("protocol", None, None)


if __name__ == "__main__":
    unittest.main()
