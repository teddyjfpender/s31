"""Fail-closed controls for the v0.1 published-proof blocker matrix."""

from __future__ import annotations

import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from scripts.release import pcs_fri_v01_blockers as gate


class PcsFriV01BlockersTests(unittest.TestCase):
    def test_complete_matrix_is_blocked_and_source_bound(self) -> None:
        report = gate.matrix()
        self.assertEqual(report["status"], "blocked")
        self.assertFalse(report["proven_release_admissible"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertEqual(set(report["profiles"]), set(gate.EXPECTED_PROFILE_STEPS))
        self.assertEqual(len(report["profiles"]), 12)
        obligations = {row["id"] for row in report["obligations"]}
        self.assertEqual(len(obligations), len(gate.OBLIGATIONS))
        self.assertTrue(all(row["status"] == "open" for row in report["obligations"]))
        self.assertTrue(all(row["gap_kind"] and row["published_requirement"] and
                            row["missing_discharge"] for row in report["obligations"]))
        self.assertIn("uninstantiated_theorem_premise",
                      {row["gap_kind"] for row in report["obligations"]})
        self.assertIn("unproven_native_refinement",
                      {row["gap_kind"] for row in report["obligations"]})
        for name, profile in report["profiles"].items():
            self.assertFalse(profile["proven_release_admissible"], name)
            self.assertIsNone(profile["native_proven_security_bits"], name)
            self.assertEqual(set(profile["blocker_ids"]),
                             obligations if profile["fri_fold_step"] == 4 else
                             obligations - {"P10_GROUPED_FOLD_SCHEDULE"})
        self.assertFalse(report["whole_prover_cost"]["current_engine_matches_v8r1"])
        self.assertEqual(report["query_epoch"]["counter_inputs"], list(range(9)))
        self.assertTrue(report["query_epoch"]["native_blake2s_counter_overflow_fail_closed"])
        self.assertFalse(report["query_epoch"]["full_transcript_counter_wrap_proven"])
        self.assertEqual(gate.encoded(report), gate.MATRIX.read_text())
        self.assertTrue(all(len(digest) == 64 for digest in report["evidence_sha256"].values()))

    def test_admission_never_follows_from_candidate_parameter_arithmetic(self) -> None:
        with contextlib.redirect_stdout(io.StringIO()) as output:
            code = gate.main(["--check", "--require-admissible"])
        self.assertEqual(code, 2)
        report = json.loads(output.getvalue())
        self.assertFalse(report["proven_release_admissible"])

    def test_stale_snapshot_and_roster_drift_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            stale = Path(directory) / "stale.json"
            stale.write_text("{}\n")
            with patch.object(gate, "MATRIX", stale), \
                    contextlib.redirect_stderr(io.StringIO()), \
                    self.assertRaises(SystemExit) as failure:
                gate.main(["--check"])
            self.assertEqual(failure.exception.code, 2)
        with patch.object(gate, "EXPECTED_PROFILE_STEPS", {"gate": 1}):
            with self.assertRaisesRegex(ValueError, "roster"):
                gate.matrix()
        with patch.object(gate, "FRI_CONFIG_SOURCES", ("scripts/release/README.md",)):
            with self.assertRaisesRegex(ValueError, "FRI tuple changed"):
                gate.matrix()


if __name__ == "__main__":
    unittest.main()
