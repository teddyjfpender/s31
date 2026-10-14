"""Source-bound checks for the accepted sparse Gate H3 candidate roster."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/release"))
import pcs_fri_sparse_p05_h3_roster as roster  # noqa: E402


class SparseH3RosterTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.evidence = json.loads(roster.EVIDENCE.read_text())

    def test_accepted_roster_covers_every_source_and_claim_once(self) -> None:
        result = roster.derive(self.evidence)
        self.assertEqual([h["candidate_direct_track_width"] for h in result["heights"]],
                         [32, 60, 42])
        self.assertEqual([h["candidate_width_if_periodicity_is_separate"]
                          for h in result["heights"]], [36, 64, 46])
        self.assertEqual(result["total_original_source_columns"], 61)
        self.assertEqual(result["total_direct_own_quotient_claims"], 73)
        self.assertEqual(result["total_legacy_periodicity_relation_words"], 12)
        self.assertEqual(result["heights"][0]["own_quotient_claim_refs"][2:4],
                         [[57, 2, 20, 0], [58, 2, 20, 1]])
        self.assertIsNone(result["conditional_paper_mapping"]["native_to_paper_batch_width_M"])
        self.assertIsNone(result["native_proven_security_bits"])
        self.assertFalse(result["proven_release_admissible"])

    def test_stale_or_corrupted_accepted_data_rejected(self) -> None:
        for mutate in (
            lambda d: d["package_checks"].__setitem__("proof_sha256", "00" * 32),
            lambda d: d["accepted_capture"]["columns"][1].__setitem__("first_claim_index", 0),
            lambda d: d["accepted_capture"]["columns"][1].__setitem__("root_index", 2),
            lambda d: d["accepted_capture"]["columns"][1].__setitem__("source_value_at_first_raw_query", -1),
            lambda d: d["accepted_capture"].__setitem__("first_raw_lifted_query_position", -1),
            lambda d: d["accepted_capture"]["claims"][0]["value_limbs"].__setitem__(0, 1),
            lambda d: d["accepted_capture"]["heights"][0].__setitem__("committed_input_log_size", 15),
            lambda d: d["candidate_paper_parameters"].__setitem__("B_from_sealed_fri_blowup", 4),
            lambda d: d.__setitem__("native_proven_security_bits", 96),
        ):
            with self.subTest(mutate=mutate):
                bad = copy.deepcopy(self.evidence)
                mutate(bad)
                with self.assertRaises(ValueError):
                    roster.derive(bad)

    def test_checked_in_manifest_and_lean_data_are_current(self) -> None:
        self.assertEqual(roster.OUTPUT.read_text(),
                         roster.canonical_json(roster.derive(self.evidence)))
        self.assertEqual(roster.LEAN.read_text(), roster.lean_data(self.evidence))


if __name__ == "__main__":
    unittest.main()
