"""Finite accepted-roster occupancy and point-partition controls for P05."""

from __future__ import annotations

import copy
import hashlib
import json
import sys
import unittest
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(REPO / "scripts/release"))
import pcs_fri_sparse_p05_paper_ensemble as paper  # noqa: E402


class SparsePaperEnsembleTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.evidence = json.loads(paper.EVIDENCE.read_text())

    def test_exact_conditional_occupancies_keep_native_M_null(self) -> None:
        result = paper.derive(self.evidence)
        expected = {
            "base_single_Q": ([28, 56, 38], 56),
            "shifted_single_Q": ([8, 8, 8], 8),
            "joint_multi_Q_repeated_original": ([36, 64, 46], 64),
            "joint_multi_Q_deduplicated_original": ([32, 60, 42], 60),
        }
        for name, (sizes, maximum) in expected.items():
            batch = result["conditional_ensembles"][name]
            self.assertEqual([d["conditional_M_i"] for d in batch["domains"]], sizes)
            self.assertEqual(batch["conditional_common_padded_M"], maximum)
            for domain in batch["domains"]:
                self.assertEqual(len(domain["words"]), domain["conditional_M_i"])
        partition = result["accepted_point_partition"]
        self.assertEqual(len(partition["base_claim_indices"]), 61)
        self.assertEqual(len(partition["shifted_claim_indices"]), 12)
        self.assertEqual(sorted(partition["base_claim_indices"] +
                                partition["shifted_claim_indices"]), list(range(73)))
        self.assertEqual(result["native_source_point_projection"][
            "by_native_extended_log_size"], [
                {"height": 17, "doublings": 0},
                {"height": 11, "doublings": 6},
                {"height": 5, "doublings": 12},
            ])
        self.assertFalse(result["native_source_point_projection"]
                         ["paper_common_Q_equivalence_proven"])
        self.assertEqual(result["additional_native_periodicity_relation_words_by_height"],
                         [4, 4, 4])
        self.assertEqual(result["conditional_joint_width_if_periodicity_independent"]
                         ["repeated_original"], [40, 68, 50])
        self.assertEqual(result["legacy_native_quotient_contributions"], {
            "explicit_ood": 73, "periodicity": 12,
            "total_accumulated": 85, "independently_degree_tested": False,
            "lifted_log17_periodicity_duplicates_sample1_at_height17": 4,
            "height_local_periodicity_duplicates_sample1_at_all_heights": 12,
            "coefficient_compression_theorem_proven": False,
        })
        repeated_height_17 = result["conditional_ensembles"][
            "joint_multi_Q_repeated_original"]["domains"][0]["words"]
        column_20 = [w for w in repeated_height_17 if w["source_ref"] == [2, 20]]
        self.assertEqual([w["role"] for w in column_20],
                         ["original", "native_own_quotient_candidate"] * 2)
        self.assertEqual([w.get("paired_claim_index", w.get("claim_index"))
                          for w in column_20], [57, 57, 58, 58])
        self.assertIsNone(result["native_to_paper_batch_width_M"])
        self.assertIsNone(result["native_proven_security_bits"])
        self.assertFalse(result["proven_release_admissible"])

    def test_point_partition_rejects_relabelled_accepted_claims(self) -> None:
        base = self.evidence["accepted_capture"]
        for mutate in (
            lambda claims: claims[0].__setitem__("point_x_limbs",
                                                 base["claims"][57]["point_x_limbs"]),
            lambda claims: (claims[57].__setitem__("point_x_limbs",
                                                  base["claims"][58]["point_x_limbs"]),
                            claims[58].__setitem__("point_x_limbs",
                                                   base["claims"][57]["point_x_limbs"])),
        ):
            with self.subTest(mutate=mutate):
                bad = copy.deepcopy(self.evidence)
                claims = bad["accepted_capture"]["claims"]
                mutate(claims)
                # Keep the inner digest self-consistent: reject the semantic
                # point partition, not merely a stale checksum.
                bad["accepted_ood_claim_map_sha256"] = hashlib.sha256(json.dumps(
                    claims, sort_keys=True, separators=(",", ":")
                ).encode()).hexdigest()
                with self.assertRaises(ValueError):
                    paper.derive(bad)

    def test_checked_in_ensemble_is_current(self) -> None:
        self.assertEqual(paper.OUTPUT.read_text(),
                         paper.canonical_json(paper.derive(self.evidence)))


if __name__ == "__main__":
    unittest.main()
