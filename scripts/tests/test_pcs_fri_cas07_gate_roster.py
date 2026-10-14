"""Fail-closed Gate-to-CAS07 metadata boundary tests."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts.release.pcs_fri_cas07_gate_roster import (
    derive_candidate_roster, require_production_equivalence,
)

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "src/frontends/s31/tests/python/security/fixtures/effects_gate_ownership/gate-component-roster.json"


def checked_shape() -> dict:
    """Build only the fields already checked by extract_gate in the real CLI."""
    roster = json.loads(FIXTURE.read_text())
    tables = [{"name": row["name"], "proof_index": row["proof_index"],
               "trace_log_size": row["trace_log_size"],
               "main_trace_columns": row["base_trace_columns"],
               "interaction_trace_columns": row["interaction_trace_columns"]}
              for row in roster["components"]]
    fixed = [{"id": row["id"], "commitment_index": row["commitment_index"],
              "log_size": row["log_size"]} for row in roster["preprocessed_columns"]]
    return {
        "lowering": "gate", "key_schema": "s31-verification-key-gate-roster-v1",
        "profile": "circuit-v1", "max_trace_log_size": 20,
        "package_checks": {"native_check_key": "accepted",
                           "package_manifest_sha256": "a" * 64,
                           "verification_key_sha256": "b" * 64},
        "source_binding": {"engine_gitlink": "e" * 40},
        "gate_final_domain": {"air_bundle_sha256": "c" * 64,
                              "source_sha256": {"runtime": "f" * 64}},
        "gate_trace_and_fri_schedule": {
            "status": "conditional_source_bound_geometry", "tables": tables,
            "preprocessed_columns": fixed,
            "pcs_commitment_trees": [
                {"kind": "preprocessed", "column_count": 45},
                {"kind": "main", "column_count": 114},
                {"kind": "interaction", "column_count": 152},
                {"kind": "composition", "column_count": 8},
            ],
        },
    }


class Cas07GateRosterTests(unittest.TestCase):
    def test_exact_roster_is_metadata_only_and_binds_empty_heights(self) -> None:
        result = derive_candidate_roster(checked_shape())
        self.assertEqual(result["binding"]["candidate_profile"]["columns_by_height"],
                         [51, 0, 8, 0, 15, 0, 8, 0, 0, 0, 0, 28, 8, 0, 0, 0, 193])
        self.assertEqual(result["source_words"], 56_708_112)
        self.assertEqual(result["source_plus_tree_estimated_bytes"], 293_941_280)
        self.assertEqual(result["unmapped_composition_columns"], 8)
        self.assertFalse(result["production_equivalent"])
        self.assertIsNone(result["native_proven_security_bits"])
        self.assertIsNone(result["published_batch_width_M_for_actual_proof"])
        self.assertEqual(result["selected_target"],
                         {"metric": "paper_work_factor_epsilon_over_T", "bits": 96,
                          "T_hash_queries": 1 << 64})
        self.assertTrue(result["hypothetical_paper_batching_term_if_M_equals_width"]["152"]
                        ["term_exceeds_2_pow_minus_96"])
        with self.assertRaisesRegex(ValueError, "does not establish production equivalence"):
            require_production_equivalence(result)

    def test_unreviewed_height_or_width_rejects(self) -> None:
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["tables"][1]["trace_log_size"] = 10
        with self.assertRaisesRegex(ValueError, "occupied heights changed"):
            derive_candidate_roster(changed)
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["tables"][1]["main_trace_columns"] += 1
        with self.assertRaisesRegex(ValueError, "source width changed"):
            derive_candidate_roster(changed)

    def test_source_order_and_key_gate_reject(self) -> None:
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["tables"][0]["proof_index"] = 1
        with self.assertRaisesRegex(ValueError, "table proof order changed"):
            derive_candidate_roster(changed)
        changed = checked_shape()
        changed["package_checks"]["native_check_key"] = "unsupported"
        with self.assertRaisesRegex(ValueError, "native check-key did not accept"):
            derive_candidate_roster(changed)

    def test_digest_changes_with_key_pin_and_boolean_integer_rejects(self) -> None:
        original = checked_shape()
        changed = copy.deepcopy(original)
        changed["package_checks"]["verification_key_sha256"] = "d" * 64
        self.assertNotEqual(derive_candidate_roster(original)["candidate_roster_sha256"],
                            derive_candidate_roster(changed)["candidate_roster_sha256"])
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["tables"][0]["main_trace_columns"] = True
        with self.assertRaisesRegex(ValueError, "invalid table width"):
            derive_candidate_roster(changed)


if __name__ == "__main__":
    unittest.main()
