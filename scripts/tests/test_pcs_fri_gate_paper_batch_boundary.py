"""Exact conditional Gate batching arithmetic and fail-closed source checks."""

from __future__ import annotations

import copy
import json
import tempfile
import unittest
from fractions import Fraction
from pathlib import Path

from scripts.release.pcs_fri_gate_paper_batch_boundary import (
    ENGINE_COMMIT, ENGINE_SHA256, F, T, TARGET, batching_term,
    checked_engine_sources, derive_boundary, require_paper_mapping,
)

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = ROOT / "src/frontends/s31/tests/python/security/fixtures/effects_gate_ownership/gate-component-roster.json"


def checked_shape() -> dict:
    """A report-shaped fixture; only the real CLI runs package check-key."""
    roster = json.loads(FIXTURE.read_text())
    return {
        "lowering": "gate", "key_schema": "s31-verification-key-gate-roster-v1",
        "profile": "circuit-v1", "max_trace_log_size": 20,
        "package_checks": {"native_check_key": "accepted",
                           "package_manifest_sha256": "a" * 64,
                           "verification_key_sha256": "b" * 64},
        "source_binding": {"engine_gitlink": ENGINE_COMMIT},
        "fri": {"log_blowup_factor": 1, "fold_step": 1, "raw_queries": 70},
        "gate_final_domain": {
            "status": "conditional_source_bound_geometry",
            "fri_input_domain_log": 21,
            "committed_composition_column_log_size": 20,
            "air_bundle_sha256": "c" * 64,
            "source_sha256": {"native_verifier": "e" * 64},
        },
        "gate_trace_and_fri_schedule": {
            "status": "conditional_source_bound_geometry",
            "preprocessed_columns": roster["preprocessed_columns"],
            "tables": [{"name": row["name"], "proof_index": row["proof_index"],
                        "trace_log_size": row["trace_log_size"],
                        "main_trace_columns": row["base_trace_columns"],
                        "interaction_trace_columns": row["interaction_trace_columns"]}
                       for row in roster["components"]],
            "pcs_commitment_trees": [
                {"kind": "preprocessed", "column_count": 45},
                {"kind": "main", "column_count": 114},
                {"kind": "interaction", "column_count": 152},
                {"kind": "composition", "column_count": 8},
            ],
        },
    }


class GatePaperBatchBoundaryTests(unittest.TestCase):
    def test_observed_roster_and_conditional_exact_cap(self) -> None:
        report = derive_boundary(checked_shape(), ENGINE_SHA256)
        self.assertEqual(report["native_commitment_widths"], [45, 114, 152, 8])
        self.assertEqual(report["native_source_columns_total"], 319)
        self.assertEqual(report["native_first_fri_domain_size"], 1 << 21)
        rows = report["binding"]["native_roster_by_log"]
        self.assertEqual([(row["source_log_size"], row["tree_columns"])
                          for row in rows], [
            (20, [3, 16, 32, 8]), (18, [3, 1, 4, 0]),
            (16, [4, 3, 8, 0]), (14, [3, 1, 4, 0]),
            (9, [8, 12, 8, 0]), (8, [3, 1, 4, 0]),
            (4, [21, 80, 92, 0]),
        ])
        geometry = report["conditional_paper_geometry_if_N_is_max_gate_trace_and_B_is_native_blowup"]
        self.assertEqual((geometry["N"], geometry["B"], geometry["D0_NB_squared"]),
                         (1 << 20, 2, 1 << 22))
        self.assertEqual(geometry["largest_M_whose_batching_term_with_R_at_least_1_fits_target"], 64)
        self.assertEqual(geometry["next_M_exceeds_target"], 65)
        self.assertEqual(geometry["field_size"], F)
        self.assertEqual(geometry["counterfactual_M_values"]["largest_single_native_height"]["assumed_M"], 193)
        self.assertTrue(geometry["counterfactual_M_values"]["largest_single_native_height"]
                        ["single_term_BCS_work_factor_with_R_at_least_1_exceeds_target"])
        self.assertEqual(batching_term(65, 1 << 20, 2), Fraction(64 * (1 << 22), F))
        self.assertLessEqual(batching_term(64, 1 << 20, 2) * Fraction(T + 1, T), TARGET)
        self.assertGreater(batching_term(65, 1 << 20, 2) * Fraction(T + 1, T), TARGET)
        self.assertIsNone(report["published_batch_width_M_for_actual_proof"])
        self.assertIsNone(report["native_proven_security_bits"])
        self.assertFalse(report["release_gate_admissible"])
        with self.assertRaisesRegex(ValueError, "no proved paper ensemble mapping"):
            require_paper_mapping(report)

    def test_change_in_key_changes_binding_but_not_admission(self) -> None:
        changed = checked_shape()
        changed["package_checks"]["verification_key_sha256"] = "d" * 64
        a = derive_boundary(checked_shape(), ENGINE_SHA256)
        b = derive_boundary(changed, ENGINE_SHA256)
        self.assertNotEqual(a["binding_sha256"], b["binding_sha256"])
        self.assertFalse(b["release_gate_admissible"])

    def test_roster_and_source_mismatch_rejected(self) -> None:
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["pcs_commitment_trees"][3]["column_count"] = 7
        with self.assertRaisesRegex(ValueError, "tree widths changed"):
            derive_boundary(changed, ENGINE_SHA256)
        changed = checked_shape()
        changed["gate_trace_and_fri_schedule"]["tables"][0]["main_trace_columns"] += 1
        with self.assertRaisesRegex(ValueError, "grouping disagrees"):
            derive_boundary(changed, ENGINE_SHA256)
        changed = checked_shape()
        changed["package_checks"]["native_check_key"] = "rejected"
        with self.assertRaisesRegex(ValueError, "check-key did not accept"):
            derive_boundary(changed, ENGINE_SHA256)
        changed = checked_shape()
        changed["source_binding"]["engine_gitlink"] = "e" * 40
        with self.assertRaisesRegex(ValueError, "gitlink changed"):
            derive_boundary(changed, ENGINE_SHA256)
        hashes = copy.deepcopy(ENGINE_SHA256)
        hashes[next(iter(hashes))] = "f" * 64
        with self.assertRaisesRegex(ValueError, "source hashes changed"):
            derive_boundary(checked_shape(), hashes)

    def test_exact_source_pin_fails_on_byte_change(self) -> None:
        self.assertEqual(checked_engine_sources(), ENGINE_SHA256)
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            for name in ENGINE_SHA256:
                dst = root / name
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes((ROOT / name).read_bytes())
            target = root / next(iter(ENGINE_SHA256))
            target.write_bytes(target.read_bytes() + b"\n")
            with self.assertRaisesRegex(ValueError, "reviewed PCS/FRI source changed"):
                checked_engine_sources(root)


if __name__ == "__main__":
    unittest.main()
