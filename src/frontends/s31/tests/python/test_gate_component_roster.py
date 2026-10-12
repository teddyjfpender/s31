"""Fail-closed package checks for the source-derived gate AIR roster."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.gate_component_roster import ARTIFACT, KEY_SCHEMA, NAMES, digest, validate


class GateComponentRosterTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.package = Path(self.temporary.name)
        self.roster = {
            "schema": "s31-component-roster-gate-v1", "profile": "circuit-v1",
            "program_sha256": "0" * 64, "canonical_ir_sha256": "1" * 64,
            "air_bundle_sha256": "2" * 64, "preprocessed_root": "3" * 64,
            "circuit_hash": "4" * 64, "claimed_sums": 11,
            "components": [
                {"name": name, "source_index": index, "proof_index": index,
                 "claimed_sum_index": index, "trace_log_size": 4,
                 "base_trace_columns": 4, "interaction_trace_columns": 4,
                 "log_size_source": "eq_in0_address",
                 "lookup_uses_per_row": [{"relation_id": "Gate", "uses": 2}]}
                for index, name in enumerate(NAMES)
            ],
            "preprocessed_columns": [
                {"id": "eq_in0_address" if index == 0 else f"fixed_{index}",
                 "commitment_index": index, "log_size": 4,
                 "rows": 16, "values_sha256": "5" * 64}
                for index in range(45)
            ],
        }
        self.key = {field: self.roster[field] for field in (
            "program_sha256", "canonical_ir_sha256", "air_bundle_sha256",
            "preprocessed_root", "circuit_hash")}
        self.key.update(schema=KEY_SCHEMA, gate_component_roster_sha256=digest(self.roster))
        self.report = {"gate_component_roster": copy.deepcopy(self.roster),
                       "gate_component_roster_sha256": digest(self.roster)}
        self.artifacts = {ARTIFACT: "digest"}
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))

    def check(self) -> None:
        validate(self.package, "gate", self.artifacts, self.key, self.report)

    def test_exact_roster_is_admitted(self) -> None:
        self.check()
        # JSON file formatting and key order do not alter the typed digest.
        (self.package / ARTIFACT).write_text(json.dumps(self.roster, sort_keys=True, indent=2))
        self.check()

    def test_missing_or_mutated_artifact_is_rejected(self) -> None:
        del self.artifacts[ARTIFACT]
        with self.assertRaises(ValueError):
            self.check()
        self.artifacts[ARTIFACT] = "digest"
        self.roster["preprocessed_columns"][0]["id"] = "other"
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))
        with self.assertRaises(ValueError):
            self.check()

    def test_coherent_digest_reseal_requires_native_source_check(self) -> None:
        self.roster["preprocessed_columns"][0]["values_sha256"] = "6" * 64
        self.key["gate_component_roster_sha256"] = digest(self.roster)
        self.report["gate_component_roster"] = copy.deepcopy(self.roster)
        self.report["gate_component_roster_sha256"] = digest(self.roster)
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))
        # Package consistency alone cannot authenticate an attacker-authored
        # package; the embedded native verifier reconstructs the roster.
        self.check()

    def test_bad_roster_order_or_digest_is_rejected(self) -> None:
        self.roster["components"][0]["proof_index"] = 1
        self.report["gate_component_roster"] = copy.deepcopy(self.roster)
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))
        with self.assertRaises(ValueError):
            self.check()
        self.roster["components"][0]["proof_index"] = 0
        self.report["gate_component_roster"] = copy.deepcopy(self.roster)
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))
        self.key["gate_component_roster_sha256"] = "f" * 64
        with self.assertRaises(ValueError):
            self.check()

    def test_old_key_cannot_carry_new_roster(self) -> None:
        self.key["schema"] = "s31-verification-key-v1"
        with self.assertRaises(ValueError):
            self.check()
        self.key.pop("gate_component_roster_sha256")
        self.report.clear()
        self.artifacts.clear()
        (self.package / ARTIFACT).unlink()
        self.check()


if __name__ == "__main__":
    unittest.main()
