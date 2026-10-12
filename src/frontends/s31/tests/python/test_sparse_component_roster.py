"""Fail-closed package validation for sparse AIR roster metadata."""

from __future__ import annotations

import copy
import json
import sys
import tempfile
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from package.sparse_component_roster import ARTIFACT, COMPONENTS, KEY_SCHEMA, digest, validate


class SparseComponentRosterTests(unittest.TestCase):
    def setUp(self) -> None:
        temporary = tempfile.TemporaryDirectory()
        self.addCleanup(temporary.cleanup)
        self.package = Path(temporary.name)
        self.roster = {
            "schema": "s31-component-roster-sparse-gate-v1", "profile": "sparse-v3",
            "program_sha256": "0" * 64, "canonical_ir_sha256": "1" * 64,
            "air_bundle_sha256": "2" * 64, "preprocessed_root": "3" * 64,
            "circuit_hash": "4" * 64, "claimed_sums": 3,
            "components": [
                {"name": name, "source_index": source_index,
                 "proof_index": proof_index, "claimed_sum_index": proof_index,
                 "trace_log_size": 16 if source == "fixed" else 4,
                 "base_trace_columns": base, "interaction_trace_columns": interaction,
                 "log_size_source": source,
                 "lookup_uses_per_row": [
                     {"relation_id": relation, "uses": count} for relation, count in uses]}
                for proof_index, (name, source_index, base, interaction, source, uses)
                in enumerate(COMPONENTS)
            ],
            "preprocessed_columns": [
                {"id": ("qm31_ops_in0_address" if index == 0 else
                        "m31_to_u32_input_addr" if index == 1 else
                        "seq_16" if index == 11 else f"column_{index}"),
                 "commitment_index": index, "log_size": 16 if index == 11 else 4,
                 "rows": 65536 if index == 11 else 16, "values_sha256": "5" * 64}
                for index in range(12)
            ],
        }
        self.key = {field: self.roster[field] for field in (
            "program_sha256", "canonical_ir_sha256", "air_bundle_sha256",
            "preprocessed_root", "circuit_hash")}
        self.key.update(schema=KEY_SCHEMA, sparse_component_roster_sha256=digest(self.roster))
        self.report = {"sparse_component_roster": copy.deepcopy(self.roster),
                       "sparse_component_roster_sha256": digest(self.roster)}
        self.artifacts = {ARTIFACT: "hash"}
        self.write()

    def write(self) -> None:
        (self.package / ARTIFACT).write_text(json.dumps(self.roster))

    def check(self) -> None:
        validate(self.package, "sparse-gate", self.artifacts, self.key, self.report)

    def test_valid_and_reordered_json(self) -> None:
        self.check()
        (self.package / ARTIFACT).write_text(json.dumps(self.roster, sort_keys=True))
        self.check()

    def test_component_order_and_geometry(self) -> None:
        self.roster["components"][0]["source_index"] = 3
        self.report["sparse_component_roster"] = copy.deepcopy(self.roster)
        self.write()
        with self.assertRaises(ValueError):
            self.check()

    def test_missing_sidecar_and_digest(self) -> None:
        self.artifacts.clear()
        with self.assertRaises(ValueError):
            self.check()
        self.artifacts[ARTIFACT] = "hash"
        self.key["sparse_component_roster_sha256"] = "f" * 64
        with self.assertRaises(ValueError):
            self.check()

    def test_downgraded_key_is_rejected(self) -> None:
        self.key["schema"] = "s31-verification-key-v3"
        with self.assertRaises(ValueError):
            self.check()
        self.artifacts.clear()
        self.report.clear()
        self.key.pop("sparse_component_roster_sha256")
        (self.package / ARTIFACT).unlink()
        with self.assertRaises(ValueError):
            self.check()

    def test_coherent_reseal_needs_embedded_native_check(self) -> None:
        self.roster["preprocessed_columns"][0]["values_sha256"] = "6" * 64
        self.report["sparse_component_roster"] = copy.deepcopy(self.roster)
        self.report["sparse_component_roster_sha256"] = digest(self.roster)
        self.key["sparse_component_roster_sha256"] = digest(self.roster)
        self.write()
        self.check()


if __name__ == "__main__":
    unittest.main()
