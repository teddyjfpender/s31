"""Mutation controls for the bounded source-to-generic-Gate admission."""

from __future__ import annotations

import copy
import hashlib
import json
import shutil
import struct
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.effects_gate_ownership import admitted_ssa, check_gate_ownership  # noqa: E402
from package.gate_component_roster import digest as roster_digest  # noqa: E402

FIXTURE = Path(__file__).parent / "fixtures" / "effects_gate_ownership"
MANIFEST = {"lowering": "gate", "name": "affine_guard", "source_text_sha256": "fixture"}


class EffectsGateOwnershipTests(unittest.TestCase):
    def setUp(self) -> None:
        self.topology = json.loads((FIXTURE / "gate-topology.json").read_text())

    def check(self, topology: dict) -> dict:
        with patch("package.effects_gate_ownership._load_topology", return_value=topology):
            return check_gate_ownership(FIXTURE, MANIFEST)

    def test_actual_emitted_fixture(self) -> None:
        receipt = self.check(self.topology)
        self.assertEqual(receipt["node_count"], 3)
        self.assertEqual(receipt["assertion_count"], 1)
        self.assertEqual(receipt["public_words"], 8)

    def test_wrong_arithmetic_row_rejected(self) -> None:
        altered = copy.deepcopy(self.topology)
        altered["sub"][0]["in1"] = altered["node_wires"][1]["wires"][0]
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_resealed_wrong_row_still_rejected_by_source_graph(self) -> None:
        # Keep dynamic column SHA and roster digest internally consistent so
        # the source graph check, not the earlier hash check, is exercised.
        altered = copy.deepcopy(self.topology)
        wrong = altered["node_wires"][1]["wires"][0]
        altered["sub"][0]["in1"] = wrong
        column = next(item for item in altered["columns"]
                      if item["id"] == "qm31_ops_in1_address")
        column["values"][len(altered["add"])] = wrong
        column_hash = hashlib.sha256(struct.pack(
            f"<{len(column['values'])}I", *column["values"])).hexdigest()
        with tempfile.TemporaryDirectory() as temp:
            package = Path(temp) / "package"
            shutil.copytree(FIXTURE, package)

            def rewrite(name: str, value: dict) -> None:
                (package / name).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

            roster = json.loads((package / "gate-component-roster.json").read_text())
            next(item for item in roster["preprocessed_columns"]
                 if item["id"] == column["id"])["values_sha256"] = column_hash
            rewrite("gate-component-roster.json", roster)
            report = json.loads((package / "cost-report.json").read_text())
            report["gate_component_roster"] = roster
            report["gate_component_roster_sha256"] = roster_digest(roster)
            rewrite("cost-report.json", report)
            key = json.loads((package / "verification-key.json").read_text())
            key["gate_component_roster_sha256"] = roster_digest(roster)
            rewrite("verification-key.json", key)
            with patch("package.effects_gate_ownership._load_topology", return_value=altered):
                with self.assertRaisesRegex(ValueError, "source node 4 differs"):
                    check_gate_ownership(package, MANIFEST)

    def test_wrong_assertion_pair_rejected(self) -> None:
        altered = copy.deepcopy(self.topology)
        altered["eq"][0]["in1"] = altered["node_wires"][4]["wires"][0]
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_wrong_numeric_constant_rejected(self) -> None:
        altered = copy.deepcopy(self.topology)
        next(item for item in altered["constants"] if item["limbs"] == [7] * 4)["limbs"] = [8] * 4
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_wrong_public_pin_rejected(self) -> None:
        altered = copy.deepcopy(self.topology)
        altered["output"][5] = altered["output"][4]
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_wrong_fixed_column_or_root_rejected(self) -> None:
        altered = copy.deepcopy(self.topology)
        next(item for item in altered["columns"] if item["id"] == "qm31_ops_sub_flag")["values"][0] ^= 1
        with self.assertRaises(ValueError):
            self.check(altered)
        altered = copy.deepcopy(self.topology)
        altered["preprocessed_root"] = "0" * 64
        with self.assertRaises(ValueError):
            self.check(altered)

    def test_unsupported_lane_and_peephole_shapes_rejected(self) -> None:
        cert = json.loads((FIXTURE / "source-relation-certificate.json").read_text())
        cert["ssa"]["lane_count"] = 3
        self.assertFalse(admitted_ssa(cert))
        cert["ssa"]["lane_count"] = 4
        cert["ssa"]["nodes"][0]["constant"] = 0
        self.assertFalse(admitted_ssa(cert))
        with self.assertRaises(ValueError):
            check_gate_ownership(FIXTURE, {**MANIFEST, "lowering": "direct-gate"})


if __name__ == "__main__":
    unittest.main()
