"""Mutation controls for the bounded source-to-generic-Gate admission."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.effects_gate_ownership import admitted_ssa, check_gate_ownership  # noqa: E402

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
