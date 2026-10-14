"""Hostile controls against a captured native control-gadget Gate topology."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.control_air_correspondence import check_control_air  # noqa: E402

FIXTURE = Path(__file__).parent / "fixtures" / "control_air"
TOPOLOGY = json.loads((FIXTURE / "gate-topology.json").read_text())


class ControlAirCorrespondenceTests(unittest.TestCase):
    def test_native_capture_and_sealed_roster(self) -> None:
        receipt = check_control_air(FIXTURE, TOPOLOGY)
        self.assertEqual(receipt["checked_arithmetic_rows"], 14)
        self.assertEqual(receipt["checked_public_binding_gate_rows"], 15)
        self.assertEqual(receipt["checked_conversion_rows"], 5)
        self.assertEqual(receipt["public_output_pin_addresses"], [4, 5, 6, 7])
        self.assertEqual(receipt["active_inverse_lanes"], 4)
        self.assertEqual(receipt["control_nodes"], ["z", "picked", "result"])

    def test_changed_fixed_column_is_rejected_before_graph_check(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(item for item in changed["columns"]
             if item["id"] == "qm31_ops_mul_flag")["values"][-8] ^= 1
        with self.assertRaisesRegex(ValueError, "fixed column"):
            check_control_air(FIXTURE, changed)

    def test_zero_test_anchor_removal_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["add"] = [gate for gate in changed["add"]
                          if not (gate["in0"] == gate["out"] and gate["in1"] == 22)]
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "zero-test gadget"):
                check_control_air(FIXTURE, changed)

    def test_select_output_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["add"] if gate["out"] == 27)["in1"] = 25
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "wrong unique add producer"):
                check_control_air(FIXTURE, changed)

    def test_inverse_mask_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["sub"] if gate["in0"] == 30)["in1"] = 1
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "expected one uniquely owned sub"):
                check_control_air(FIXTURE, changed)

    def test_public_input_loses_base_field_owner(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["pointwise_mul"] = [gate for gate in changed["pointwise_mul"]
                                    if gate["out"] != 11]
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "wrong unique pointwise_mul producer"):
                check_control_air(FIXTURE, changed)

    def test_source_and_fixed_root_identity_are_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["program_sha256"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "not bound to the sealed source"):
            check_control_air(FIXTURE, changed)
        changed = copy.deepcopy(TOPOLOGY)
        changed["preprocessed_root"] = "0" * 64
        with self.assertRaisesRegex(ValueError, "not bound to the sealed source"):
            check_control_air(FIXTURE, changed)

    def test_output_lane_extraction_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["pointwise_mul"]
             if gate["out"] == 40)["in1"] = 1
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "uniquely owned pointwise_mul"):
                check_control_air(FIXTURE, changed)

    def test_public_conversion_input_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["m31_to_u32"][3]["input"] = 38
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "wrong unique conversion"):
                check_control_air(FIXTURE, changed)

    def test_duplicate_conversion_output_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["m31_to_u32"][4]["out"] = changed["m31_to_u32"][3]["out"]
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "duplicate addresses"):
                check_control_air(FIXTURE, changed)

    def test_inverse_basis_restore_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["mul"] if gate["out"] == 42)["in1"] = 37
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "uniquely owned mul"):
                check_control_air(FIXTURE, changed)

    def test_public_pin_producer_rewire_is_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["add"] if gate["out"] == 6)["in0"] = 39
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "wrong unique add producer"):
                check_control_air(FIXTURE, changed)

    def test_public_output_order_and_padding_are_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        changed["output"][2], changed["output"][3] = changed["output"][3], changed["output"][2]
        with self.assertRaisesRegex(ValueError, "public output ABI"):
            check_control_air(FIXTURE, changed)
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["add"] if gate["out"] == 9)["in1"] = 1
        with patch("package.control_air_correspondence._check_columns"):
            with self.assertRaisesRegex(ValueError, "wrong unique add producer"):
                check_control_air(FIXTURE, changed)


if __name__ == "__main__":
    unittest.main()
