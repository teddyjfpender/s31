"""Fixed Gate producer roster controls for public addresses 3 through 10."""

from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from scripts.compiler.control_gate_pin_roster_audit import check_pin_roster

FIXTURE = (Path(__file__).resolve().parents[2] /
           "src/frontends/s31/tests/python/security/fixtures/control_air/gate-topology.json")
TOPOLOGY = json.loads(FIXTURE.read_text())


def column(topology: dict, name: str) -> list[int]:
    return next(c["values"] for c in topology["columns"] if c["id"] == name)


class ControlGatePinRosterTests(unittest.TestCase):
    def test_sealed_fixture_has_eight_positive_ordered_pins(self) -> None:
        receipt = check_pin_roster(TOPOLOGY)
        self.assertEqual(receipt["public_pin_physical_rows"], list(range(4, 12)))
        self.assertEqual(receipt["public_pin_addresses"], list(range(3, 11)))
        self.assertEqual(receipt["positive_conversion_producers"], 5)
        self.assertFalse(receipt["global_lookup_claim_authenticated"])

    def test_zero_or_duplicate_pin_producer_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        column(changed, "qm31_ops_mults")[6] = 0
        with self.assertRaisesRegex(ValueError, "ordered public pins"):
            check_pin_roster(changed)
        changed = copy.deepcopy(TOPOLOGY)
        column(changed, "qm31_ops_out_address")[12] = 5
        next(gate for gate in changed["add"] if gate ==
             {"in0": 0, "in1": 0, "out": 0})["out"] = 5
        with self.assertRaisesRegex(ValueError, "two positive QM31 rows"):
            check_pin_roster(changed)

    def test_conversion_collision_and_pin_order_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        column(changed, "m31_to_u32_output_addr")[0] = 3
        with self.assertRaisesRegex(ValueError, "conversion output collides"):
            check_pin_roster(changed)
        changed = copy.deepcopy(TOPOLOGY)
        changed["output"][2], changed["output"][3] = (
            changed["output"][3], changed["output"][2])
        with self.assertRaisesRegex(ValueError, "public output ABI"):
            check_pin_roster(changed)

    def test_noncanonical_fixed_multiplicity_rejected(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        column(changed, "qm31_ops_mults")[4] = 2**31 - 1
        with self.assertRaisesRegex(ValueError, "noncanonical fixed"):
            check_pin_roster(changed)

    def test_physical_flags_and_graph_must_agree(self) -> None:
        changed = copy.deepcopy(TOPOLOGY)
        column(changed, "qm31_ops_sub_flag")[4] = 1
        with self.assertRaisesRegex(ValueError, "not one-hot"):
            check_pin_roster(changed)
        changed = copy.deepcopy(TOPOLOGY)
        next(gate for gate in changed["add"] if gate["out"] == 3)["in0"] = 1
        with self.assertRaisesRegex(ValueError, "graph rows differ"):
            check_pin_roster(changed)


if __name__ == "__main__":
    unittest.main()
