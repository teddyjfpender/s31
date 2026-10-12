"""Positive and negative controls for the square4 base-trace diagnostic scope."""

from __future__ import annotations

import copy
import json
import sys
import unittest
from pathlib import Path


FORMAL = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FORMAL / "scripts"))
import check_square4_native_witness as witness  # noqa: E402

REPORT = FORMAL / "fixtures/square4-native-physical.json"


class Square4NativeWitnessScopeTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.report = json.loads(REPORT.read_bytes())

    def test_pinned_report_and_five_invalid_mutations(self) -> None:
        summary = witness.check_report(self.report)
        self.assertEqual(summary["arithmetic_roots"], 4608)
        self.assertEqual(summary["ideal_gate_uses"], 1033)
        self.assertEqual(summary["ideal_gate_yields"], 1033)
        witness.mutation_controls(self.report)

    def test_locally_valid_padding_row_fails_ideal_gate_balance(self) -> None:
        # Row 11 is arithmetic padding, but its Gate output has multiplicity
        # eleven. Its local roots still vanish; the new Gate check rejects it.
        self.assertEqual([col[11] for col in self.report["fixed_columns"]],
                         [1, 0, 0, 0, 0, 0, 0, 11])
        self.assertEqual([col[11] for col in self.report["main_columns"]], [0] * 12)
        alternative = copy.deepcopy(self.report)
        alternative["main_columns"][0][11] = 1
        alternative["main_columns"][4][11] = 2
        alternative["main_columns"][8][11] = 3
        with self.assertRaisesRegex(ValueError, "ideal Gate balance differs"):
            witness.check_report(alternative)
        self.assertEqual([col[11] for col in alternative["main_columns"]][::4],
                         [1, 2, 3])


if __name__ == "__main__":
    unittest.main()
