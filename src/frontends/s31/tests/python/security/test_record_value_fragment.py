"""Source-derived record value semantics, private wires and result aliases."""

from __future__ import annotations

import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(S31 / "python"))

from package.record_value_fragment import (  # noqa: E402
    InvalidRecordValueFragment, P, evaluate_record_source_assignment,
)

SOURCE = b"""struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
"""


def encoded(value: object) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


class RecordValueFragmentTests(unittest.TestCase):
    def assignment(self, left: int = 2, right: int = 3,
                   secret: int = 7) -> dict:
        result = (left * secret + right) % P
        return {"public_inputs": {"_s31_abi_input_0": [left],
                                  "_s31_abi_input_1": [right]},
                "private_inputs": {"_s31_abi_input_2": [5],
                                   "_s31_abi_input_3": [secret]},
                "public_outputs": {"q": [result],
                                   "_s31_abi_input_1": [right]}}

    def test_hand_value_and_field_order(self) -> None:
        result = evaluate_record_source_assignment(SOURCE, encoded(self.assignment()))
        self.assertEqual(result["proof_words"], [2, 3, 17, 3, 0, 0, 0, 0])
        self.assertEqual([leaf["words"] for leaf in result["leaves"]],
                         [[2], [3], [17], [3]])
        wrapped = evaluate_record_source_assignment(
            SOURCE, encoded(self.assignment(P - 1, P - 1, P - 1)))
        self.assertEqual(wrapped["proof_words"][:4], [P - 1, P - 1, 0, P - 1])

    def test_result_and_private_input_changes(self) -> None:
        honest = self.assignment()
        changed = self.assignment(secret=8)
        self.assertEqual(evaluate_record_source_assignment(
            SOURCE, encoded(changed))["proof_words"][2], 19)
        honest["public_outputs"]["q"] = [18]
        with self.assertRaisesRegex(InvalidRecordValueFragment, "claimed public"):
            evaluate_record_source_assignment(SOURCE, encoded(honest))

    def test_malformed_assignment_fails_closed(self) -> None:
        for label, change in (
            ("modulus", lambda obj: obj["public_inputs"].update(_s31_abi_input_0=[P])),
            ("bool", lambda obj: obj["public_inputs"].update(_s31_abi_input_0=[True])),
            ("extra", lambda obj: obj["private_inputs"].update(extra=[0])),
            ("missing", lambda obj: obj["private_inputs"].pop("_s31_abi_input_3")),
        ):
            with self.subTest(label=label):
                assignment = self.assignment()
                change(assignment)
                with self.assertRaises(InvalidRecordValueFragment):
                    evaluate_record_source_assignment(SOURCE, encoded(assignment))
        duplicated = encoded(self.assignment()).replace(
            b'"public_inputs":{', b'"public_inputs":{},"public_inputs":{', 1)
        with self.assertRaisesRegex(InvalidRecordValueFragment, "duplicate"):
            evaluate_record_source_assignment(SOURCE, duplicated)


if __name__ == "__main__":
    unittest.main()
