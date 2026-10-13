"""Invoice fixture, source parity, and independent arithmetic boundaries."""

import copy
import json
import sys
import unittest
from pathlib import Path

S31 = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(S31 / "python"))

from oracle import OracleError, evaluate_relation
from text_frontend import compile_text

EXAMPLE = S31 / "examples/invoice"


def limbs(value):
    return [(value >> (16 * index)) & 65535 for index in range(4)]


class InvoiceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.relation, _ = compile_text((EXAMPLE / "invoice.s31").read_text())
        cls.fixture = json.loads((EXAMPLE / "invoice.valid.json").read_text())

    def assignment(self, inputs=None, total=1300):
        assignment = copy.deepcopy(self.fixture)
        for name, value in (inputs or {}).items():
            assignment["private_inputs"][name] = limbs(value)
        assignment["public_outputs"]["total"] = limbs(total)
        return assignment

    def test_checked_in_relation_matches_text(self):
        self.assertEqual(self.relation, json.loads((EXAMPLE / "invoice.s31.json").read_text()))

    def test_fixture_total(self):
        expected = 3 * 125 + 2 * 450 + 25
        self.assertEqual(evaluate_relation(self.relation, self.fixture), {"total": limbs(expected)})

    def test_zero_quantities_leave_only_delivery(self):
        assignment = self.assignment({"quantity_a": 0, "quantity_b": 0}, total=25)
        self.assertEqual(evaluate_relation(self.relation, assignment), {"total": limbs(25)})

    def test_false_total_is_rejected(self):
        with self.assertRaisesRegex(OracleError, "does not match"):
            evaluate_relation(self.relation, self.assignment(total=1301))

    def test_zero_prices_and_full_width_totals(self):
        cases = (
            ({"price_a": 0, "price_b": 0}, 25),
            ({"quantity_a": 2**32 + 1, "price_a": 65536 + 3},
             (2**32 + 1) * (65536 + 3) + 2 * 450 + 25),
            ({"quantity_a": 1, "price_a": 2**64 - 1,
              "quantity_b": 0, "delivery_fee": 0}, 2**64 - 1),
        )
        for inputs, expected in cases:
            with self.subTest(inputs=inputs):
                self.assertEqual(evaluate_relation(self.relation, self.assignment(inputs, expected)),
                                 {"total": limbs(expected)})

    def test_checked_overflows_are_rejected(self):
        maximum = 2**64 - 1
        cases = {
            "product": {"quantity_a": maximum, "price_a": 2},
            "subtotal": {"quantity_a": maximum, "price_a": 1,
                         "quantity_b": 1, "price_b": 1},
            "fee": {"quantity_a": maximum, "price_a": 1,
                    "quantity_b": 0, "delivery_fee": 1},
        }
        for stage, inputs in cases.items():
            with self.subTest(stage=stage), self.assertRaisesRegex(OracleError, "overflow"):
                evaluate_relation(self.relation, self.assignment(inputs, total=0))


if __name__ == "__main__":
    unittest.main()
