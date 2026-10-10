"""Pinned Gate bytecode scalar replay and changed-cell controls."""

from __future__ import annotations

import hashlib
import struct
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[5]
sys.path.insert(0, str(ROOT / "scripts"))

from export_s31_direct_gate_bytecode_arithmetic import (  # noqa: E402
    BUNDLE, decoded_program, evaluate_row, gate_program,
)
from export_s31_direct_gate_evaluator_fixture import (  # noqa: E402
    add, arithmetic, base, denominator, interaction_residuals, mul, scale, sub,
)


def first_row() -> tuple[tuple[int, ...], ...]:
    return ((0, 0, 1, 0, 22, 22, 23, 2),
            (0, 1, 2, 7, 0, 1, 2, 7, 0, 1, 4, 49),
            (1, 2, 3, 4, 5, 6, 7, 8),
            (9, 10, 11, 12, 13, 14, 15, 16))


def second_row() -> tuple[tuple[int, ...], ...]:
    return ((0, 0, 1, 0, 23, 23, 24, 4),
            (0, 1, 4, 49, 0, 1, 4, 49, 0, 1, 16, 2401),
            (17, 18, 19, 20, 21, 22, 23, 24),
            (25, 26, 27, 28, 29, 30, 31, 32))


class GateBytecodeArithmeticTest(unittest.TestCase):
    def setUp(self) -> None:
        self.bundle = BUNDLE.read_bytes()
        self.program = decoded_program(gate_program(self.bundle))

    def check_row(self, row: tuple[tuple[int, ...], ...]) -> tuple[tuple[int, ...], ...]:
        fixed, main, current, previous = row
        actual = evaluate_row(self.program, fixed, main, current, previous,
                              base(2), base(7), base(11), 512)
        pair, last = interaction_residuals(fixed, main, current, previous)
        self.assertEqual(tuple(base(value) for value in arithmetic(fixed, main)),
                         actual[:9])
        self.assertEqual((pair, last), actual[9:])
        return actual

    def test_all_eleven_roots_on_two_source_rows(self) -> None:
        for row in (first_row(), second_row()):
            with self.subTest(row=row[0][4]):
                actual = self.check_row(row)
                self.assertEqual(actual[:9], (base(0),) * 9)

    def test_changed_cells_reach_expected_root_families(self) -> None:
        original = self.check_row(first_row())
        fixed, main, current, previous = first_row()
        changed_fixed = list(fixed)
        changed_fixed[1], changed_fixed[2] = changed_fixed[2], changed_fixed[1]
        changed_main = list(main)
        changed_main[8], changed_main[11] = changed_main[11], changed_main[8]
        changed_current = list(current)
        changed_current[0], changed_current[4] = changed_current[4], changed_current[0]
        changed_previous = list(previous)
        changed_previous[4] += 1
        self.assertNotEqual(self.check_row((tuple(changed_fixed), main, current, previous))[:9],
                            original[:9])
        self.assertNotEqual(self.check_row((fixed, tuple(changed_main), current, previous))[:9],
                            original[:9])
        self.assertNotEqual(self.check_row((fixed, main, tuple(changed_current), previous))[9],
                            original[9])
        self.assertNotEqual(self.check_row((fixed, main, current, tuple(changed_previous)))[10],
                            original[10])

    def test_extension_roots_with_nonbase_challenges(self) -> None:
        alpha, z, claimed = (2, 3, 5, 7), (11, 13, 17, 19), (23, 29, 31, 37)
        for fixed, main, current, previous in (first_row(), second_row()):
            actual = evaluate_row(self.program, fixed, main, current, previous,
                                  alpha, z, claimed, 512)
            semantic = (fixed[0], fixed[3], fixed[1], fixed[2], *fixed[4:])
            left = denominator(semantic[4], main[:4], alpha, z)
            right = denominator(semantic[5], main[4:8], alpha, z)
            output = denominator(semantic[6], main[8:12], alpha, z)
            first = current[:4]
            last = current[4:]
            previous_last = previous[4:]
            pair = sub(mul(first, mul(left, right)), add(left, right))
            difference = add(sub(sub(last, previous_last), first),
                             scale(claimed, pow(512, -1, (1 << 31) - 1)))
            singleton = add(mul(difference, output), base(semantic[7]))
            self.assertEqual(actual[9:], (pair, singleton))

    def test_changed_installed_bundle_is_rejected(self) -> None:
        mutation = bytearray(self.bundle)
        mutation[-32] ^= 1
        self.assertNotEqual(hashlib.sha256(mutation).hexdigest(),
                            hashlib.sha256(self.bundle).hexdigest())
        with self.assertRaisesRegex(ValueError, "installed AIR bundle digest changed"):
            gate_program(bytes(mutation))

    def test_rehashed_root_order_is_rejected(self) -> None:
        mutation = bytearray(gate_program(self.bundle))
        # Root section is the last 44 bytes of the fixed selected program.
        mutation[-44], mutation[-40] = mutation[-40], mutation[-44]
        semantic = 0xCBF29CE484222325
        for byte in mutation[216:]:
            semantic ^= byte
            semantic = (semantic * 0x100000001B3) & ((1 << 64) - 1)
        struct.pack_into("<Q", mutation, 16, semantic)
        with self.assertRaisesRegex(ValueError, "selected Gate semantic identity changed"):
            decoded_program(bytes(mutation))


if __name__ == "__main__":
    unittest.main()
