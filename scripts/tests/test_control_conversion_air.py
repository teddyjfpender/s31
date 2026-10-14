"""Focused mutation controls for the installed conversion AIR source guard."""

from __future__ import annotations

import unittest
from pathlib import Path

from scripts.s31_formal_lib.checks import FormalError
from scripts.s31_formal_lib.control_conversion_air import (
    BUNDLE, WITNESS, check, selected_program,
)

ROOT = Path(__file__).resolve().parents[2]
P = 2**31 - 1


class ConversionAirTests(unittest.TestCase):
    def test_installed_air_and_lookup_schedule(self) -> None:
        check(ROOT)

    def test_bytecode_mutation_rejected(self) -> None:
        data = bytearray((ROOT / BUNDLE).read_bytes())
        data[-16] ^= 1
        with self.assertRaises(FormalError):
            check(ROOT, bundle=bytes(data))

    def test_range_lookup_mutation_rejected(self) -> None:
        source = (ROOT / WITNESS).read_text().replace(
            "Lookup.use(.{ rc16, m(32767).sub(c[2]) })",
            "Lookup.use(.{ rc16, m(32768).sub(c[2]) })", 1)
        with self.assertRaisesRegex(FormalError, "lookup tuple schedule"):
            check(ROOT, witness=source)

    def test_zero_wraparound_fails_first_residual(self) -> None:
        low, high, input_value = 65535, 32767, 0
        self.assertEqual(low + 65536 * high, P)
        self.assertEqual((input_value - low - 65536 * high) % P, 0)
        for inverse_or_one in (0, 1, 2, P - 1):
            self.assertEqual(((input_value * inverse_or_one - 1) * low) % P,
                             P - low)

    def test_selected_evaluator_is_present(self) -> None:
        self.assertGreater(len(selected_program((ROOT / BUNDLE).read_bytes())), 2000)


if __name__ == "__main__":
    unittest.main()
