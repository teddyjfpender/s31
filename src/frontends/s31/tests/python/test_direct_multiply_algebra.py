"""Independent integer checks for the direct multiplier's overflow identities.

These tests model the equations over integers. They do not execute the Zig
gadget or establish that the native AIR enforces those equations.
"""

from __future__ import annotations

import random
import unittest


PRIME = (1 << 31) - 1
WIDTHS = (8, 16, 32, 64, 128)


def signed_value(pattern: int, width: int) -> int:
    return pattern - (1 << width) if pattern >> (width - 1) else pattern


def signed_high_equations(a: int, b: int, width: int) -> bool:
    """Solve the checked-sign high-limb equations with the exact product."""
    word = 1 << width
    unsigned_product = a * b
    low = unsigned_product % word
    high = unsigned_product // word
    sa, sb, sr = a >> (width - 1), b >> (width - 1), low >> (width - 1)
    limb_bits = 8 if width == 8 else 16
    limb_base = 1 << limb_bits
    carry = 0
    for shift in range(0, width, limb_bits):
        limb_a = (a >> shift) % limb_base
        limb_b = (b >> shift) % limb_base
        limb_h = (high >> shift) % limb_base
        left = carry + sa * limb_b + sb * limb_a + sr * (limb_base - 1)
        assert left < PRIME
        next_carry, expected_h = divmod(left, limb_base)
        assert next_carry in range(4)
        assert limb_h + next_carry * limb_base < PRIME
        if limb_h != expected_h:
            return False
        carry = next_carry
    return carry == sa * sb + sr


def unsigned_shortcut_equations(a: int, b: int, width: int) -> bool:
    """Solve the low-column and omitted-high-coefficient conditions."""
    digit_bits = 8 if width <= 32 else 13
    radix = 1 << digit_bits
    count = (width + digit_bits - 1) // digit_bits
    digits_a = [(a >> (i * digit_bits)) % radix for i in range(count)]
    digits_b = [(b >> (i * digit_bits)) % radix for i in range(count)]
    carry = 0
    low_digits = []
    for column in range(count):
        total = carry + sum(digits_a[i] * digits_b[column - i]
                            for i in range(count) if 0 <= column - i < count)
        assert total < PRIME
        carry, digit = divmod(total, radix)
        low_digits.append(digit)
    high_coefficients = [sum(digits_a[i] * digits_b[column - i]
                             for i in range(count) if 0 <= column - i < count)
                         for column in range(count, 2 * count - 1)]
    assert all(coefficient < PRIME for coefficient in high_coefficients)
    spill = sum(digit << (i * digit_bits) for i, digit in enumerate(low_digits)) >> width
    return carry == 0 and spill == 0 and all(c == 0 for c in high_coefficients)


class DirectMultiplyAlgebraTest(unittest.TestCase):
    def test_exhaustive_i8_signed_high_identity_matches_range(self) -> None:
        for a in range(256):
            for b in range(256):
                product = signed_value(a, 8) * signed_value(b, 8)
                fits = -128 <= product <= 127
                self.assertEqual(fits, signed_high_equations(a, b, 8),
                                 (a, b, product))

    def test_signed_high_identity_at_wide_boundaries(self) -> None:
        for width in WIDTHS[1:]:
            top = 1 << (width - 1)
            mask = (1 << width) - 1
            patterns = (0, 1, 2, 3, 7, top - 1, top, top + 1,
                        mask - 7, mask - 2, mask - 1, mask)
            for a in patterns:
                for b in patterns:
                    product = signed_value(a, width) * signed_value(b, width)
                    fits = -top <= product < top
                    self.assertEqual(fits, signed_high_equations(a, b, width),
                                     (width, a, b, product))

    def test_unsigned_shortcut_at_edges_and_deterministic_samples(self) -> None:
        rng = random.Random(0x53131)
        for width in WIDTHS:
            top = 1 << width
            edges = tuple(value for value in
                          (0, 1, 2, 3, 255, 256, top // 2 - 1,
                           top // 2, top - 2, top - 1) if value < top)
            samples = [(a, b) for a in edges for b in edges]
            samples.extend((rng.randrange(top), rng.randrange(top))
                           for _ in range(100))
            if width >= 64:
                # The d13 source digit is partial: 12 bits for u64, 11 for u128.
                samples.extend(((1 << (width - 12), 1 << 13),
                                (1 << (width - 1), 2),
                                (top - 1, 1)))
            for a, b in samples:
                self.assertEqual(a * b < top,
                                 unsigned_shortcut_equations(a, b, width),
                                 (width, a, b))


if __name__ == "__main__":
    unittest.main()
