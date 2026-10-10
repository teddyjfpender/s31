# Fixed-width multiplication

These programs use the same `std::int::mul_wrapping` call on three widths:

- [`u8_wrapping.s31`](u8_wrapping.s31): one byte with a discarded carry.
- [`u32_wrapping.s31`](u32_wrapping.s31): carry propagation across two u16 limbs.
- [`i128_wrapping.s31`](i128_wrapping.s31): signed two's-complement bit-pattern multiplication.

Each `.valid.json` file supplies an independently calculated private input
and public result. The [fixed-width walkthrough](../../../docs/fixed-width-integers.md)
explains the byte constraints and multiplication AIR by hand. The
[native acceptance gate](../../../tests/acceptance/math/README.md) verifies
all three proofs and rejects a changed public result for each.
