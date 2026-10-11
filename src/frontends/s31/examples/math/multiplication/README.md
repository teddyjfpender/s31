# Fixed-width multiplication

The wrapping programs return the low fixed-width product bits:

- [`u8_wrapping.s31`](u8_wrapping.s31): one byte with a discarded carry.
- [`u32_wrapping.s31`](u32_wrapping.s31): carry propagation across two u16 limbs.
- [`i128_wrapping.s31`](i128_wrapping.s31): signed two's-complement bit-pattern multiplication.

The checked programs reject arithmetic overflow:

- [`u8_checked.s31`](u8_checked.s31): $25\cdot10=250$ fits one byte.
- [`i8_checked.s31`](i8_checked.s31): $(-1)\cdot2=-2$ fits signed one-byte range.
- [`u32_checked.s31`](u32_checked.s31): $65535^2$ fits four bytes.
- [`i128_checked.s31`](i128_checked.s31): $(-2)\cdot3=-6$ retains its sign across eight limbs.

Each `.valid.json` file supplies an independently calculated private input
and public result. The [fixed-width walkthrough](../../../docs/fixed-width-integers.md)
explains the byte constraints and multiplication AIR by hand. The
[native acceptance gate](../../../tests/acceptance/math/README.md) verifies
representative proofs and rejects a changed public result for each.
