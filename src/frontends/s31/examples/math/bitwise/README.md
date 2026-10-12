# Fixed-width bitwise programs

Run either checked-in `.s31` source with its `.valid.json` assignment. The
syntax uses the nominal integer type to fix the number of bits; the verifier
key commits to that type and to the operation.

[`u8_xor.s31`](u8_xor.s31) computes `170 XOR 204 = 102`. Both private inputs
have one byte-sized limb in the assignment. The source lowers to two
`int_view` nodes and one `int_bit_xor` node. The circuit proves that the
input limbs equal their Boolean bit decompositions, computes each XOR bit as
`a + b - 2*a*b`, and packs the output bits. The
[worked chapter](../../../docs/fixed-width-integers.md#bitwise-operations-by-hand)
lists every bit and constraint.

[`u32_mix.s31`](u32_mix.s31) reads its two private inputs in both AND and XOR.
It then combines the results with NOT and OR. For the checked-in assignment,
the output is `0xFDFBF9F7`, represented as little-endian `u16` limbs
`[63991, 65019]`. The compiler reuses each already constrained input bit in
both branches, and reuses packed result bits in the later operations.

[`i128_xor.s31`](i128_xor.s31) proves an eight-limb signed XOR whose inputs
and result cross the sign bit. It checks the highest supported scalar width
and verifies that signedness changes interpretation rather than Boolean bit
equations.

The [native acceptance gate](../../../tests/acceptance/math/bitwise.py) pins
the normalized circuit hash and AIR geometry for all three examples, checks the
independent oracle, proves each valid assignment, checks the native verifier,
rejects a changed public statement, and rejects a false output during native
witness construction. The [Lean model](../../../../../../formal/s31/S31/Gadgets/IntegerBits.lean)
proves the width-generic pointwise Boolean rules. It does not prove that the
production Zig circuit implements that model; the executable gates check
that boundary separately.
