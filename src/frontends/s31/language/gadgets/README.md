# Relation compiler gadgets

`integer_multiply.zig` implements fixed-width wrapping and complete
multiplication with byte-constrained schoolbook columns. Its local comments
spell out the integer bounds that make each M31 field equation sound. The
parent
[`relation_compiler.zig`](../relation_compiler.zig) connects the gadget to
normalized relation nodes and the circuit builder, including signed and
unsigned checked-overflow constraints.

`integer_bits.zig` decomposes byte or u16 limbs into proved Boolean wires,
computes AND/OR/XOR/NOT with arithmetic gates, and packs result bits back to
bounded limbs. The relation compiler caches a decomposition per wire and limb
width, so consecutive bitwise nodes reuse it. This path stays in the
arithmetic/Equation AIR components and does not activate the large generic
XOR lookup table.

The same bit cache serves static shifts and rotations. `shiftedBits` selects
proved bit wires or constant zero; the signed right shift selects the proved
high bit when the source index would exceed the width. For counts divisible
by the limb width, `intStaticShift` in the relation compiler avoids bit
decomposition and rewires already bounded `u16` limbs. The arithmetic right
shift derives its fill limb from the constrained sign bit. The source count
is normalized and carried in the relation's `index` field.
The cache also records the bit representation of the constant-zero limb and
of a sign-fill limb. A later unaligned shift or bitwise operation can reuse
those bits without guessing and checking them again.

`integer_division.zig` fuses quotient multiplication and remainder addition
in base-256 columns for `u8` through `u128`. It proves all high product
columns, fixes the terminal carry to zero, and proves `remainder<divisor`
with bounded limb borrows. `intDivRem` in the parent compiler handles signed
types by proving sign bits, conditionally negating the inputs into unsigned
magnitudes, then conditionally negating both results. The positive-quotient
sign check rejects `MIN / -1`. An explicit-witness gadget entry point tests
wrong quotient, oversized remainder, zero divisor, and truncated product
attempts independently of the witness generator.
