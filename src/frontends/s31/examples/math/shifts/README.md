# Static fixed-width shifts and rotations

Each checked-in program uses one of the five `std::int` operations and has a
matching valid assignment. The angle-bracket count is known when the text is
compiled. It is normalized into the relation's `index` field: shifts cap
counts at the type width and rotations reduce counts modulo that width.
The type tag, operation, and canonical count are committed in the circuit
and verifier key.

The `u32` programs all start with `0x12345678`, stored as little-endian
`u16` limbs `[22136, 4660]`:

| Program | Public result | Output limbs | Circuit method |
| --- | --- | --- | --- |
| [`u32_shl16.s31`](u32_shl16.s31) | `0x56780000` | `[0, 22136]` | Move one constrained limb and insert zero. |
| [`u32_shr_logical4.s31`](u32_shr_logical4.s31) | `0x01234567` | `[17767, 291]` | Decompose two limbs into bits, select, and pack. |
| [`u32_rotl16.s31`](u32_rotl16.s31) | `0x56781234` | `[4660, 22136]` | Swap two constrained limb wires. |
| [`u32_rotr4.s31`](u32_rotr4.s31) | `0x81234567` | `[17767, 33059]` | Decompose two limbs into bits, select, and pack. |

[`i8_sar8.s31`](i8_sar8.s31) shifts the signed byte pattern 253 ($-3$)
right by the full width. Its proved sign bit is one, so the result pattern
is 255 ($-1$). The circuit enforces the sign extraction before using the
fill byte `255*sign`.
[`i128_sar128.s31`](i128_sar128.s31) checks the same rule across eight
limbs: the private pattern is $-3$, and every public output limb must be
65535. It exercises high-width signed fill without decomposing all 128 bits.

The [worked tutorial](../../../docs/fixed-width-integers.md#static-shifts-and-rotations-by-hand)
shows the bit wiring and how it becomes AIR checks. The
[native acceptance gate](../../../tests/acceptance/math/shifts.py) pins the
cost and checks proofs, statement tampering, and false outputs. The
[Lean model](../../../../../../formal/s31/S31/Gadgets/IntegerShift.lean)
proves the five width-generic bit-vector equations. Correspondence between
that model and production Zig lowering remains an explicit audit boundary.
