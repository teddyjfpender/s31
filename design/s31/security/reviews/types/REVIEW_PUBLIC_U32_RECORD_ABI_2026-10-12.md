# Independent review: public u32 record ABI

Reviewed commit: `b82afc0` (`Add public u32 record ABI with two-limb direct range proof`).
The review covered the public `u32` record path under `direct-gate`. It did not
cover private `u32`, chip or mixed lowering, arbitrary source programs, or the
underlying proof system.

## Value and proof binding

The source type `u32` has two little-endian `u16` limbs. The typed record
descriptor says `kind: u32`, `length: 2`; its relation input is a public
`u16[2]` wire. Python and Zig both reject any other limb count for this tag.
The type tag, field name, order, and wire alias enter the canonical v2 ABI
digest. A `u16[2]` descriptor over the same relation therefore has a
different key identity.

The native direct circuit calls the arithmetic bit decomposition for each
limb of a public `u32` input. Each of the 32 bits is Boolean and each limb is
reconstructed from its own 16 bits. Since `2^16 < 2^31-1`, the field
reconstruction identifies a unique canonical limb. The record output must
alias a public input with the same `u32` tag and wire. The statement parser
requires the two input and two output words to agree for an alias, and caps
each word below 65536. Flat assignments encounter the relation's own `u16`
range check, even if the typed JSON adapter is bypassed.

The record wrapper adds no arithmetic rows relative to the equivalent
`u16[2]` descriptor on the same relation. The 32-bit range proof itself is
real work; “zero cost” applies to naming and packing the already constrained
limbs as one source-level record field.

## Adversarial controls

[`public_u32_adversarial_v2.py`](../../../../../src/frontends/s31/tests/acceptance/record_abi/public_u32_adversarial_v2.py)
checks the independent Python and production Zig descriptor/statement parsers.
The five descriptor attacks include coherently changing the relation and
descriptor to one or three `u32` limbs, a private `u32` input with a separate
public M31 claim, and two directions of a `u32`/`u16[2]` alias type mismatch.
The nine statement attacks include a high limb at 65536 or the M31 modulus,
a negative, Boolean or floating high limb, an input/output high-limb mismatch,
a duplicate nested JSON key, and noncanonical whitespace/newline encodings.
The honest case uses `[65535,32768]`, which is `0x8000ffff` in little-endian
order. All attacks were rejected by both parsers.

The review found no accepted malformed descriptor or public claim in this
bounded corpus. Native malformed float and duplicate-key statements initially
failed closed with `InvalidRecordAbi` and `DuplicateField`, respectively.
`claimedWords` now maps those parser failures to `InvalidRecordStatement`
while preserving `OutOfMemory` as a resource error. This fixes the statement
error contract; it is not a proof-soundness repair.

## Limits

The acceptance test for the feature separately runs native proofs at zero,
maximum and mixed limbs, changed-claim rejection, and a geometry comparison
against a `u16[2]` descriptor. This review's native corpus stops at parser and
relation admission. Neither test proves the whole Python-to-Zig compiler
correspondence or the soundness of the native AIR, PCS or FRI implementation.
