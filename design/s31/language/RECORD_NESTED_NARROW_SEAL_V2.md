# Nested narrow record ABI seal

The [bounded acceptance test](../../../src/frontends/s31/tests/acceptance/record_abi/nested_narrow_seal_v2.py)
checks one source-to-verifier seam: public `u8` and `u16` leaves nested inside a
record and tuple, with a repeated `u16` result alias. It starts from two S31
source texts. Both compile to the **same flat first-order relation** and the
same public values. One source calls the nested input field `digit`; the other
calls it `value`. The native verifier for each package receives its own
generated key and canonical typed statement.

The first source is equivalent to this shortened form:

```s31
struct Inner { byte: u8, digit: [u16; 1] }
struct Request { pair: (Inner, [m31; 1]) }
struct Copy { byte: u8, digit: [u16; 1] }
struct Result { copy: Copy, again: [u16; 1], sum: [m31; 1] }
circuit nested_narrow(public req: Request) -> public Result {
    let byte_field = std::field::from_u16(std::int::limbs(req.pair.0.byte));
    let digit_field = std::field::from_u16(req.pair.0.digit);
    let sum = byte_field + digit_field + req.pair.1;
    Result {
        copy: Copy { byte: req.pair.0.byte, digit: req.pair.0.digit },
        again: req.pair.0.digit,
        sum: sum
    }
}
```

The flattened inputs are three distinct wires: `req.pair.0.byte` as a public
`u8` tag on a `u16` relation limb, `req.pair.0.digit` as public `u16`, and
`req.pair.1` as public M31. The result has four named leaves, but `copy.digit`
and `again` refer to the same input wire. The result therefore contributes
three output slots, alongside three input slots. At byte 255, digit 65535, and salt
`p − 2`, where `p = 2³¹ − 1`, the verifier's eight-word vector is:

```text
[255, 65535, p−2, 255, 65535, 65788, 0, 0]
 input byte digit salt  result byte digit sum  padding
```

The frontend lowers the arithmetic to two `cast_m31` nodes and two `add`
nodes. Direct Gate supplies Boolean reconstruction constraints for the public
`u8` and `u16` input limbs. The two narrow result leaves must alias those
range-checked public inputs; no derived narrow result is admitted. Record
grouping and the repeated `again` name add no arithmetic node.

The static gate pins both source hashes and both canonical ABI digests, checks
the handwritten nested paths, verifies flat relation and assignment equality,
checks the modular sum with the separate Python relation oracle, and compares
the exact typed statement projection. It rejects wrong version, split aliases,
and out-of-range narrow claims before any native proof work.

The native gate builds both source-bound packages and proves the same values
under each. Its key test changes the ABI digest in an otherwise valid key and
requires `InvalidVerificationKey`. Its replay test sends proof A to verifier B
with **B's valid key and B's valid statement**, and vice versa. Thus rejection
must happen after the statement and key are accepted, not merely because a
renamed field made a malformed claim. Malformed version, path, order, `u8`, and
`u16` statements are tested separately at the native statement parser.

The local native run accepted both honest proofs (56,903 and 54,951 bytes),
reported identical padded AIR geometry, and rejected both cross-replays at
`InvalidInteractionNonce`. It also rejected the forged key and all five
malformed statement controls. Proof size here is a fixture observation, not a
cost comparison between two arithmetic programs.

Run from the repository root:

```sh
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_narrow_seal_v2.py
python3 -B src/frontends/s31/tests/acceptance/record_abi/nested_narrow_seal_v2.py --native
```

This is a finite executable correspondence and proof-binding control for two
source programs. A changed source field also changes the embedded source
digest, so the cross-replay rejection establishes the combined source, ABI,
key, and proof seal; it does not isolate which transcript field causes the
failure. It does not prove the general compiler or native STARK verifier
correct for all programs.
