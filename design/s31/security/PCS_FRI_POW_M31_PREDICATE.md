# P07: the two Gate PoW predicates after M31 reduction

The selected Gate verifier checks two proof-of-work nonces. The interaction
nonce is checked after the main root and before the lookup challenge. The FRI
nonce is checked after the final FRI coefficients and before raw query draws.
Both use the `Blake2sM31MerkleChannel`; the selected bit counts are 20 and 26.
An invalid nonce returns before it is absorbed. A valid nonce is absorbed as
little-endian `u64`, resetting the channel draw counter before the next draw.

For either stage, the verifier computes:

```text
prefix = M31_BLAKE2s(LE32(0x12345678) || zero[12] || digest[32] || LE32(bits))
result = M31_BLAKE2s(prefix[32] || LE64(nonce))
accept iff trailingZeroBits(result[0..16]) >= bits
```

`M31_BLAKE2s` reduces each little-endian output word modulo
`p = 2^31 - 1`. Since both selected bit counts are at most 31, the final
predicate only reads the low `bits` of the first reduced word. The
[Lean theorem](../../../formal/s31/S31/Gadgets/PcsFri/PowM31Predicate.lean)
identifies that predicate, for **every** raw 32-bit first word, with the zero
fiber of the previously proved M31 masked-query map.

## Counting by hand

The raw 32-bit range has size `2^32 = 2p + 2`. Every residue modulo `p`
occurs twice, except residues 0 and 1 occur a third time. For `1 ≤ bits ≤ 31`,
exactly `q = 2^(31-bits)` residues in `0..p-1` have their low `bits` zero.
Residue 0 contributes the extra third preimage. Therefore:

```text
favorable raw first words = 2q + 1 = 2^(32-bits) + 1.
```

| Gate barrier | bits | Ideal raw zero-bit words | Actual M31 favorable words | One-try fraction under uniform raw 32-bit output |
| --- | ---: | ---: | ---: | ---: |
| Interaction | 20 | 4,096 | 4,097 | `4097 / 2^32` |
| FRI | 26 | 64 | 65 | `65 / 2^32` |

Examples of the extra zero fiber are raw first words `0`, `p`, and `2p`:
all reduce to zero. Raw `2p+1 = 2^32-1` reduces to one and fails either
selected predicate. The exact counts are proved in Lean; the
[native differential](../../../formal/s31/tests/pcs_fri_pow_m31_predicate_native.zig)
checks native verification with the production bit counts at both saved
pre-PoW states of the **8-bit pedagogical transcript fixture**. Its oracle
uses independent standard-library BLAKE2s and arithmetic M31 reduction;
it also checks the reducer on boundary words. The [source guard](../../../scripts/s31_formal_lib/pcs_fri_pow_m31_predicate.py)
pins the selected bit counts, profile, barriers, prefix/nonce encodings,
fixed-block hash reduction and low-bit predicate.
Two pinned positive vectors at the production 20- and 26-bit counts are also
accepted by both the independent oracle and the native verifier.

This is a one-try **conditional** finite count. It does not prove that an
adversary's nonce attempts are independent, that the raw hash is a random
oracle, or that the two PoW stages multiply their work factors. It assigns no
grinding credit in the PCS/FRI error ledger. A full P07 discharge still needs
the native-to-BCS transcript reduction, cross-role framing or collision
analysis, a total adversarial hash-work budget `T`, and the published theorem's
round/error parameters. Native proven security bits remain unset.
