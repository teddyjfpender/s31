# P06: plain Merkle byte-preimage bridge

The selected S31 PCS uses plain BLAKE2s for its lifted Merkle tree. A leaf
message is the concatenation of each canonical M31 word's four little-endian
bytes in committed column order. A parent message is its 32-byte left digest
followed by its 32-byte right digest. There is no leaf or parent tag.

[`MerkleBytePreimage.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MerkleBytePreimage.lean)
proves that encoding a canonical M31 row into leaf bytes is injective,
including across different row lengths. It also proves that concatenating two
fixed 32-byte child digests preserves their order and identity. Combined with
the existing same-root, same-index, same-height `MerkleOpening` theorem, two
different accepted rows yield a collision on **different byte messages** sent
to the same abstract 32-byte hash function: either two leaf messages or two
ordered parent messages. No global hash injectivity is assumed.

For a concrete leaf, the row `[1, 256, 2147483646]` hashes these 12 bytes:

```text
01 00 00 00 | 00 01 00 00 | fe ff ff 7f
```

The native differential
[`pcs_fri_merkle_byte_preimage_native.zig`](../../../formal/s31/tests/pcs_fri_merkle_byte_preimage_native.zig)
compares `Blake2sPlainMerkleHasher` against Zig's standard BLAKE2s over
explicitly assembled messages. It covers canonical boundary words and row
lengths 0, 1, 7, 15, 16, 17, 31, 32 and 33, then compares ordered parent
digests. Sixteen M31 words occupy 64 bytes, exactly a parent message's
length. That overlap is real in this plain-hash profile; the collision
reduction is therefore for a **fixed tree shape and opening type**. A protocol
that reuses a root across different shapes needs a separate shape-binding
argument.

The [source guard](../../../scripts/s31_formal_lib/pcs_fri_merkle_byte_preimage.py)
pins the selected plain profile, leaf bytes, parent child order, and S31's
post-verification path replay. Seven hostile source mutations must fail it.
Run the focused checks with:

```sh
formal/s31/tests/run_pcs_fri_merkle_byte_preimage_native.sh
```

This closes the **abstract canonical-row-to-byte-message reduction** and
gives source-bound finite native evidence. P06 remains open: the Zig decoder
has no all-input operational-semantics refinement to Lean, prover column
origin is not universally proven, the installed verifier is not joined to
this theorem, and no quantitative BLAKE2s collision bound or full BCS work
budget has been established.

## QM31 FRI row bridge

[`FriQm31BytePreimage.lean`](../../../formal/s31/S31/Gadgets/PcsFri/FriQm31BytePreimage.lean)
models one QM31 evaluation as four canonical M31 coordinates in the pinned
`[c0.a, c0.b, c1.a, c1.b]` order. It proves that flattening an arbitrary
list of such evaluations into an M31 row is injective, including when the two
lists have different lengths. Thus, given **two accepted full paths** for
different QM31 rows at the **same** root, height, and leaf index, the existing
plain-byte lemma produces two distinct byte messages with the same digest.
The theorem requires canonical coordinates and fixed 32-byte sibling/digest
types. It covers the one-evaluation unpacked row and four-evaluation packed
row used by the selected FRI verifier; it does not infer either accepted path
from a Zig proof.

The pinned [`fri_merkle_admission.zig`](../../../src/frontends/s31/runtime/fri_merkle_admission.zig)
flattens each captured evaluation with `toM31Array()` and writes coordinate
`j` at `offset * 4 + j`. The existing source guard checks both operations and
the admission call in all four S31 verifier paths. The focused native byte
test now independently encodes one- and four-evaluation rows and compares
the production leaf hasher to BLAKE2s on those exact bytes. This joins the
formal message representation to the reviewed finite native path; universal
Zig-to-Lean decoder semantics and quantitative collision security remain
open.
