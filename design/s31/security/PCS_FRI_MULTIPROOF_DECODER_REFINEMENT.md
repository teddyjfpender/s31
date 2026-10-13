# Lifted Merkle compressed decoder refinement check

The S31 verifier calls the pinned `stwo-zig` lifted Merkle verifier. Its proof
contains a **compressed** list of sibling hashes, while the FRI capture
records one **full** authentication path per requested leaf. The deterministic
decoder is the bridge between those representations.

[`pcs_fri_decoder_refinement_native.zig`](../../../formal/s31/tests/pcs_fri_decoder_refinement_native.zig)
builds a complete eight-leaf tree independently of the decoder. For every one
of the 255 nonempty query subsets it creates a compressed witness from that
tree, asks the native `verifyWithPathCapture` to verify it, and compares **every
captured sibling at every level** with the original tree. The queries are fed
in reverse order with one duplicate, so the check covers native sorting,
deduplication, witness cursor order, paired nodes, ancestor lookup, and copying
paths back to the caller's order. A separate two-column case verifies native
log-size column ordering before leaf hashing. This finite check runs the
actual pinned Zig decoder and S31's `Blake2sPlainMerkleHasher`, whose leaf and
parent hashing have no type prefixes.

For example, query leaves `1`, `3`, and `7` in an eight-leaf tree. `Lᵢ` is a
leaf hash and `Pᵢⱼ` is the parent of the indexed leaf pair:

```text
layer 0: queried L1,L3,L7 consume witnesses L0,L2,L6
         frontier becomes P01,P23,P67
layer 1: P01,P23 pair without witness; P67 consumes P45
         frontier becomes P0123,P4567
layer 2: P0123,P4567 pair without witness; frontier becomes root

compressed witness: [L0,L2,L6,P45]
captured path for 1: [L0,P23,P4567]
captured path for 3: [L2,P01,P4567]
captured path for 7: [L6,P45,P0123]
```

The test also requires a short witness, surplus witness, changed hash,
inconsistent duplicate row, and out-of-domain index to fail without publishing
a capture. The companion [source guard](../../../scripts/s31_formal_lib/pcs_fri_capture.py)
pins the reviewed `verifyImpl` stages and has hostile mutation tests. Run both
with:

```sh
formal/s31/tests/run_pcs_fri_decoder_refinement_native.sh
```

This is a **finite executable refinement check**, not a proof of arbitrary
height Zig semantics. The existing
[`MultiproofDecoder.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofDecoder.lean)
proves one-layer model properties and
[`MultiproofCapture.lean`](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofCapture.lean)
proves that modeled full paths replay to the checked root. The native
all-height simulation remains to be proved. The test does not establish that
the native committed tree was built from the intended oracle columns, nor a
quantitative BLAKE2s collision reduction. The Merkle binding theorem compares
openings at the **same root, height, and index** and extracts a concrete leaf
or parent collision; it makes no global injectivity assumption. P06 stays open
until those native origin and cryptographic obligations are discharged.
Empty-tree placeholders and cross-height reuse of a plain-hash root are outside
this finite check and need explicit protocol-level shape handling.
