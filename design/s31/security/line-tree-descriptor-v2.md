# Candidate S31NAT9F line-tree statement binding

The exact Python byte model is
[`pcs_fri_line_descriptor_v2.py`](../../../scripts/release/pcs_fri_line_descriptor_v2.py).
The native peer is `src/core/vcs_lifted/line_descriptor_v2.zig` in stwo-zig.
This profile is reserved and unselected.

The line hash profile is fixed by leaf personalization `S31P2LEF`, parent
personalization `S31P2PAR`, canonical M31 little-endian leaf words and a
64-byte `left || right` parent message. Its 32-byte identifier is the framed
role-9, event-0 BLAKE2s hash of
`S31LINE2S31P2LEFS31P2PARM31LE32|P64`. The four source roots keep the
production plain BLAKE2s profile.

Each line-tree descriptor has this canonical layout. All integers use
unsigned little-endian encoding:

```text
S31LTDV2 [8 bytes] | track [u8: original=1, own=2]
| fold height [u32] | binary Merkle log size [u32, at most 63]
| exact transcript root event [u64] | sealed key digest [32]
| fixed line hash profile digest [32] | column count [u32, 1..256]
| ordered unique column identity digests [32 bytes each]
```

`S31LTMV2` manifests begin with the sealed key digest, fixed profile digest,
fold count `u32` (1..64), strictly descending fold heights (`u32` each), and
tree count `u32`. Each tree is prefixed by its byte length `u32`. Exactly two
trees occur at each nonterminal fold height, in original then own quotient
order. Their root event ordinals are `17 + 3i` and `18 + 3i` for fold index
`i`, matching the proposed four-root Gate transcript plan. The last fold
height is present in the roster but has terminal coefficients rather than
line roots. The framed role-9, event-0 digest of the full manifest goes in
`StatementBinding.line_profile_digest`; the manifest and statement key
digests must agree. The whole manifest is capped at 512 KiB before allocation.
Column identity digests come from distinct key-owned column identities; their
row values may be equal. `tree_log_size` and fold height are both committed,
but the candidate Gate key has not fixed their arithmetic relation. The
selected key derivation must validate that relation against proof geometry.

This commits a named root to its planned event and tree geometry only if the
selected verifier privately derives the descriptors and ordered column IDs
from a sealed key, checks the statement geometry, and hands each opening
checker the root it actually absorbed at that event. The current candidate
functions accept caller-supplied structures and do not prove that custody
property. The event wrapper also has public mutable fields in Zig; a selected
verifier must encapsulate it.

Exact Python and Zig vectors pin the same descriptor bytes, manifest length
and digest. Tests reject reordered or duplicated tracks, wrong event
ordinals, malformed rosters, wrong statements and malformed paths. This does
not establish a BLAKE2s random-oracle model, a BCS reduction, or native
security bits. The official Circle FRI theorem map also leaves the used
non-squaring-consistent query variant without a complete LDR proof; the
selected verifier must show one raw query projects consistently through all
folds and match a proven theorem before release admission.

The candidate native opening helper rehashes all manifest bytes for every
opening, costing `q × manifest_bytes` hashed bytes across `q` queries. A
selected verifier needs one-time statement admission and a privately owned
validated descriptor cache before checking individual openings. This is an
unimplemented efficiency and custody boundary, not a benchmarked cost claim.
