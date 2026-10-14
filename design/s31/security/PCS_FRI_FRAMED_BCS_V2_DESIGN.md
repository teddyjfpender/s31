# Versioned BCS framing for a future paired Gate proof

**Status:** candidate protocol design and executable byte model. The selected
S31 raw Gate proof remains `S31NAT8R`; this document does not change its
prover or verifier. There is no native BCS/ROM theorem, no assigned native
collision width, and no release admission from this design.

The [raw Gate audit](PCS_FRI_RAW_GATE_BCS_AUDIT.md) proves that unframed
`BLAKE2s(digest || root)` can be both a transcript root absorption and a plain
Merkle parent hash input. A canonical root can also be the field payload for
two QM31 values. These are byte-input role overlaps, with no demonstrated
accepted-proof forgery. The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf)
puts the BCS/ROM term inside a round-by-round IOP reduction; a new format
with separated roles is a practical prerequisite for applying a standard
domain-separated hash model to S31. Tags alone do not supply the IOP theorem,
adaptive adversary bound, or native byte refinement.

## Proposed format boundary

Reserve `S31NAT9F` for a future paired, framed ordinary Gate proof. This
selector is **not accepted** by the installed runtime. It must have distinct
package channel profile, verification-key schema and profile strings, and a
new PCS protocol revision. The existing `S31NAT8R` decoder and its key remain
unchanged. A verifier must derive the selector and expected profile from the
package and key, reject cross-version proofs, and bind the relation, key,
four source-tree shapes, and full FRI configuration before its first random
challenge.

The candidate's one BLAKE2s-256 oracle call is:

```text
H( ASCII("S31BCS2") [7]
   || role [1]
   || LE64(payload byte length) [8]
   || LE64(verifier-derived event number) [8]
   || payload )
```

All lengths and event numbers must be within `u64`; no truncation or wrap is
allowed. The byte parser rejects unknown roles, wrong lengths and trailing
bytes. The `event` number denotes a protocol stage. Repeated challenge-block
draws at one stage also include a checked `u32` counter in the payload. A
rejected M31 challenge block consumes another counter; a nonce trial includes
its own `u64` nonce in the payload. The event schedule is verifier-derived
from the key and checked proof geometry, never supplied by the prover.

| Role | Byte value | Payload after the 24-byte frame header |
| --- | ---: | --- |
| `field_absorb` | 1 | current digest `[32]` followed by canonical little-endian M31 limbs, four per QM31 |
| `root_absorb` | 2 | current digest `[32]` followed by a root `[32]`; the event identifies tree kind and stage |
| `nonce_absorb` | 3 | current digest `[32]` followed by accepted `u64` nonce |
| `raw_word_draw` | 4 | current digest `[32]` followed by checked `u32` block counter |
| `pow_prefix` | 5 | current digest `[32]` and difficulty `u32` |
| `pow_trial` | 6 | prefix digest `[32]` and candidate `u64` nonce |
| `merkle_leaf` | 7 | tree context `[32]` and canonical M31 row bytes |
| `merkle_parent` | 8 | tree context `[32]`, ordered left `[32]`, right `[32]`; event is the tree level |
| `tree_context` | 9 | canonical tree descriptor, including key digest, tree kind/track, height and column-roster digest |
| `statement` | 10 | canonical program/key/profile/FriConfig statement frame |

The [Python byte model](../../../scripts/release/pcs_fri_framed_bcs_v2.py)
implements these frames, strict parsing and representative hash operations.
The [Lean model](../../../formal/s31/S31/Gadgets/PcsFri/FramedBcsV2Encoding.lean)
proves distinct role bytes give distinct *hash inputs* for arbitrary payloads,
that a fixed role/event retains its payload, and that distinct event numbers
below `2^64` have distinct little-endian encodings and hence separate stages.
It does not prove Zig uses these bytes or that BLAKE2s acts as a random oracle.
The eventual Zig implementation must enforce bounded, nonwrapping `u64`
numbering.

## Paired Gate event order

The experimental P05 paired protocol uses **one transcript channel** for
the four source roots and both FRI degree tracks. The proposed frame plan
follows its current event order:

```text
statement
  fixed root → circuit identity → public outputs → main root
  interaction PoW check → accepted nonce mix → lookup z, alpha draw
  interaction claim → interaction root → composition gamma draw
  composition root → OOD seed/point draw → sampled values mix
  common cross-height batch lambda draw
  for each fold height, descending:
      fold alpha draw
      if nonterminal: original line root → own-quotient line root
  original terminal coefficients → own-quotient terminal coefficients
  PCS PoW check → accepted nonce mix → raw query draws
  authenticated opening and fold checks under all source and line roots
```

The alpha-before-pair-root ordering is specific to this experimental paired
candidate. The old raw Gate profile retains its existing root-before-alpha
FRI order. Neither sequence can share a proof selector. The
[`candidate_paired_gate_plan`](../../../scripts/release/pcs_fri_framed_bcs_v2.py)
function allocates distinct event ordinals for a strictly descending fold
height roster and both line tracks. Its two-height report is illustrative;
the production roster and wire must be frozen together before implementing
native dispatch.
The currently accepted native path draws DEEP randomness after sampled-value
absorption. This *new versioned* paired candidate draws one common batch
`lambda` at that same relative point, replacing the legacy DEEP draw. Its
algebra, FRI relation and round-error ledger require a new proof; old proof
bytes and challenge values cannot be reused.

There is a current hash-profile mismatch to resolve deliberately: production
Gate source roots use `Blake2sPlainMerkleHasher`, while the CAS09 experimental
line prover uses `Blake2sMerkleHasher`. They are not byte-identical. The new
protocol must choose and implement one versioned Merkle byte profile for both
track trees, or specify and prove two separately typed profiles with distinct
tree contexts. Its fixed preprocessed root and verification key must be
recomputed if that tree's hash profile changes. Do not reuse a legacy root
under the new selector.

## Cost and implementation path

The framing is designed to keep nonce grinding cheap. A PoW trial is
`24 + 32 + 8 = 64` bytes, so a straightforward BLAKE2s implementation still
uses one 64-byte compression block per trial. A raw query draw is 60 bytes.
Root absorption grows from 64 to 88 bytes and a parent with 32-byte tree
context grows from 64 to 120 bytes; a direct implementation uses two blocks
for each of those calls. Because Merkle hashing dominates large traces, this
cost must be measured before selecting the format. A precomputed per-tree,
per-level BLAKE2s prefix state could amortize a fixed first block, but that
requires an explicitly frozen byte encoding and differential proof; the
current 120-byte prototype does not claim that optimization.

**One-block parent candidate.** Zig's BLAKE2s implementation accepts an
eight-byte personalization (`.context`) that changes the initial chaining
state without adding message bytes. A new, separately versioned Merkle profile
could use `BLAKE2s-256(context="S31P2PAR", left[32] || right[32])` for an
internal node, and a different fixed personalization such as `S31P2LEF` for
leaves. The parent then has one 64-byte message block. No tree descriptor is
truncated into the eight-byte parameter: the *full* descriptor, height and
column roster must be checked against the key, absorbed in the initial
statement, and bound to each root at its verifier-derived event. A Merkle
binding proof must account for that root-level context instead of assuming
independent per-tree hash oracles. In particular, personalization is a
different oracle interface from the 24-byte framed input modeled above; the
Lean frame-separation lemmas do not establish separation across parameter
values or its random-oracle theorem. The source and line tree hash profiles,
and any rederived fixed root/key, must be selected in one new proof version.
The 120-byte framed parent remains the executable candidate until this
alternative has exact native/Python byte parity and a soundness argument.

For a limited throughput check on this host, CPython `hashlib.blake2s` took
0.254–0.266 seconds for one million personalized 64-byte hashes and 0.288
seconds for one million unpersonalized 120-byte framed hashes (two runs each,
single process, fixed inputs). This includes Python call overhead and is not
a Zig prover benchmark; the compression count is the more portable cost
signal. Benchmark the native tree builder and verifier before freezing either
profile.

The implementation sequence is:

1. Freeze the paired wire, tree descriptor and event table together with a
   new protocol revision. Bind all four source roots and both FRI tracks to
   verifier-derived tree contexts; reject shape or profile mismatch before
   any challenge.
2. Implement the framed raw channel and framed Merkle profile in stwo-zig as
   new types. Use typed call sites or a checked stage machine so every mix,
   draw and PoW call gets its intended role and event. Keep legacy types and
   proof bytes intact.
3. Add the new S31 prover/verifier selector, key schema, package manifest and
   explicit `S31NAT9F` parser together. Require full native/Python byte
   parity across variable rejection loops, both nonce barriers, all fold
   heights, duplicate queries, and each Merkle tree kind. Retain strict
   source revision and installed-binary fingerprints.
4. Prove the selected native execution refines the framed model, including
   canonical input encodings and Merkle path ownership. Then prove an
   adaptive ROM/BCS reduction with one accounting of all oracle calls,
   grinding attempts, root/leaf/parent collisions and the chosen `T=2^64`.
   Finally join the paired PCS/FRI degree-corrected IOP theorem and every P09
   error term. Only that full chain may assign native proven bits.

Run the prototype controls:

```sh
python3 -B -m unittest scripts.tests.test_pcs_fri_framed_bcs_v2
python3 -B scripts/release/pcs_fri_framed_bcs_v2.py
python3 -B scripts/release/pcs_fri_framed_bcs_v2.py --require-native-soundness
```

The last command intentionally fails. The report always keeps
`native_proven_security_bits=null` and `proven_release_admissible=false`.
