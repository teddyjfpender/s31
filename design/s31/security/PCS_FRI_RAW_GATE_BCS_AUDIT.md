# Raw Gate verifier transcript and the open BCS boundary

**Status:** source-bound deterministic transcript evidence for opt-in ordinary
Gate `raw-blake2s-rejection-v1`. The raw channel's fixed-prefix draws and
masked query indices have exact finite counts, but no adaptive BCS/ROM or
complete P09 error theorem has been proved for the native verifier. The
selected target remains `epsilon(T)/T <= 2^-96` at `T=2^64` BLAKE2s
queries. Native proven bits are `null`; the release gate remains closed.

Run the [diagnostic](../../../scripts/release/pcs_fri_raw_gate_bcs.py):

```sh
python3 -B scripts/release/pcs_fri_raw_gate_bcs.py
python3 -B scripts/release/pcs_fri_raw_gate_bcs.py --require-adaptive-bcs
bash formal/s31/tests/run_pcs_fri_raw_gate_bcs_transcript_native.sh
```

The second command exits 2. The diagnostic requires the exact pinned engine
gitlink and eleven reviewed engine-file SHA-256 values. It checks the S31
prover/verifier profile dispatch and source event order, then reports hashes
of the two S31 runtime files actually inspected. A changed reviewed engine
file or removed/reordered source stage rejects. These are source checks; they
do not attest the installed executable or prove all Zig control flow.

## What is in a raw ordinary Gate proof

The native verifier accepts only the `S31NAT8R` wire selector for this
entrypoint. Its 192-byte prefix is eight magic bytes, a little-endian `u64`
interaction nonce, and eleven claimed QM31 interaction sums, each encoded as
four canonical little-endian M31 `u32` limbs. The remainder is a bounded
postcard STARK proof. The decoder requires exactly four commitment roots,
the selected PCS configuration, the key's preprocessed root, complete input
consumption, and a 16 MiB proof cap with 64 MiB bounded decoding storage.
The raw verifier excludes recursive conversion and chip composition.

The reviewed source follows this order for an accepting ordinary Gate path:

```text
raw wire + canonical sums + four roots checked
  → salt and FRI configuration
  → fixed root → circuit identity root → eight public values → main root
  → verify interaction PoW (20 bits) → absorb nonce
  → draw lookup z, alpha → check lookup sum
  → absorb interaction claims → interaction root
  → draw AIR coefficient → composition root
  → draw OOD seed → check AIR/OOD identity
  → absorb OOD sampled values → draw DEEP coefficient
  → each FRI root then its fold challenge → absorb terminal coefficients
  → verify FRI PoW (26 bits) → absorb nonce
  → draw 70 raw query positions → verify openings and FRI equations
```

The four roots occur at distinct challenge-dependent epochs. Failed nonce
checks exit before absorption. The native PCS authenticates sampled original
rows and computes one accumulated quotient answer per query, so the
[degree-correction P05 gap](PCS_FRI_DEGREE_CORRECTION_GAP.md) persists.

The [synthetic transcript fixture](../../../formal/s31/tests/pcs_fri_raw_gate_bcs_transcript.json)
uses small 8-bit PoW checks, fixed roots and values, and one inner FRI layer.
An independent Python BLAKE2s-256 state machine generates all digests,
nonces, challenges and 70 query positions. The
[native Zig replay](../../../formal/s31/tests/pcs_fri_raw_gate_bcs_transcript_native.zig)
matches each retained value, six digest/counter checkpoints and all nine
query-hash blocks. It is **not** an accepted STARK proof or an adversarial
proof fixture. Production PoW remains 20 and 26 bits; the source guard pins
those constants separately. The [six Python tests](../../../scripts/tests/test_pcs_fri_raw_gate_bcs.py)
reject changes to profile dispatch, magic, PoW barriers, rejection rule,
draw preimage and counter handling.

## Fixed-prefix ideal-raw counts

For one fixed transcript digest, model each distinct raw BLAKE2s input as
independent uniform 256-bit output. `drawBaseFelts` rejects a whole eight-word
block if any `u32 >= 2p`, where `p=2^31-1`. The accepted-block fraction is

```text
a = (2p / 2^32)^8 = (1 - 2^-31)^8.
```

Each accepted M31 residue has two raw preimages, so the two QM31 lookup
challenges from one accepted block are uniform under this premise. Rejected
blocks consume counter values; the next accepted block is still uniform if
the distinct hash outputs are independent. The [existing Lean sampler
theorem](../../../formal/s31/S31/Gadgets/PcsFri/RawMaskedQuery.lean) proves
that masking an unreduced `u32` by `2^k-1` has exactly `2^(32-k)` preimages
per query index. It counts vectors with replacement, so duplicates are
allowed.

At the two production PoW barriers, raw BLAKE2s output is not M31-reduced.
The predicate reads low bits of the first raw `u32`; the
[new Lean lemmas](../../../formal/s31/S31/Gadgets/PcsFri/RawGateBcsBoundary.lean)
give exactly 4096 favorable words for 20 bits and 64 for 26 bits. Thus a
**single fresh ideal-raw trial at a fixed prefix** succeeds with fractions
`2^-20` and `2^-26`, respectively. The theorem does not grant 46 bits of
combined grinding credit. It does not count an adversary's search or the
relationship between nonce choice, later challenges, and committed oracles.

### Two-stage adaptive search ledger

The source order matters: the interaction nonce is checked before absorption,
then its accepted value changes the lookup draws, interaction commitment,
composition challenge and root, OOD draws, and FRI commitments. Only after
those events does the verifier check the FRI nonce. The nonce predicate first
hashes a 52-byte prefix message `LE32(0x12345678) || 12 zero bytes || digest
|| LE32(bits)`, then a 40-byte message `prefixDigest || LE64(nonce)`. The
accepted nonce absorption separately hashes `channelDigest || LE64(nonce)`.
The prefix digest can be cached for distinct nonces at the same stage state.

Here is the strongest **conditional** search accounting established in
[`RawGateTwoStageGrinding.lean`](../../../formal/s31/S31/Gadgets/PcsFri/RawGateTwoStageGrinding.lean).
Assume every fresh, distinct nonce-trial input has uniform independent raw
output even conditioned on all prior oracle traffic, and that any earlier
query of the same bytes is charged and cannot be treated as fresh. For a stage
with at most `n` trials of conditional pass probability at most `p`, its hit
probability is at most `min(1,n p)`. The exact all-fresh fixed-stage value is
`1-(1-p)^n`. If each possible first success selects a different FRI prefix,
the weighted second-stage branch lemma still bounds the linked two-stage hit
by the first-stage mass times a uniform conditional second-stage bound.

| Barrier | Native bits | One fresh nonce | At most `n` fresh trials |
| --- | ---: | ---: | ---: |
| Interaction | 20 | `2^-20` | `min(1,n/2^20)` |
| FRI, conditional on any first-stage history | 26 | `2^-26` | `min(1,n/2^26)` |

Even under these stronger hypothetical freshness assumptions, an adversary
with `T=2^64` BLAKE2s queries has PoW-only envelopes of `1` for either
stage. The resulting `1/T=2^-64` trivial work-factor upper bound is larger
than the chosen `2^-96` target, so **PoW alone cannot certify that target**.
For just one nonce at each fixed barrier the fresh-oracle joint chance would
be `2^-46`; allowing only one extra interaction trial already makes the
two-stage chance strictly larger. Adding 20 and 26 as unconditional
"security bits" is therefore invalid. These are probabilities of finding
valid PoW nonces, not probabilities of accepting a false STARK statement.

The raw profile does not satisfy the byte-domain premise by syntax. The
40-byte PoW nonce input and the 40-byte accepted-nonce absorption input are
equal whenever `prefixDigest = channelDigest`; a ROM proof would have to
bound or rule out that coincidence in reachable transcripts. Root absorption
also exactly overlaps plain Merkle parent hashing and sometimes field
absorption, as shown below. The Lean branch bound is therefore **not applied
to the selected native channel**. A complete reduction would have to count
all prior, repeated, cross-role and adaptive queries, model both accepted
nonce barriers jointly with the later STARK checks, and identify a valid
multi-round IOP theorem. The release gate and proven-bit value remain closed.

After an accepted FRI nonce is absorbed, the draw counter resets to zero.
The FRI query path calls `drawU32s` directly, with **no field rejection**:
70 words use exactly nine 32-byte hash blocks at counters `0..8`. Each block
hashes `digest || LE32(counter) || 0x00` (37 bytes). The native counter
increments before the hash and traps rather than wrapping at `2^32-1`.
Earlier field-challenge epochs may make an unbounded number of whole-block
rejection attempts; there is no fixed worst-case draw count for those epochs.
The [Lean nine-counter result](../../../formal/s31/S31/Gadgets/PcsFri/RawGateBcsBoundary.lean)
establishes only the bounded post-nonce query epoch. The generic
[hash-input length proof](../../../formal/s31/S31/Gadgets/PcsFri/BcsTranscriptEpoch.lean)
also applies to this raw channel: a 37-byte query preimage cannot equal the
52-byte PoW-prefix input, 40-byte PoW-nonce input, or a 32-byte digest plus
a whole number of four-byte words. It does not separate two 64-byte
absorption roles such as a root and two QM31 values.

## The quantitative theorem interface

The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf) states a BCS/ROM
term `3(T^2+1)/2^lambda` in absolute error. If **hypothetically** its theorem
applied with `lambda=256`, then at selected `T=2^64` its work-factor
contribution would be

```text
3(T^2+1) / (2^256 T) < 2^-126.
```

The inequality is checked with exact rational arithmetic in the diagnostic
and proved in the new Lean file. It is a paper-only bound. Although the raw
channel retains a full 256-bit digest, a native-to-paper BCS theorem must
still account for untagged root/field absorption inputs, reused hash roles,
adaptive commitments, both nonce searches, rejected blocks, Merkle hashing,
and the total adversarial budget. The bound is therefore marked
`applies_to_native_verifier=false` in the report.

At `T=2^64`, the paper collision term **alone** meets the chosen work-factor
target exactly when the hypothetical uniform hash-output width is at least
162 bits: at 161 bits it is above `2^-96`, and at 162 bits it is strictly
below. The diagnostic checks both comparisons using exact fractions and
reports the remaining round-error budget at 162 bits. This does not assign
`lambda=162` or `lambda=256` to the native verifier. In particular, the
separate M31-reduced channel has at most `p^8` output states and a nonuniform
output distribution; its security cannot be read from the raw digest size.

## A concrete byte-encoding obstruction

The selected raw channel and plain Merkle hasher reuse BLAKE2s without role
tags. For any 32-byte `d` and `r`, the source computes both a channel root
absorption and a Merkle parent from the same input bytes:

```text
channel.mixRoot at digest d, root r:  BLAKE2s(d || r)
Merkle parent with children d, r:    BLAKE2s(d || r)
```

Likewise, if each of the eight little-endian `u32` limbs of `r` is below
`p=2^31-1`, `mixRoot(r)` and `mixFelts(two QM31 values encoded by r)`
send identical bytes to BLAKE2s at the same digest. There are exactly `p^8`
such 32-byte strings among `2^256` possible strings. A plain Merkle leaf of
16 M31 words is also 64 bytes, the parent input length. The
[Lean input equalities](../../../formal/s31/S31/Gadgets/PcsFri/RawGateBcsRoleOverlap.lean)
and focused byte tests establish only these encoding overlaps. They do not
construct two accepted Merkle paths or a forged STARK proof.

This is an explicit counterexample to treating the existing hash-call roles
as automatically domain separated. A native BCS proof must work with these
shared input bytes, establish reachable-stage separation, or move to a
separately versioned domain-separated transcript and Merkle profile. The
published `3(T^2+1)/2^lambda` expression cannot simply be assigned
`lambda=256` on the basis of the BLAKE2s output width.

P07 and P09 remain open for five concrete reasons:

1. Prove all accepting native executions and their installed binary match
   the byte-level transcript, including postcard decoding, rejection loops,
   failures, and every possible FRI layer count.
2. Specify a random-oracle domain/collision model for the raw 256-bit hash
   with these untagged role inputs and distinct commitment epochs.
3. Charge adaptive selection of commitments, both valid nonce searches,
   rejected challenge blocks and all oracle queries against `T=2^64`; derive
   the actual effect of PoW rather than adding its bit counts.
4. Join the raw query distribution and authenticated opening relation to
   a matching degree-corrected PCS/FRI IOP theorem. The native quotient-only
   FRI still lacks that paper premise.
5. Instantiate every paper round error at the actual installed parameters.
   The current 70-query, blowup-two ungrinded profile already fails the
   [232-query necessary expression](PCS_FRI_GATE_QUERY_SCALE_PROBE_2026-10-14.md),
   independent of the small hypothetical 256-bit collision term.
