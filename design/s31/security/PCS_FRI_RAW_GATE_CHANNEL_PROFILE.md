# Opt-in raw BLAKE2s Gate channel

The S31 `raw-blake2s-rejection-v1` channel profile is an opt-in, versioned
ordinary `gate` proof profile. It uses the existing stwo-zig
`proving_5a7c5ed.Blake2sMerkleChannel` for both proving and native verification.
Version 1 admits FRI fold step 1 only.
The legacy Gate profile continues to use `Blake2sM31MerkleChannel` and its
existing proof and key formats. Raw Gate does not generate recursive or fold
keys and rejects recursive or fold commands.

**Security status:** ideal raw BLAKE2s draws remove the legacy modulo-bias
factor for this version's fixed-prefix challenge sample. The native profile
still uses 70 FRI queries, below the **232-query necessary arithmetic** for
the selected `T=2⁶⁴`, 96-bit paper work-factor target in the illustrative
single-point calculation. The P05 degree-correction, multi-domain FRI, and
adaptive BCS joins remain open. This profile has **no proven release-security
bit count**; 232 queries alone would not close those joins. See the
[conservative-profile decision](PCS_FRI_CAS05_CONSERVATIVE_PROFILE_DECISION.md)
and [query-scale probe](PCS_FRI_GATE_QUERY_SCALE_PROBE_2026-10-14.md).

## One fixed-prefix draw

For a fixed transcript prefix, assume each distinct draw-counter input yields
an independent uniform raw 32-byte BLAKE2s block, containing eight independent
uniform `u32` words. The channel rejects the **whole** block if
any word is at least `2p`, where `p=2³¹−1`, increments its draw counter, and
tries again. A retained word is uniform on `[0,2p)`. Every M31 residue has
exactly two retained preimages (`r` and `r+p`), so the eight output residues,
and therefore the two QM31 lookup challenges formed from them, are uniform
under that premise. The acceptance probability per block is
`(2p/2³²)^8 = (1−2⁻³¹)^8`; the rejection probability is about `3.73×10⁻⁹`.
The raw channel also uses raw BLAKE2s when mixing transcript data; this is a
different transcript, not just a change to lookup sampling.
For comparison, the selected legacy M31-reduced channel has the sharp
one-pair worst-case density ratio `(3p/2³²)^8 ≈ 25.6289061545`; see the
[finite-model count](PCS_FRI_LOOKUP_PAIR_BIAS.md). The raw rejection profile
removes that local sampling factor under the stated fixed-prefix premise.

The Gate preprocessed commitment hasher remains
`Blake2sPlainMerkleHasher` for both channel profiles. The fixed-root bytes
can therefore be shared, while the proof transcript cannot. The generated
key binds `channel_profile`, `circuit-raw-v1`, a distinct key schema, the
roster digest and fixed root. The raw proof has distinct `S31NAT8R` magic;
legacy and raw native verifiers reject one another's proof bytes and keys.

This argument is conditional on ideal independent raw hash words **for one
fixed draw input**. It is not a BCS/Fiat–Shamir reduction for adaptive
transcripts. An attacker can select commitments and valid PoW continuations,
and the number of tests and hash queries must be charged in a full theorem.
The native PCS/FRI P07 and P09 blockers stay open; no native proven security
bits follow from this profile alone.
The current source-bound P02 Gate interaction diagnostic admits the legacy
profile only; its source pin is refreshed, but it is not a raw-profile
soundness certificate.

### Raw FRI query indices

The [Lean sampler lemma](../../../formal/s31/S31/Gadgets/PcsFri/RawMaskedQuery.lean)
models the actual low-bit operation after the raw channel's `drawU32s`:

```text
index = word & (2^k − 1) = word mod 2^k,     0 ≤ k < 32 in the native path.
```

For any fixed index, exactly `2^(32−k)` of the `2^32` possible raw words map
to it. The arithmetic lemma also covers `k=32`; native `u32` shifting must
use `k<32`. It counts all `s`-draw vectors with replacement, so duplicate
queries cause no exception. The [source guard](../../../scripts/s31_formal_lib/pcs_fri_raw_query.py)
pins raw prover/verifier selection, the unreduced word path, masking, and
retention of raw query slots before Merkle-opening deduplication. This is an
exact finite statement **conditional on independent uniform raw words**.
Adaptive commitment and PoW choices, correlation across transcript epochs,
and accepted-oracle agreement still require the BCS/ROM and IOP reduction.

## Build and migration

```sh
python3 src/frontends/s31/python/s31.py build \
  src/frontends/s31/examples/arithmetic/affine4_v1.s31.json \
  --lowering gate --channel-profile raw-blake2s-rejection-v1 \
  --out zig-out/s31/affine4-raw
```

The default build remains `legacy`. Deployments must distribute and pin the
new native verifier and key together; existing proof files cannot be silently
upgraded. The raw package omits recursive and fold artifacts and capabilities.

Source anchors: `src/frontends/s31/build.zig`,
`src/frontends/s31/runtime/native_verifier.zig`,
`src/frontends/s31/runtime/mvp_runtime.zig`, and the pinned engine's
`src/core/channel/blake2s.zig` and `src/core/vcs_lifted/channel_profile.zig`.
In the pinned engine, `Blake2sChannelGeneric(false)` supplies the raw channel;
`drawU32s` hashes with `Blake2sHasherGeneric(false)`, and `drawBaseFelts`
checks **all eight** raw words against `2p` before calling `M31.fromU64`.
`Blake2sMerkleChannelProfile` selects this channel when `m31_channel=false`
while both profiles name the same `Blake2sPlainMerkleHasher`.
