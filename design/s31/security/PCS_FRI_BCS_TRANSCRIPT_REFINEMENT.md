# P07: the selected direct Gate transcript, byte by byte

This is a **scoped deterministic correspondence check** for the S31
`verifyDirectGateBound` path under the pinned `proving_5a7c5ed`
`Blake2sM31MerkleChannel`. It does not prove a random-oracle or BCS security
bound. The v0.1 proven-release gate remains closed.

## What the verifier does

`mix` replaces the 32-byte channel digest with a BLAKE2s-M31 hash of the old
digest followed by the supplied bytes, and resets the u32 draw counter to
zero. BLAKE2s-M31 means each little-endian 32-bit output word is reduced
modulo `p = 2^31 − 1`. A root mix hashes `digest || 32 root bytes`. A field
mix hashes `digest || four little-endian M31 limbs per QM31 value`. A `u64`
mix hashes `digest || little-endian u64`.

One draw hashes `digest || little-endian u32(counter) || 0x00`, then returns
eight reduced 32-bit words. A secure field draw rejects the *whole* block if
any word is at least `2p`, reduces the accepted words modulo `p`, and takes
the first four. A lookup-element pair takes both four-word halves of one
accepted block. The checked native increment aborts before u32 wrap.

For the direct Gate, the relevant event order is:

```text
profile tag + source digest + chip marker
  → channel salt → FRI config
  → fixed root → circuit identity → eight public outputs → main root
  → verify interaction PoW nonce → absorb that nonce
  → draw lookup z, alpha → absorb claimed interaction sum → interaction root
  → draw composition randomness → composition root → draw OODS seed
  → absorb sampled values → draw DEEP randomness
  → for each FRI layer: absorb its root → draw its folding alpha
  → absorb last-layer coefficients
  → verify FRI PoW nonce → absorb that nonce
  → draw 70 raw query positions (nine hash blocks)
```

The verifier checks both nonce predicates **against the digest before that
nonce is absorbed**. The FRI nonce therefore changes the query epoch; the
interaction nonce changes the lookup challenge. Invalid nonces exit before
the corresponding absorption and draw. The native verifier authenticates
and checks openings after query sampling; those checks are separate P04/P06
obligations.

The [M31 PoW predicate audit](PCS_FRI_POW_M31_PREDICATE.md) proves the exact
first-word raw preimage counts at both selected barriers: 4,097 favorable
32-bit words at 20 bits and 65 at 26 bits. The corresponding ideal direct
zero-bit counts are 4,096 and 64. This is a conditional one-try count and
gives no independent-grinding or soundness credit.

## A hand-sized transcript example

The [fixture](../../../formal/s31/tests/pcs_fri_bcs_transcript.json) uses an
all-zero source digest, no chip, fixed synthetic roots, one inner FRI layer,
and **8-bit fixture PoW** at each barrier so it runs quickly. Production
Gate settings are different; this example tests encodings and order.

| Event | Channel digest (first 8 hex digits) | Next draw counter |
| --- | --- | ---: |
| after main root, before interaction PoW | `44990d04` | 0 |
| after valid interaction nonce `153` | `d2c3d81f` | 0 |
| after drawing lookup `z, α` | `d2c3d81f` | 1 |
| after last FRI coefficients, before FRI PoW | `085c3a58` | 0 |
| after valid FRI nonce `124` | `693e8204` | 0 |
| after 70 raw queries | `693e8204` | 9 |

The lookup `z` is the four-limb field value
`(428100, 1961430125, 453493376, 2124077454)`. The first eight raw
query positions on a `2^21` domain are
`[389498, 1444040, 1759634, 1743664, 1896056, 1037969, 1141352,
619474]`. Query sampling masks the low 21 bits; it does not consume a secure
field draw. A changed nonce changes the digest and therefore the later
challenge bytes unless a hash collision occurs.

The [independent Python model](../../../scripts/s31_formal_lib/pcs_fri_bcs_transcript.py)
uses `hashlib.blake2s`, its own field reduction and its own transcript state
machine. The [native Zig replay](../../../formal/s31/tests/pcs_fri_bcs_transcript_native.zig)
checks both PoW predicates, every retained challenge, all 70 raw positions,
six digest/counter milestones, and the native channel's actual M31 encoding.
The [source audit](../../../scripts/tests/test_pcs_fri_bcs_transcript.py)
pins the direct Gate entrypoint, selected channel alias, profile bytes,
config, both PoW rejection branches, commitment/challenge order, root and
nonce encodings, last-layer absorption, query loop and counter behavior.
Hostile edits to these barriers must fail. It records the pinned engine
gitlink and hashes of the reviewed source files.

[`BcsTranscriptEpoch.lean`](../../../formal/s31/S31/Gadgets/PcsFri/BcsTranscriptEpoch.lean)
proves, for an uninterpreted hash, that the nine post-nonce draw *inputs* are
distinct and their counters cannot overflow a u32. The nine concrete
little-endian counter encodings are checked without a global injectivity
assumption. It also states that a successful modeled query epoch requires a
valid nonce. A query draw hashes 37 bytes: the 32-byte digest, four-byte
counter and one zero byte. Channel absorptions hash a 32-byte digest followed
by complete u32 words, so their input lengths are divisible by four; the two
PoW hash calls take 52 and 40 bytes. The Lean length proof therefore rules
out a query-input collision with those operation classes for **any** byte
contents. The native replay now independently rebuilds and hashes all nine
37-byte preimages, including the partial last block. The source audit pins
the 37-byte native buffer, digest/counter copies, and four-byte field limbs.
It says nothing about distinct hash outputs or whether a query input equals
an earlier challenge draw input after a digest collision.

Run the focused evidence from the S31 root:

```sh
bash formal/s31/tests/run_pcs_fri_bcs_transcript_native.sh
python3 -B -m scripts.s31_formal_lib.pcs_fri_bcs_transcript
```

## What remains before P07 closes

1. A checked correspondence from every selected native verifier path and
   Zig execution to this symbolic transcript, including failures, loops,
   integer representations and the actual package/profile dispatch.
2. A specified BCS/Fiat–Shamir theorem that matches this M31-reduced
   BLAKE2s channel, plain Merkle encoding, nonce schedule, and query law.
   The selected release target uses the paper's work-factor measure
   `ε(T)/T ≤ 2^-96` at `T=2^64` BLAKE2s queries; the native bound is still
   absent. Specify and bound the adversary's total hash work `T`, rounds `R`,
   output/collision parameter `lambda`, and the real effect of both grinding
   stages. Do not add 20 and 26 PoW bits to a soundness estimate by fiat.
   Each channel digest has at most `p^8 < 2^248` states after reduction,
   so `lambda = 256` cannot be inherited from raw BLAKE2s. Native root and
   field absorption lack operation tags; for example, a 32-byte root and two
   QM31 values of the same bytes form an identical next-hash input at the
   same digest. The fixed call schedule may still suffice, but the reduction
   must state and justify the required cross-role framing assumption.
3. Quantitative Merkle binding and BLAKE2s/ROM assumptions, including
   operation framing and cross-role hash-input collisions, joined to the
   independently reviewed FRI/PCS error terms.
4. A complete published-parameter soundness calculation. The sealed current
   `blowup=2, queries=70, FRI PoW=26` tuple already fails the target 96-bit
   Johnson-envelope necessary query arithmetic in the
   [conservative feasibility audit](PCS_FRI_GATE_CONSERVATIVE_FEASIBILITY.md).

The differential fixture proves equality on concrete inputs. The source
guard is syntactic. The Lean theorem is a hash-input fact. None is a
cryptographic reduction or a proof that v0.1 has 96-bit native soundness.
