# Native PCS/FRI: published-bound audit

This note covers the S31 profile pinned to stwo-zig
`039dacb59980e1e871571958b396b2e29f93c0e5`. It does **not** assign a
whole-proof security level. It separates the native checks visible in source
from the hypotheses needed to apply a published STARK soundness theorem.

## What the verifier actually fixes

The selected mixed N1–N8 profile uses 26 FRI/PCS proof-of-work bits, log
blowup 1 (factor 2), 70 raw queries with replacement, a constant last-layer
polynomial, and fold step 1. The gate build also permits an explicitly
selected fold step 4. The existing [conditional error ledger](MIXED_N1_N8_CONDITIONAL_ERROR_LEDGER_2026-10-12.md)
identifies the source owners, the separate 20-bit interaction nonce, and the
terms still missing from a whole-proof bound.

The pinned `Blake2sM31MerkleChannel` hashes a 32-byte digest concatenated
with a 32-byte root for each root absorption. It resets the draw counter on
absorption. A draw hashes the digest, the little-endian 32-bit counter, and a
zero byte. The PCS verifier absorbs claimed OODS values before DEEP
randomness; FRI absorbs each layer root before drawing its folding challenge;
it absorbs the final polynomial and the verified PoW nonce before drawing
queries. The [source guard](../../../scripts/s31_formal_lib/pcs_fri_order.py)
checks these barriers against the pinned implementation. The
[Lean model](../../../formal/s31/S31/Gadgets/PcsFri/QueryAndTranscript.lean)
proves that fixed-state root and draw-counter *hash inputs* retain their
payloads, and that sorting/deduplicating or folding the query set cannot omit
a predicate for any raw sampled position. A separate
[ideal-query counting theorem](../../../formal/s31/S31/Gadgets/PcsFri/QuerySampling.lean)
shows that, under independent uniform sampling with replacement, the chance
that all `s` raw draws fall in a fixed consistency set of density `alpha` is
exactly `alpha^s`, even if draws repeat. These results do not prove hash
collision resistance, independent Fiat–Shamir randomness, or low-degree
testing. The BLAKE2s channel's 32-bit draw counter wraps; a full transcript
argument must also bound the number of draws below that wrap point.

The native M31 channel's ideal-oracle query distribution is not exactly
uniform: it reduces each 32-bit BLAKE2s output word modulo
`p=2^31-1` before the query sampler masks the low `k` bits. Residues
0 and 1 have three raw preimages, while the other residues have two. For
`k>=2`, query indices 0 and 1 each have one extra preimage relative to
uniform, the last index has two fewer, and the others have exactly the
uniform count. Thus any fixed set's one-draw probability exceeds its
uniform density by at most `2/2^32 = 2^-31`; at `k=1` the bound is
`2^-32`. The [exact finite distribution proof](../../../formal/s31/S31/Gadgets/PcsFri/M31MaskedQuery.lean)
derives every index preimage count, identifies the raw-word event with the
sum of its preimages, proves both bounds are attained, and bounds independent
ideal-word repetitions by `(alpha + 2^-31)^s` for `k>=2` or
`(alpha + 2^-32)^s` for `k=1`. Its
[source contract](../../../scripts/s31_formal_lib/pcs_fri_m31_query.py) guards
the native M31 reduction and query mask. This does not establish
independence for Fiat–Shamir draws or turn the native verifier into the
paper's interactive protocol.

The same Lean module gives a **conditional** finite-model union bound:
`bad acceptance ≤ Merkle-failure budget + Fiat–Shamir-failure budget + alpha^s`.
Its premises explicitly require native-to-IOP refinement, a fixed IOP
consistency set, and separate bounds on the first two failure events. None
of those premises is discharged for the native prover; the theorem makes the
missing interfaces visible without claiming an end-to-end security result.

The pinned engine update from PR #242 additionally rejects a proof whose
exported commitment vector differs from the roots committed into the PCS
verifier, and rejects extra zero-fold FRI layers before absorbing any FRI
root. These close local capture/round-shape gaps. They do not establish
Merkle binding, FRI proximity, or a whole-proof security bound.

The later pinned engine update from PR #243 adds native lifted-Merkle
rejection controls under the **same authenticated root**: changing an opened
row, one sibling, or the queried index is rejected; an accepted capture is
replayed independently to the root, and a failed capture leaves no partial
capture behind. Its query-projection test covers both smaller and larger tree
domains and the conjugate half-bit. The
[Lean Merkle opening model](../../../formal/s31/S31/Gadgets/PcsFri/MerkleOpening.lean)
reconstructs a full path using the verifier's low-bit child orientation and
right shift. It proves a local binding reduction: two accepted different rows
at one root and index imply either a collision of those rows' leaf hashes or
a parent-hash collision on child pairs **actually visited by those two
paths**. Given an accepted opening of a tree whose leaf row is the projected
committed-column row, the same theorem forces an accepted native row to equal
that row unless this witnessed collision event occurs. This is a conditional
symbolic theorem. It does not yet prove that the Zig multiproof decoder
reconstructs the model's full paths, that its leaf encoding matches the
modeled row order, that the committed tree has the modeled columns, or a
quantitative BLAKE2s collision bound.

The next engine pin from PR #244 rejects lifted-Merkle query indices outside
`[0,2^height)` before decoding. This prevents a query index `q + 2^height`
from replaying `q`'s low-bit path under the same root; its native test mutates
an accepted two-level query from `1` to `5` and requires rejection with no
published capture. The
[Lean compressed-capture model](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofCapture.lean)
now represents each paired-sibling or witness-consuming native layer chunk.
It proves that every successful modeled edge walk yields a full path that
reconstructs the checked root, has the declared depth, and reaches root index
zero under the native range condition. Composing this with the prior
witnessed-collision reduction identifies an opened row with the projected
committed-column row, conditional on the tree's committed-column origin and
absence of the *local* collision event. The
[pinned decoder source control](../../../scripts/s31_formal_lib/pcs_fri_capture.py)
and native tests check the implementation's branch, sibling, shift and
publication structure. The
[Lean deterministic decoder](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofDecoder.lean)
now proves, assuming a strictly sorted frontier, that a successful one-layer
decode covers every input node exactly, emits the modeled parents, consumes
the precise witness prefix, and gives each node a valid event in the modeled
path walk. Source mutation controls additionally pin sorting, deduplication,
chunk advancement, witness cursor advancement, and ancestor matching. A
[focused native adversarial test](../../../formal/s31/tests/pcs_fri_decoder_native.zig)
checks paired decoding, duplicate query capture, witness underflow and
overflow, a changed witness, and inconsistent duplicate rows against the
pinned engine. A
machine-checked semantics of Zig's sorting,
deduplication, witness cursor and capture-copy loops into the modeled chunk
events is **still missing**. No quantitative cryptographic or FRI bound
follows from this model alone.

The pinned engine's FRI capture additionally requires its raw query positions
to equal the verifier-owned transcript draw before copying them into the
published capture. A same-fold permutation or repeated position cannot
replace a sampled position while preserving a successful capture. The lifted
Merkle capture publishes a valid empty-tree result only after rejecting
nonempty query and witness data. These are native custody and shape checks;
they do not establish the Fiat–Shamir or PCS soundness reduction.

The [independent leaf encoding check](../../../scripts/s31_formal_lib/pcs_fri_leaf_encoding.py)
reconstructs 12 openings and three lifted roots at heights 3, 4, and 6 from
upstream Rust oracle values. It sorts columns by ascending log size with
original order for ties, projects every nontrivial column row using the
conjugate low bit, serializes canonical M31 words as little-endian u32, and
hashes the row with **plain BLAKE2s-256**. The S31
`Blake2sM31MerkleChannel` has an M31 Fiat–Shamir channel, but its Merkle hasher
is plain and unreduced: no `leaf` or `node` domain prefix is present in this
profile. The check rebuilds every parent from left and right child hashes
and independently replays a full path for each queried row. Production
source anchors and mutation controls cover the relevant prover and verifier
order, projection, serialization and hash branches. This closes a concrete
finite leaf-byte mismatch risk and binds the model's row order to the pinned
sources; it is not a Zig execution proof, a general committed-column-origin
proof, or a collision-resistance bound.

## Cross-domain query geometry

The [S-two whitepaper, §5.3](https://eprint.iacr.org/2026/532.pdf) says its
then-current regular Merkle layout opens points that are **not** consistent
under circle-group squaring. That caveat must not be applied automatically to
this pinned Zig engine. Its lifted prover leaves and PCS verifier both use
`prepareTreeQueryPositions` from `core/pcs/utils.zig`. For a query `q` on a
size-`2^k` canonical circle domain and a smaller tree of size `2^l`, the
mapping is

```text
q_l = ((q >> (k - l + 1)) << 1) + (q & 1).
```

The low bit selects the conjugate half of the circle domain; the other bits
are in FFT bit-reverse order. If `C_k(q)` denotes the resulting circle-group
index, the canonical-coset definitions imply
`C_l(q_l) = 2^(k-l) C_k(q) (mod 2^31)`. For example, at `k=5`, `l=3`,
`q=7` maps to `q_l=1`; four times the group index `503316480` is
`2013265920`, exactly the smaller-domain group index. The larger-tree branch
selects a preimage, so projecting its result back recovers the original
query. The [independent integer-index check](../../../scripts/s31_formal_lib/pcs_fri_projection.py)
enumerates 20,460 cases across both tree-height directions and checks the
pinned prover/verifier source mapping, including conjugate-bit preservation.
The [general Lean index theorem](../../../formal/s31/S31/Gadgets/PcsFri/CanonicalCircleFoldIndex.lean)
proves the smaller-domain equation for all `0≤k-l<k≤30` in the modeled
canonical circle group, without relying on that finite enumeration. Native
index-to-point arithmetic and authenticated opening semantics are still
separate refinement obligations.

FRI's circle-to-line step instead discards the conjugate bit: its query set
folds by right-shifting the raw index while its sparse evaluation reverses
the remaining bits before selecting the line-domain point. This is the
expected `P -> x(P)` projection. These finite geometry checks address one
specific whitepaper divergence; a theorem relating every lifted Merkle leaf,
FRI opening and cross-domain batch to the paper's interactive verifier is
still missing.

## Why `26 + 70 = 96` is not a theorem

The upstream [Stwo Cairo README](https://github.com/starkware-libs/stwo-cairo#security--soundness)
calls its 26-bit PoW, blowup-2, 70-query target **96 bits of conjectured
soundness**. The native `securityBits()` calculation is `pow_bits +
log_blowup_factor * n_queries`; it only calculates that heuristic.
Call sites that print or gate on `securityBits()` should label it a
**nominal work-plus-query score**, never a proven lower bound on security.

In [Circle STARKs, Appendix B, Theorem 6 and Remark 26](https://eprint.iacr.org/2024/278.pdf),
the proven Johnson-regime query term is `epsilon_Q = alpha^s`, with
`alpha = (1 + 1/(2m)) * sqrt(rho)`, `m >= 3`, and circle-code rate
`rho = (N+1)/|D|`. For blowup 2, `rho` is slightly **above** 1/2.
Consequently `alpha > 1/sqrt(2)` and 70 queries provide **less than 35
bits in this published query bound**. With `m=3` and negligible finite-domain
correction, the term is about `2^-19.43`. Even *optimistically* granting the
full 26 PoW bits as a multiplier of that error would yield fewer than 61
bits in the `m -> infinity` limit, or about 45.4 bits for `m=3`.
Such addition itself needs a random-oracle/adversary-budget proof; PoW bits
cannot simply be added to every error term.

The complete paper bound is stricter. Theorem 6 includes commitment/folding
error `epsilon_C` in addition to `alpha^s`. One leading upper-bound term from
Remark 26 is

```text
(L - 2/3) * (m + 1/2)^7 / (3 * (rho_minus)^(3/2)) * |D|^2 / |F|
```

where `L` is the batch width, `rho_minus = 1/blowup`, and this implementation
uses `|F| = (2^31-1)^4` for QM31 challenges. As a deliberately favorable
arithmetic illustration, take `N=512`, `L=1`, and `m=3`. This single term
is approximately `2^-93.0` for blowup 2, `2^-89.5` for blowup 4, and
`2^-86.0` for blowup 8. Actual S31 batch widths and the remaining terms
can make the paper's *upper bound* worse. These figures are not attacks or
estimates of real prover success; they demonstrate that increasing the query
count alone cannot certify a 96-bit **proven** bound from this theorem.

Appendix B, Theorem 7 adds AIR composition and OODS terms, including
`ell_plus * ((C-1)/|F| + d*(N+2)/(|F|+1-|D|))`; a valid substitution needs
the emitted constraint count `C`, degree `d`, list-size bound, and every
component's geometry. The [official Stwo whitepaper summary](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
also records a BCS/Fiat–Shamir bound of the form
`(T+R)*max_i epsilon_i + 3*(T^2+1)/2^lambda`, for a stated adversary hash
budget `T` and number of rounds `R`. The whitepaper's non-squaring-consistent
implementation caveat concerns its regular cross-domain Merkle layout; the
pinned Zig source uses the transposed-consistent map checked above. The other
protocol and cryptographic hypotheses still require an end-to-end reduction.

## What a conservative profile requires

Before advertising a proven security number, an implementation-specific
reduction must map the emitted AIR, DEEP quotients, lifted multi-height PCS,
Merkle opening layout, raw-query distribution, and Fiat–Shamir schedule to
the theorem's exact protocol. It must check the domain-size and degree
conditions for each program, include the lookup/interaction argument, and
choose an explicit adversary budget. Fold step 4 additionally needs a
separate reduction: one commitment/challenge is used across a group of
butterfly folds, so it is not automatically the paper's sequence of
independent single-fold challenges.

The [published-bound preflight](../../../scripts/release/pcs_fri_proven_preflight.py)
evaluates Theorem 6's Johnson query term with exact integer arithmetic,
checks basic domain and multiplicity preconditions, and encloses one leading
term of Remark 26's commitment-error **upper-bound expression** between two
exact rational values. Its default `N=512, B=2, m=3, L=1, s=70` is an
illustration, **not** an assertion that every native proof has that geometry.
It finds that 348 ungrinded raw queries would be needed to put the query term
alone below `2^-96` for those illustrative inputs. The leading Remark 26
envelope term already exceeds `2^-96` in that illustration; this only says
that particular published envelope cannot certify the target there. A smaller
actual error, another theorem, or another parameterization is not ruled out.
The preflight reports both the paper's uniform-query arithmetic and an
outward rational upper bound after the native M31 mask bias. Both require
348 queries in this example; neither certifies the native protocol.

```sh
python3 -B scripts/release/pcs_fri_proven_preflight.py
python3 -B scripts/release/pcs_fri_proven_preflight.py --require-proven
```

The second command **must exit nonzero**, including when a caller supplies
many queries: no native-to-paper protocol reduction or whole-proof bound is
installed. Its output always has `native_proven_security_bits: null` and
`proven_release_admissible: false`. It rejects fold step 4 because the
single-fold paper theorem does not apply to the native grouped schedule as
given. It does not account for proof-of-work bits, which require the
Fiat–Shamir adversary-budget theorem and the exact native nonce schedule.

For any proposed `N, C, d, L, m, T`, a future conservative certificate must
evaluate **all** published terms with justified arithmetic and reject a
profile if a theorem precondition fails. It may suggest more
queries and blowup, but the QM31 `|D|^2/|F|` term can then dominate. Larger
circuits or a high adversary budget may require a wider challenge field or
a different proved protocol. No fixed `pow=26, queries=70, blowup=2`
tuple can be certified for every S31 program by parameter arithmetic alone.

Reproduce the illustrative query and leading commitment-term arithmetic:

```sh
python3 - <<'PY'
from math import log2
p, N, m, L, s = 2**31-1, 512, 3, 1, 70
for blowup in (2, 4, 8):
    D = N*blowup
    rho = (N+1)/D
    alpha = (1+1/(2*m))*rho**0.5
    leading = (L-2/3)*(m+0.5)**7/(3*(1/blowup)**1.5)*D**2/p**4
    print(blowup, -s*log2(alpha), -log2(leading))
PY
```

The two printed columns are query-term bits and leading commitment-term
bits in an **idealized application of the paper's bound**, not a bound for
the S31 implementation. Exact program geometry and the missing protocol
reduction remain blockers.
