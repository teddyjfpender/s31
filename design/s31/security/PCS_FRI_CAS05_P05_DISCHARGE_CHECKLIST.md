# P05 discharge checklist for the paired CAS05 draft

**Status:** CAS05 is experimental. Its verifier is outside production PCS, and
there are **no proven native PCS/FRI security bits** or conservative release
profile. This checklist is an independent proof-interface review of
[stwo-zig PR #249 at `234ac67b2`](https://github.com/teddyjfpender/stwo-zig/tree/234ac67b2819e6b102e8d43da93a38a4a902075e).
It complements the [theorem bridge ledger](PCS_FRI_CAS05_THEOREM_BRIDGE.md)
and the [v0.1 blocker matrix](pcs-fri-v01-blockers.json); neither a source
guard nor a passing proof fixture discharges P05.

## 1. State the exact accepted relation

A complete CAS05 verifier call first matches an **independently supplied**
profile, source root, and ordered OOD claims. It replays the tagged transcript
on a staged channel and publishes that channel only after every check passes
([verifier lines 176–225](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/paired_sparse_cascade_experimental.zig#L176-L225)).
The [XDM04 verifier](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/transposed_merkle_sparse.zig#L177-L279)
authenticates two original-source rows at each height against one transposed
root. For each authenticated M31 word, the
[paired batch](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/transposed_paired_sparse.zig#L55-L80)
derives **that word's own two-point conjugate quotient**, then combines
`f₀, q₀, f₁, q₁, …` with successive powers of one `λ`. The verifier
[authenticates two line words per layer and checks every sampled fold and the
short terminal polynomial](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/paired_sparse_cascade_experimental.zig#L238-L325).
The [audit extractor](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/paired_sparse_relation_experimental.zig#L258-L371)
replays and records this **sampled** relation. Its returned rows are useful
evidence; they do not establish whole-oracle degree or a security bound.

**Discharge test:** give a semantic refinement from every accepting canonical
CAS05 byte wire, external statement, authenticated root and line opening, and
transcript state to one explicit ideal oracle relation. Keep proof-supplied
metadata distinct from the public statement throughout. The
[outer decoder](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/paired_sparse_cascade_wire.zig#L112-L227)
alone is only a shape and canonical-field check.

## 2. Prove the two-point theorem join

The [S-two whitepaper, Protocol 4 and Theorem 5](https://eprint.iacr.org/2026/532.pdf)
prove degree-corrected evaluation using both an original and a **single-point**
quotient. Section 4.5 says the analysis carries over to conjugate two-point
quotients, while omitting its details. That mathematical extension is still
different from proving that CAS05 implements it.

The native divisor is a **line in the circle algebra**. Its two roots do not
justify replacing the paper's circle degree condition with a degree-two
ordinary-polynomial condition. The
[ordinary-polynomial analogue](../../../formal/s31/S31/Gadgets/PcsFri/TwoPointDegreeCorrection.lean)
states its own limitation. The
[native Laurent model](../../../formal/s31/S31/Gadgets/PcsFri/NativeCircleQuotientRows.lean)
constructs a radius-`n−1` own quotient for a bounded **honest** source
polynomial under explicit field and OOD premises; it does not recover such a
polynomial from arbitrary accepted committed rows.
The [finite-domain Laurent uniqueness theorem](../../../formal/s31/S31/Gadgets/PcsFri/CircleLaurentUniqueness.lean)
now proves that an exact all-row own-quotient equation reconstructs a bounded
source word, and that more than `2n` distinct Fourier evaluations determine
an `L_n` polynomial. This supplies the coefficient model's exact uniqueness
step, but CAS05 authenticates sparse samples and still needs the correlated
agreement and query reduction.

**Discharge test:** prove the exact native circle-basis filtration, two-point
claim interpolation and row quotient identity, approximate joint agreement
for originals and own quotients, and the small-domain uniqueness premise for
every nonempty height. Then prove that deriving each batch oracle from the
precommitted source and OOD claims substitutes for Protocol 3's explicit
post-`λ` batch commitment. The sampled fold must refine the published
normalized recurrence: CAS05's height-`i` insertion has a `2⁻ⁱ` source
factor after normalizing its unhalved butterflies
([native relation and scope](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/design/pcs/SPARSE_CASCADE_EXPERIMENTAL.md)).
Apply Theorem 4 only after these oracle and degree joins are proved.

## 3. Prove the native query, OOD, and commitment games

The paper's two-point sampler is uniform on
`C(QM31) \ C(CM31)`, whose affine size is `q⁴−q²` for `q=2³¹−1`.
The paper's single-point Protocol 4 instead uses
`C(QM31) \ C(M31)`, size `q⁴−q−2`. CAS05 samples a rational-map seed and
rejects `y.c1=0` ([native draw](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/paired_sparse_cascade_experimental.zig#L76-L91));
its accepted image has size `A=(q²−1)²`. The
[Lean support arithmetic](../../../formal/s31/S31/Gadgets/PcsFri/OodAcceptedSupport.lean)
and [concrete circle count](../../../formal/s31/S31/Gadgets/PcsFri/ConcreteCircleCount.lean)
show that the modeled CM31 and QM31 circles have `q²−1` and `q⁴−1` points,
respectively; the complement of the embedded CM31 circle has `q⁴−q²` points.
Together with the already-proved guarded seed count, `q²−1` is the
cardinality difference between that complement and the accepted seeds.
The conditional uniform mass ratio
is `q²/(q²−1)`. Its `twoPointSupport` definition is not itself a formal
field-point counting theorem; the new count supplies that separate fact.
The [guarded image theorem](../../../formal/s31/S31/Gadgets/PcsFri/GuardedCircleImage.lean)
now proves that the modeled rational-map image is exactly the QM31 circle
points with nonzero upper `y` coefficient and lies inside the complement
of the embedded CM31 circle. The
[field-count bridge](../../../formal/s31/S31/Gadgets/PcsFri/OodGuardFieldCount.lean)
proves that the counted `acceptedGuard` predicate is exactly the concrete
QM31 field guard and that the modeled image has `(q²−1)²` points, leaving
exactly `q²−1` points in the two-point universe outside that image. The
transcript draw and installed binary are separate obligations.
The ratio transfers a
**fixed bad-set count only if** that count is first proved for the two-point
universe. It does not establish adaptive Fiat–Shamir sampling.

Raw queries are [low-bit masks of BLAKE2s words](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/queries.zig#L5-L28)
drawn after all roots and terminal coefficients. Repeats count as separate
draws, while lower-height projections can overlap. The
[Lean sparse-query model](../../../formal/s31/S31/Gadgets/PcsFri/SparseMultiHeightAgreement.lean)
proves a fixed-oracle joint event and shows why multiplying per-height miss
probabilities is unsound. It assumes ideal independent raw draws and a
correlated-agreement witness that CAS05 has not supplied.
The [fixed-oracle paired sparse batch theorem](../../../formal/s31/S31/Gadgets/PcsFri/PairedSparseBatchAgreement.lean)
now bounds the shared-`λ` collision exception by
`Σᵢ 2·columnsᵢ·mismatchedRowsᵢ` and combines its complement with the exact
adjacent-pair raw-query schedule, counting repeated ideal draws separately.
It requires a candidate original oracle fixed before `λ` and a lower bound
on source disagreements at some height; it does not derive either from a
false accepted CAS05 proof or from native FRI proximity.

**Discharge test:** prove XDM04 and line Merkle binding to fixed committed
oracles, exact circle/coset projection, the two-point OOD bad-set numerator
and guard-abort law, the adaptive masked query law, and a BCS/ROM reduction
for the actual shared Blake2s transcript and tree encodings. Count all
adversarial oracle work, the exact round schedule, and collision events;
CAS05 currently has no PoW stage
([transcript ledger](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/design/pcs/CAS05_BCS_ROM_JOIN.md)).

## 4. Admit only a measured, source-bound profile

The sparse verifier admits `k≤22`, `2≤H≤8`, and at most `16,384` raw queries,
subject to its wire and column bounds
([XDM04 profile](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/core/pcs/transposed_merkle_sparse.zig#L14-L41)).
The CAS05 host now invokes a separate
[`commitSparse` constructor](https://github.com/teddyjfpender/stwo-zig/blob/234ac67b2819e6b102e8d43da93a38a4a902075e/src/prover/pcs/transposed_cascade_experimental.zig).
It validates the XDM04 query shape but still materializes the full tree and
preflights a 192 MiB tree-plus-logical-source budget. The legacy XDM03
constructor retains `k≤16` and `queries·2ᴴ≤2¹⁶`. A native `k=17,H=2`
CAS05 proof verifies through the statement-bound wire, while `k=22,H=8`
with one source column per height exceeds the host budget. That `k=22`
verifier geometry leaves 8,192 terminal coefficients on 16,384 line-domain
rows; it is not yet a host proof or an admitted profile.

**Discharge test:** extract the actual installed S31 key's domain roster,
degree bounds, column widths, query count, and proof selector; prove its
prover and verifier match the admitted CAS05 format; then instantiate every
fold, batch, OOD, query, and BCS round error with explicit adversary budget
`T` and absolute or work-factor target. The
[capacity decision](PCS_FRI_CAS05_CONSERVATIVE_PROFILE_DECISION.md)
is paper-only arithmetic for one illustrative table: under its `T=2³²`
assumption, the quoted QM31 bound does not yield absolute 96 bits. It is
neither a native proof nor a universal lower bound. Until the full chain is
proved, the [v0.1 release gate](pcs-fri-v01-blockers.json) must retain
`native_proven_security_bits = null` and `proven_release_admissible = false`.
