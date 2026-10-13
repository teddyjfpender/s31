# P05 paired PCS migration: source-pinned engineering map

**Status:** design and exact draft-source diagnostic, not a production protocol
or soundness certificate. S31 production still pins stwo-zig commit
`59e1f115250b8af01712b9bf3d71616e53094964`, whose PCS feeds only a DEEP
quotient word to FRI. The experimental [stwo-zig PR #249](https://github.com/teddyjfpender/stwo-zig/pull/249)
has a separate original-plus-own-quotient path. This note reviews its commit
`234ac67b2819e6b102e8d43da93a38a4a902075e`, which includes canonical
in-memory value checks and the bounded CAS05 sparse host path from
[stwo-zig PR #264](https://github.com/teddyjfpender/stwo-zig/pull/264). A changed
draft needs a new source review. Neither path currently supplies proven native
security bits.

The [S-two whitepaper theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
states that degree-corrected batch evaluation tests **both** the original
words and their own OOD quotient words, across the multi-domain FRI cascade.
The S31 [P05 gap](PCS_FRI_DEGREE_CORRECTION_GAP.md) and [native witness](PCS_FRI_NATIVE_DEGREE_WITNESS.md)
show why a quotient-only FRI check cannot simply inherit that theorem.

## The smallest protocol delta

One versioned production PCS mode must carry the following complete relation
from prover to verifier. This is a protocol change, not a new setting for the
old `CommitmentSchemeProof.fri_proof`:

1. **Trust the profile externally.** The verification key selects the paired
   proof version, source domains and column counts, blowup, FRI schedule,
   query count, statement roots and public OOD claims. Reject a proof's mode
   or geometry before consuming any proof-supplied transcript bytes.
2. **Commit sources before challenges.** The prover commits every original
   column at its own canonical circle height. One authenticated transposed
   source root covers all heights. Bind the profile and root, then draw the OOD
   point, bind claims, and draw one shared batch challenge `λ`.
3. **Pair each column with its own quotient.** At height `i`, for every
   original `f_(i,j)` with claim `v_(i,j)`, derive the native two-point
   conjugate quotient `q_(i,j)` from the same committed source word. Feed
   `f_(i,j)` and `q_(i,j)` into the height batch in the exact order
   `f₀ + λq₀ + λ²f₁ + λ³q₁ + …`; reset powers only at the next height while
   keeping the same `λ`. Do not accept separately supplied quotient openings.
4. **Run one multi-height FRI on that extended ensemble.** Insert each height
   batch at its matching fold, commit intermediate line roots, reveal a
   bounded terminal polynomial, then derive sampled raw queries. The verifier
   authenticates original source pairs and line pairs at every queried
   projection, recomputes each quotient, checks every fold and the terminal,
   and publishes transcript state only on full success.
5. **Use an explicit new wire and transcript version.** The reviewed draft
   currently uses outer magic `S31CAS05`, outer version 6 with `S31CAS06`
   transcript tags, and nested `S31XDM04` sparse source openings. Production
   must freeze a version after its final layout and security review; existing
   quotient-only proofs must never be silently reinterpreted as paired ones.

The draft already implements much of this in
`src/prover/pcs/paired_sparse_cascade_experimental.zig`,
`src/core/pcs/paired_sparse_cascade_experimental.zig`,
`src/core/pcs/transposed_paired_sparse.zig`, and
`src/core/pcs/paired_sparse_cascade_wire.zig`. Its host prover still uses
`transposed_cascade_experimental.zig` and its `commitSparse` constructor. It
uses the XDM04 sparse profile, but still materializes the full Merkle tree;
the legacy XDM03 constructor remains separately capped at `k≤16`.
Production `src/prover/pcs/scheme.zig` and `src/core/pcs/verifier.zig` remain
on the old quotient-only path. Copying a batch formula into either production
file without changing the proof format, source authentication, fold schedule,
and verifier dispatch would leave P05 open.

## Exact reviewed profile geometry

Run the [source-pinned checker](../../../scripts/release/pcs_fri_cas05_source_profile.py)
with a local stwo-zig Git repository containing the reviewed draft commit:

```sh
python3 -B scripts/release/pcs_fri_cas05_source_profile.py \
  /path/to/stwo-zig --largest-log-size 22 --height-count 8 \
  --log-blowup 1 --queries 232 --columns 1,1,1,1,1,1,1,1 \
  --theta 16383/65536
```

The checker requires the exact reviewed draft ref and seven source-file
SHA-256 hashes. It rejects changed source or profile shapes. It reports
`k=22`, `B=2`, eight heights, source domains `2²²` through `2¹⁵`, a
`2¹⁴`-row terminal domain with `2¹³` QM31 coefficient words, and paper
Protocol-3 indices `n=21`, `r=7` **if** a refinement is proved. The
candidate source code dimensions satisfy the **single-point Protocol-4**
numeric small-table inequality at `θ=16383/65536`; these are not an
authenticated S31 AIR table roster, and the inequality has **not** been
rederived for CAS05's conjugate two-point line in the circle algebra. Its
ordinary-polynomial degree-two analogue does not establish the native
circle-basis threshold.

The OOD sample universe also differs. Protocol 4's single-point set is
`C(QM31) \ C(M31)`, with `q⁴−q−2` points. The whitepaper's Section 4.5
two-point discussion instead excludes the quadratic subfield circle,
`C(QM31) \ C(CM31)`, with `q⁴−q²` points. For an ideal uniform seed, CAS05's
`y.c1 ≠ 0` guard has `(q²−1)²` accepted images, a strict subset smaller by
`q²−1`; the support-size ratio is exactly `q²/(q²−1)`. The checker reports
these counts separately. They do not prove a bad-set bound for the two-point
quotient or an adaptive Fiat–Shamir sampling law.

The XDM04 sparse verifier's visible caps admit this shape. CAS05's host now
preflights the same sparse query shape, but limits the full Merkle tree plus
logical borrowed source words to **192 MiB** before allocation. At
`k=22,H=8,s=232` with one column per height, its estimate is **301,858,784
bytes**, so the host rejects that example. The legacy XDM03 path still has
the distinct `k≤16` and `s·2^H≤2¹⁶` caps. The native `k=17,H=2,B=2,s=3`
CAS05 fixture passes the new host preflight at **9,175,008 bytes**, produces
a **266,584-byte** proof and verifies through the canonical wire; the focused
test process measured **38,453,248 bytes** peak RSS. The preflight excludes
FRI working arrays and proof buffers, and this small fixture is not a
scalability benchmark. A practical `k=22` profile still needs a scalable
host source commitment/prover and new measurements. The tool reports no
native `R`, `T`, theorem admission, or security bits; `--require-proven`
always exits nonzero.

The [field-capacity decision](PCS_FRI_CAS05_CONSERVATIVE_PROFILE_DECISION.md)
adds another constraint: for its illustrative `N=2²⁰`, `T=2³²`, zero-grinding
**single-point paper** arithmetic, QM31 can meet a 96-bit *work-factor* expression with 232
ideal queries, but the same quoted bound cannot meet an **absolute** 96-bit
target at that adversary budget. A hypothetical larger even-degree challenge
field clears that particular nonquery expression, but no such native CAS05
field/protocol exists. The security target, field, and threat budget must be
fixed before admitting any production profile; these arithmetic examples do
not establish soundness for the draft, and their OOD term requires a fresh
two-point derivation before it can inform CAS05's bound.

## Production and S31 pin migration sequence

1. In stwo-zig, freeze the paired proof layout and transcript at a reviewed
   commit. Add a trusted-key-selected proof-mode dispatch into the production
   prover and verifier. Reject old/new mode confusion and malformed bytes
   before transcript replay. Ensure the paired verifier's external statement
   contains all roots and claims it uses.
2. Replace the bounded full-tree CAS05 host source path with a scalable
   construction of the same authenticated transposed source root and XDM04
   sparse openings.
   Benchmark the actual target `k,H,s,columns`; do not infer proof speed from
   small fixtures. Keep the verifier's sparse memory bounds and full
   failure-atomic behavior.
3. Test native honest proofs and adversarial controls through the **new
   production dispatch**, not only the experimental helper. Require multiple
   heights, columns and blowups; overdegree source rejection; changed
   authenticated original values, OOD claims, roots, line words and terminal;
   repeated/overlapping raw queries; wrong external statements; old/new
   version confusion; noncanonical bytes; and transcript rollback on every
   late failure. Compare all sampled paired words and folds against an
   independent scalar implementation. The draft's
   `paired_fri_test.zig` and `paired_fri_relation_bridge_test.zig` are the
   starting tests, not proof of the final dispatch.
4. Merge the reviewed stwo-zig PR, update S31's `deps/stwo-zig` gitlink,
   rebuild the complete S31 source bundle, and pin the installed prover,
   verifier, key and compiler identities. Extend S31 package verification so
   the trusted key selects the paired mode and binds its source roster and
   public statement. Re-run the S31 supported-profile audit against that
   exact binary. Refresh P05 source hashes only after an independent semantic
   review; keep the blocker and release gate closed during migration.
5. Establish the theorem join for the final binary: all original and own
   quotient polynomial degree spaces; the native **conjugate two-point line**
   in the circle algebra versus Protocol 4's single-point zeroifier; its
   exact circle-basis filtration, a fresh derivation of Eq. 80's small-domain
   uniqueness threshold, and substitution of the
   derived batch for a committed oracle; cross-domain correlated agreement;
   normalized folding/insertion and terminal space; actual AIR table roster
   and small-table condition; query distribution including duplicates;
   guarded OOD support; concrete Merkle/BLAKE2s binding and adaptive
   Fiat–Shamir/BCS reduction; exact `R,T` and every error term. Only then can
   a conservative profile and a security-bit claim be considered.

The existing [theorem correspondence ledger](PCS_FRI_CAS05_THEOREM_BRIDGE.md)
itemizes those proof obligations. The source-pinned tool is a regression
boundary around one draft revision, not their discharge. The current
[`TwoPointDegreeCorrection.lean`](../../../formal/s31/S31/Gadgets/PcsFri/TwoPointDegreeCorrection.lean)
is an ordinary-polynomial analogue, not a circle-code theorem. The
[`NativeCircleQuotientRows.lean`](../../../formal/s31/S31/Gadgets/PcsFri/NativeCircleQuotientRows.lean)
Laurent construction gives a conditional honest quotient; it does not turn
an accepted, authenticated CAS05 oracle into a polynomial in the required
degree space.
