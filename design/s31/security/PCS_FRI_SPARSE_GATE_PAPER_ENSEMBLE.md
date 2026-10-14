# The accepted sparse Gate roster versus the paper's FRI batch width

This note derives **function occupancy**, not a security parameter. The
[machine-readable word roster](evidence/sparse-gate-p05-paper-ensemble-2026-10-14.json)
is generated from one verifier-accepted sparse Gate proof. It names every
candidate original and own-quotient word by its source root, column, and OOD
claim. The selected verifier still runs its legacy accumulated quotient FRI;
it does not commit to or independently test these words. Its actual
native-to-paper batch width `M` is **unknown**.

## What the published protocols count

The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf), Section 4.2,
pp. 30–31, Eq. (66), gives Protocol 3 a batch of `M_i` functions on each
domain `D_i`. It pads smaller batches with zero words to the common width
`M = max_i M_i`, then uses one random `λ` across domains. Theorem 4 on p. 33
uses this **padded function width**, not the number of physical columns, in
its batching error term `(M−1)·…·|D₀|/|F|`.

Section 4.4, p. 35, Eq. (77), gives the degree-corrected Protocol 4 **one
common OOD point `Q`**. For each input function `f`, it submits both `f` and
its own single-point quotient `(f−v)/v_Q` to Protocol 3. The text immediately
before Protocol 4 says the extension to multiple query points is left to the
reader. Its Theorem 5 on pp. 35–36 transfers Protocol 3's bound under the
stated small-domain condition, provided this extended ensemble is actually
low-degree tested.

Section 4.5, p. 37, discusses replacing the single-point divisor with the
conjugate two-point divisor at `Q` and its Frobenius conjugate. It says the
soundness analysis carries over, while omitting the construction details and
requiring `Q ∉ C(CM31)` so the two conjugate points remain distinct. This
addresses the *two conjugate zeros of one quotient*. The accepted sparse
roster also has **two distinct OOD mask points** across claims; that is a
separate multiple-`Q` question. Section 4.5 additionally says its current
non-squaring-consistent circle-domain sampling lacks a full list-decoding
regime proof in the writeup.

## Exact accepted claims and conditional word lists

The [accepted geometry](evidence/sparse-gate-p05-accepted-geometry-2026-10-14.json)
pins key SHA-256 `7d4cdaab…16dccfc7`, proof SHA-256
`04eaca23…8e39`, and the full 73-claim map SHA-256
`d0dfd3b3…b99e26ed5f5`. The checked-in generator verifies each full digest,
the ordered 61 source references, and the exact QM31 point limbs. Every
source column has one claim at the base OOD point; twelve interaction
columns also have one claim at a common shifted point. The two points are
distinct. Per extended source height 17/11/5 there are 14/28/19 base claims
and 4/4/4 shifted claims.

The captured coordinate in every claim is the **raw lifted** point
`Q_top`, even for a short column. The prover evaluates a column of extended
height `h` at `Q_h = [2^(17−h)]Q_top`, because its PCS sampled-value path
sets `fold_count = 17−h` and repeatedly doubles the raw point before both
coefficient and barycentric evaluation. Thus the accepted claim value at
heights 17/11/5 belongs to a source interpolant at `Q_h` after 0/6/12
doublings. It is not a claim that the source interpolant evaluated at the
unchanged raw `Q_top` has the same value. The prior [accepted-row fixture](PCS_FRI_SPARSE_GATE_H3_ACCEPTED_ROWS.md)
checks the lifted/source-row projection on the one authenticated row. The
paper's Eq. (77) writes one `Q` for its per-domain polynomial evaluations;
relating that `Q` to native `Q_h` through lifted functions requires a
degree/domain refinement. The base and shifted raw points each project to
one point per active height; they are still two OOD masks, not six separately
sampled random challenges.

| Candidate occupancy, if mapped to paper domain batches | Height 17 | Height 11 | Height 5 | Conditional padded width |
|---|---:|---:|---:|---:|
| One single-`Q` Protocol 4 instance for the 61 base claims: one original and one quotient per claim | 28 | 56 | 38 | 56 |
| Another single-`Q` instance for the 12 shifted claims | 8 | 8 | 8 | 8 |
| One *joint multi-`Q`* instance with a separate original occurrence and own quotient for every one of the 73 claims | 36 | 64 | 46 | 64 |
| One *joint multi-`Q`* instance sharing each of 61 originals across its claims, with 73 own quotients | 32 | 60 | 42 | 60 |

The first two rows are **different Protocol 3/4 instances**. Their widths
cannot be collapsed into one soundness bound by taking `max(56,8)`; a joint
composition must bind the same source words in both instances and account for
two correlated OOD points, added challenges, rounds, query work, and errors.
The third row is the literal per-claim pair occupancy for a hypothetical
multi-`Q` extension. Four extra original *occurrences* per height explain why
its widths exceed the shared-original row. Equal source identity does not
make those occurrences free in Eq. (66). The fourth row requires a distinct
deduplication theorem. Neither joint row instantiates the published
single-`Q` Protocol 4 as written.

Native PCS also inserts one periodicity relation sample before the two
explicit OOD samples for each of the twelve two-sample columns. If a future
proof needs each as an **additional independent tested function**, the joint
per-claim occupancy becomes 40/68/50; the shared-original occupancy becomes
36/64/46. These are another conditional count, not a reason to equate the
old candidate width 64 with the literal per-claim pair width 64. Their word
identities differ.

Raw **contribution count is not distinct function count**. The source-height
period generator doubled `h` times is the identity, so in a height-local
`friAnswers(lifting_log_size=h, column_log_size=h)` calculation all twelve
periodicity points equal sample 1's point and reuse its claimed value. Even
in legacy lifted log 17, the four height-17 periodicity points duplicate
sample 1; the height-11 and height-5 shifts are nontrivial there. The native
[accepted-row fixture](../../../formal/s31/tests/pcs_fri_p05_sparse_h3_accepted_rows_native.zig)
checks both statements on the accepted roster. A future scheme could combine
some equal quotient *values*, but changing two separate `λ` powers into one
coefficient changes Protocol 3's challenge polynomial; no such compression
theorem is claimed here.

The **selected legacy** `friAnswers` path expands 73 explicit claims plus 12
periodicity terms into **85 weighted quotient contributions** and FRI-tests
their *single accumulated answer*. It does not expose 85 independent
degree-tested functions. The experimental H3 insertion instead lists 61
originals once with proposed own quotients. Its words and coefficient
schedule are neither the legacy accumulator nor Eq. (77)'s literal pair per
claim. Any theorem mapping must name which of these three objects it uses.

### One column in the list

Interaction root 2, column 20 has accepted claims 57 and 58 at height 17.
Claim 57 uses the shifted point; claim 58 uses the base point. In the joint
per-claim layout its ordered words are

```text
(original root 2 / column 20 for claim 57, own quotient for claim 57)
(original root 2 / column 20 for claim 58, own quotient for claim 58)
```

The same original source function occupies two list entries. In the
shared-original layout it occupies one entry followed by two quotient
entries. The [accepted-row hand calculation](PCS_FRI_SPARSE_GATE_H3_ACCEPTED_ROWS.md)
shows the exact two quotient values from one authenticated source row.

## Native anchors and outstanding join

- [`native_verifier.zig`](../../../src/frontends/s31/runtime/native_verifier.zig)
  `SparseP05Shape` records the verifier-owned source-root/column/height and
  OOD point/value roster only after ordinary proof admission. The
  `inspect-p05` JSON exports that captured order.
- [`samples.zig`](../../../deps/stwo-zig/src/core/pcs/quotients/samples.zig)
  `buildColumnSampleBatchesFromParallelInputs` inserts the periodicity point
  from sample 1 and the source-height period step *before* two explicit
  samples; this is the origin of the twelve extra contributions.
- [`fri_answers.zig`](../../../deps/stwo-zig/src/core/pcs/quotients/fri_answers.zig)
  consumes those weighted samples in the one legacy quotient answer.
- [`sampled_values.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_values.zig)
  computes `lifting_log_size − column.log_size` for every sampled-value
  evaluation path. [`sampled_coefficient_plans.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_coefficient_plans.zig)
  applies that many circle doublings before coefficient or barycentric
  evaluation; this is why raw captured `Q_top` and effective `Q_h` differ.
- [`p05_own_quotient_rows.zig`](../../../formal/s31/tests/lib/p05_own_quotient_rows.zig)
  `ownQuotientAt` uses native `complexConjugateLineCoeffs` and the exact
  two-point determinant. The accepted-row fixture checks all 73 corresponding
  native quotient calculations, but only on one authenticated row.

The native source domains have extended logs **17/11/5**. The conditional
paper parameter ledger starts at `D₀=N·B²=2¹⁸` for this key (`N=2¹⁶`,
`B=2`), so the height/domain and degree map needs a leading-domain and
composition proof. The four source roots have different challenge epochs.
The new word lists do not supply whole-oracle quotient commitments, a common
agreement set, paper-consistent cross-domain folding, or a BCS reduction.
They also do not establish whether periodicity words belong in the paper
ensemble. Consequently **none** of the conditional maxima above is assigned
to `native_to_paper_batch_width_M`, and no security bits or release admission
follow from the arithmetic.

## Reproduce

```sh
python3 scripts/release/pcs_fri_sparse_p05_paper_ensemble.py --check
python3 -m unittest scripts.tests.test_pcs_fri_sparse_p05_paper_ensemble
cd formal/s31 && lake build S31.Gadgets.PcsFri.SparseP05PaperEnsemble
```
