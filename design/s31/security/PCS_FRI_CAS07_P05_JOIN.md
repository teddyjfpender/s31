# CAS07 sparse folds and the P05 two-point join

CAS07/XDM05 is a candidate in [stwo-zig PR #269](https://github.com/teddyjfpender/stwo-zig/pull/269), outside production PCS. The [Lean theorem](../../../formal/s31/S31/Gadgets/PcsFri/Cas07SparseP05Join.lean) establishes two algebraic steps needed to compare it with S-two Protocols 3–4. This page states their inputs so the results are not mistaken for a soundness proof.

## Sparse height: a worked fold

Let the largest circle domain have `2^6 = 64` rows, with four height positions and source column counts `[1, 0, 0, 1]`. A raw query `r=13` follows this path:

| Height `i` | Source rows opened `b_i(r), b_i(r)+1` | Projected circle row `b_i(r)+(r mod 2)` | Folded line row `r/2^(i+1)` | Source columns |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 12, 13 | 13 | 6 | 1 |
| 1 | 6, 7 | 7 | 3 | 0 |
| 2 | 2, 3 | 3 | 1 | 0 |
| 3 | 0, 1 | 1 | 0 | 1 |

Here `b_i(r) = 2 floor(r/2^(i+1))`. Both opened source rows are needed for the butterfly; the projected row is the one on the raw query's circle projection trace. The integer equations and `2^i` raw preimages per projected row are proved in `SparseCascadeQueries.lean`. CAS07's `verifyFolds` additionally computes the actual canonical circle point for each projected row and checks that it equals the previous point doubled at **every** height, including absent ones. Its bit-reversed row-to-point map and field operations still require a native-to-model refinement. A passing fixture alone is not a proof of query distribution or of the paper's full proximity event.

At height one, no source column exists. The own-quotient batch is exactly zero; the verifier still draws `alpha_1`, authenticates the preceding line pair and checks

```text
native_fold = previous_even + previous_odd
            + alpha_1 * (previous_even - previous_odd) / line_x.
```

For `previous_even=5`, `previous_odd=9`, `line_x=2`, and `alpha_1=7`, the fold is `14 + 7*(-4)/2 = 0` in any field of characteristic other than two. The published normalized butterfly uses half this value. Since the preceding native layer carries a factor `2^1`, the exact relation is

```text
native_fold = 2^(1+1) * normalizedPair(5/2, 9/2, 2, 7).
```

At height two, another challenge and line fold are still needed; removing an absent source height would change the transcript and domain sequence. At `H=1`, the first circle fold goes straight to the revealed terminal line polynomial, as proved separately in `Cas07H1Terminal.lean`.

## What joint agreement proves

At a **nonempty** height, suppose a bounded circle Laurent polynomial `p` agrees with authenticated originals and a bounded `q` agrees with each original's own two-point quotient on the **same** set `A` of distinct Fourier coordinates. The Lean model gives `p` radius `n`, `q` radius `n-1`, and the two-point interpolation polynomial radius one. If `|A| > 2n` and the native circle-line divisor is nonzero at those rows, then the row quotient law and finite Laurent uniqueness imply the polynomial identity

```text
p = interpolation + native_line * q.
```

If the native line vanishes at the claimed out-of-domain point, evaluating this identity there gives `p(Q) = interpolation(Q)`, the claimed value. This is the exact algebraic conclusion needed from a common agreement set. The theorem takes the common set, both bounded polynomials, and the row law as explicit premises. The finite-set overlap lemma says a sufficient numerical condition for separately supplied good-row sets `A_f` and `A_q` inside domain `D` is `|A_f| + |A_q| > |D| + 2n`; it does not manufacture those sets from a FRI proof.

The published [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf), Protocol 4 and Theorem 5, uses originals and own **single-point** quotients. Its Section 4.5 discusses the conjugate two-point variant but does not supply the full extension proof. The Laurent lemma supplies a conditional uniqueness step for the native two-point line. It does not establish that the native coefficient radius is the paper's circle-code degree, nor derive the paper's small-height threshold for this variant.

### Gate's smallest occupied height

The candidate Gate roster has top log size `k=20`, occupied heights `0,2,4,6,11,12,16`, and blowup log `beta=2`. Height `i=16` has a `2^(20-16)=16`-row **source evaluation domain** with 193 columns. The host's `validateSourceDegree` allows only `2^(4-2)=4` ordered source coefficients per column. The existing `CanonicalCircleLaurentRows.fourBlock_in_band_two` proves that the first four native circle coefficient slots map into the broader Laurent radius `n=2` model. The strict uniqueness premise here is therefore `|A| > 2n = 4`, or at least five distinct Fourier rows out of 16. This is numerically attainable. The [Gate 16-row audit](PCS_FRI_GATE16_FOURIER_ROWS.md) proves index and finite modeled coordinate uniqueness and tests the exact pinned native row points; a formal native execution refinement and the **same** at least five rows satisfying both original and quotient agreement remain open. The theorem's `n` is a Laurent support radius, not the native log size `4`, the four-coefficient count, or the paper's `n=log₂(N)` variable.

The [four-block own-quotient audit](PCS_FRI_GATE_FOUR_BLOCK_OWN_QUOTIENT.md) now proves that a correct two-point claim for those four coefficients yields a radius-one quotient, with exact unscaled and native-scaled equations on every base Fourier row. A finite native witness shows that this radius-one space cannot simply be replaced by the first two circle-basis slots `{1,y}`. The source-row commitment and paper-filtration joins therefore remain open.

The distinction between separate and common agreement is concrete. Let original-good rows be `0..8` and quotient-good rows be `7..15`. Each has nine of the 16 rows, a strict majority, but their intersection is only `{7,8}`. Its size two is below the required five. `gate_separate_majorities_insufficient` checks this counterexample in Lean. Even if individual proximity estimates gave those two majorities, the algebraic uniqueness lemma would not fire; the missing cross-domain correlated-agreement reduction must supply a stronger common-set statement. The paper's own small-height condition must also be rederived for the native two-point circle filtration before using any numerical soundness profile.

### Source-path audit of the draft

This local comparison reviewed draft stwo-zig commit `859409aa1e00a71a21a0f240b7f9f5c5a64fd3f8`:

| Native path | Checked operation | Formal boundary |
| --- | --- | --- |
| `transposed_merkle_sparse_heights_experimental.zig:55` | `pairBase(raw,i) = (raw >> (i+1)) << 1` | Same integer path as `SparseCascadeQueries.pairBase` |
| `paired_sparse_cascade_heights_experimental.zig:293` | Starts from bit-reversed canonical source point; doubles once for **every** later height; rejects if it differs from the canonical `pairBase | (raw & 1)` point | Exact squaring-consistent path is checked during accepted native execution, conditional on field/canonical-domain semantics; it is not a sampling theorem |
| `paired_sparse_cascade_heights_experimental.zig:193` | Draws one `alpha_i` per height, even when the column count is zero | Empty heights remain fold rounds |
| `transposed_paired_sparse_heights_experimental.zig:47` | Empty claims yield an all-zero paired answer; nonempty claims use consecutive shared batch powers for `(original, own quotient)` | `absent_batch_zero`, `native_batch_eq_protocol3` |
| `paired_sparse_cascade_heights_experimental.zig:303` | Checks every sampled fold against authenticated next-line words or the terminal polynomial | `absent_height_normalized_line_fold` covers only local field algebra; authenticated oracle and statistical reduction are open |

No native proven security bits follow from these source checks or finite tests.

## Remaining P05 discharge

1. Tie every source and line row accepted by Zig to one fixed authenticated oracle and the exact Lean row formulas, including empty XDM05 hash-upper levels, bit-reversed coordinates, inverse arithmetic, and the H=1 terminal evaluator.
2. Refine the native two-point quotient coefficient space to the paper's circle-code filtration. Derive its small-height uniqueness threshold and prove cross-domain correlated agreement yields the common set above for each nonempty height.
3. Refine the actual CAS07 projected raw queries, terminal and transcript order to the paper's interactive protocol, including challenge independence and native query-event implication. The verifier's point-doubling check establishes a local geometry condition only.
4. Prove the exact Blake2s/Merkle BCS/ROM game and instantiate a conservative `epsilon(T)/T <= 2^-96` bound for a declared hash-query budget `T`, with the trusted S31 key, AIR roster, and claims bound inside production admission.

The v0.1 blocker matrix therefore continues to record `native_proven_security_bits = null` and `proven_release_admissible = false`.
