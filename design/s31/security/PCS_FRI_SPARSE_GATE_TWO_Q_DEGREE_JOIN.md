# Two distinct OOD points: the conditional degree join

The accepted sparse Gate proof has 61 source columns and 73 explicit OOD
claims. Twelve columns have **two distinct mask points**: shifted first, base
second. Each point also needs its Frobenius conjugate in the native quotient.
The selected verifier still FRI-tests one accumulated quotient. This note
states the algebra needed for a candidate that independently tests each
original and each point-specific own quotient. It does not assign the paper's
batch width `M` or proven security bits.

## Where a short column's claim is evaluated

The captured point in a claim is a raw point `Q_top` on the lifted log-17
circle. The prover computes `fold_count = 17 − h` for a source column of
extended log height `h` in
[`sampled_values.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_values.zig).
The coefficient plan's `foldCoefficientPoint` and barycentric plan's
`foldSamplePoint` in
[`sampled_coefficient_plans.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_coefficient_plans.zig)
both call `repeatedDoubleOnCircleQM31` with that count. Thus the source-height
interpolant is evaluated at

```text
Q_h = [2^(17−h)] Q_top

extended source height h    17       11       5
circle doublings             0        6       12
```

The Lean module models the exact native loop body
`(x,y) ↦ (2x²−1, 2xy)`. It proves that the circle equation is preserved and
that the Fourier coordinate of the projected point is
`z_h = z_top^(2^(17−h))`. This fixes the algebraic meaning of the 0/6/12
normalizations; it is not yet an operational proof of the native loop.

The [accepted claim capture](PCS_FRI_SPARSE_GATE_H3_ACCEPTED_ROWS.md) pins
all 73 raw point/value entries and the source-height row projection. It is
finite evidence. The full native coefficient evaluator and the barycentric
interpolant still need a semantic refinement to one mathematical circle
polynomial `f_h` on **every** row and at `Q_h`. In particular, the recorded
raw `Q_top` is not itself the low-height evaluation point.

Each projected `Q_h` must also pass its own nondegenerate conjugate-line
guard. [`complexConjugateLineCoeffs`](../../../deps/stwo-zig/src/core/constraints.zig)
returns `DegenerateLine` when its projected `y` equals its conjugate. A
successful guard at `Q_top` alone does not establish the guard after 6 or 12
doublings. The Lean claim certificate below explicitly requires the guard
and degree-two Fourier fact at **each projected point**. Fail-closed native
sampling and its distribution after conditioning remain open.

## Exact conditional source bounds

For the accepted blowup-two source roster, a native coefficient vector at
extended log height `h` has `2^(h−1)` trace coefficients. In the current
Laurent model its proposed radius is `n_h = 2^(h−2)`, and a conjugate two-point
line has radius one. A correct own quotient has radius at most `n_h−1`:

| Source height | Native trace coefficient count | Conditional original Laurent radius `n_h` | Own quotient radius | Whole-original uniqueness needs |
|---:|---:|---:|---:|---:|
| 17 | 65,536 | 32,768 | 32,767 | more than 65,536 distinct rows |
| 11 | 1,024 | 512 | 511 | more than 1,024 distinct rows |
| 5 | 16 | 8 | 7 | more than 16 distinct rows |

[`SparseP05TwoQDegree.lean`](../../../formal/s31/S31/Gadgets/PcsFri/SparseP05TwoQDegree.lean)
checks these numbers and proves the following coefficient-level statements.
The complete native circle FFT/basis-to-`InCircleBand n_h` proof is still
missing; the four-slot refinement does not establish the bound for 65,536,
1,024, or 16 arbitrary coefficients. The paper uses its own circle-code
filtration `L'_n`, so identifying that filtration with this Laurent bound is
another separate premise.

### Correct claims produce two own quotients

Let `f_h` be **one** source polynomial of radius `n_h`. For each distinct
projected point `Q_{h,j}` with valid conjugate-line certificate, let `I_j`
be its degree-one interpolation from the claimed value, and let `L_j` be the
line vanishing at that point and its Frobenius conjugate. If the claim is
correct, `f_h(Q_{h,j}) = I_j(Q_{h,j})`, then the Lean theorem constructs
separate polynomials `q_0,q_1`, each of radius at most `n_h−1`, with exact
coefficient identities

```text
f_h = I_0 + L_0 q_0 = I_1 + L_1 q_1.
```

The equality on the right is a cross-quotient consistency equation, not merely
two checked rows. For a small symbolic example, take `f=L_0 L_1` and both
interpolations zero. Then `q_0=L_1` and `q_1=L_0`; each quotient has its **own**
line and the reconstructed original is exactly the same polynomial. A
candidate verifier must establish this shared original from authenticated
oracles, rather than treating two copies with equal labels as automatically
equal.

### Separate point tests need one source oracle

The second Lean theorem allows the two point-specific tests to extract
different bounded originals `f_0` and `f_1`. Suppose they each agree with the
**same authenticated source function** on row sets `A_0,A_1` inside one
source domain `D`. If

```text
|D| + 2 n_h < |A_0| + |A_1|,
```

then their overlap has more than `2 n_h` distinct Fourier coordinates.
Laurent uniqueness forces `f_0=f_1`. For each point-specific own quotient,
another joint original/quotient row set of size greater than `2 n_h`, with
nonzero line denominators and the native row equation, forces its **whole
polynomial** relation. Evaluating the two identities at their respective
line roots forces both claimed OOD values on the one source polynomial.

This is a deterministic algebraic implication. The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf),
Section 4.4, Protocol 4 and Theorem 5, supplies a correlated-agreement
argument for **one** common `Q` and a single-point divisor. Section 4.5 says
its analysis extends to a conjugate two-point divisor but omits the details;
it does not describe a joint proof for two distinct mask points. Applying
two instances here requires a new adaptive joint IOP/BCS error composition
and custody proof that their originals are the same authenticated source.
The theorem assumes its row sets; it does not derive them from native FRI
acceptance or from the 70-query accepted proof.

The [conditional ensemble inventory](PCS_FRI_SPARSE_GATE_PAPER_ENSEMBLE.md)
therefore remains unchanged. A base single-Q list and a shifted single-Q
list need two-instance composition; a joint multi-Q list needs its own
theorem. The actual native-to-paper `M` remains unknown and P05 stays open.

## Reproduce

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.SparseP05TwoQDegree
```
