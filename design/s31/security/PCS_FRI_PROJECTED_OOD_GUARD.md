# Projected OOD guard for mixed-height PCS

The native verifier samples a QM31 circle point `Q` from a transcript seed.
For the two-point quotient, a line through `Q` and its CM31 conjugate is
defined only when `Q.y.c1 != 0`. The raw point satisfying that predicate does
**not** imply that every lower-height sample point satisfies it.

For a source column of extended height `h` under lifting height 17, the
sampled-value prover evaluates at `Q_h = [2^(17-h)]Q`. The sparse Gate roster
has heights 17, 11 and 5, so its fold counts are 0, 6 and 12. The native
quotient verifier uses the already projected `Q_h` in
`complexConjugateLineCoeffs` and returns `DegenerateLine` when its upper
`y` coordinate vanishes.

## Concrete witness

Let `q = 2^31-1`, `G = SECURE_FIELD_CIRCLE_GEN`, and
`Q = [(q²+1)/2]G`. The checked native test establishes all of these claims
for the actual field implementation:

1. `Q` lies on the QM31 circle, `Q.x.c0 = Q.y.c0 = 0`, and `Q.y.c1 != 0`.
2. `t = Q.y / (1+Q.x)` is defined, and the verifier's checked rational map
   sends `t` back to `Q`. The witness is therefore in the native seed image.
3. `[2]Q`, `[2^6]Q` and `[2^12]Q` have conjugate-fixed `y` coordinates.
   `complexConjugateLineCoeffs` rejects them with `DegenerateLine`.
4. The actual `friAnswers` quotient path rejects the height-11 projected
   point with `DegenerateLine` before producing a quotient answer.

The [Lean lemma](../../../formal/s31/S31/Gadgets/PcsFri/ProjectedOodGuard.lean)
proves the algebraic reason for the first doubling: for purely upper `x`
and `y`, `(2*x*y).c1 = 0`. The circle doubling formula has `2*x*y` as its
new `y` coordinate. Lean also checks `(q²+1) mod 4 = 2`; this arithmetic does
not substitute for a formal classification of the full circle group.

## Conservative support count

Write `Q=q²`. The modeled QM31 circle has `Q²−1` points. Its raw successful
set has `(Q−1)²` points, so the conjugate-fixed-`y` target set has exactly
`2(Q−1)` points. This last equality is [proved from the set complement in
Lean](../../../formal/s31/S31/Gadgets/PcsFri/ProjectedOodTargetCount.lean).

The [circle power encoding](../../../formal/s31/S31/Gadgets/PcsFri/CirclePowerEncoding.lean)
maps a point `(x,y)` injectively to `x+i·y`, where `i²=−1` in QM31. Doubling
becomes squaring, and `k` doublings become powering by `2^k`. A degree-`2^k`
power equation has at most `2^k` solutions. Lean therefore bounds the
unshifted h11 bad preimage by `2⁶·2(Q−1)` and the unshifted h5 bad preimage
by `2¹²·2(Q−1)`. Their union leaves at least

```text
(Q−1)² − (2⁶ + 2¹²)·2(Q−1)
```

raw-admissible points; Lean proves this quantity is positive. The broader
[union-bound interface](../../../formal/s31/S31/Gadgets/PcsFri/ProjectedOodSupportBound.lean)
handles four shifted h17 claims, 32 h11 claims, and 23 h5 claims given
their stated fiber caps. The extra conditioning multiplier after the raw
guard for an ideal uniform circle draw is below `1+2⁻⁴⁰`. The actual
shifted point map, selected native evaluator, and Fiat–Shamir seed law
still need their own refinement and probability argument.

The [modeled translation theorem](../../../formal/s31/S31/Gadgets/PcsFri/ProjectedOodTargetCount.lean)
now discharges those caps for **any fixed circle shifts**: circle addition
multiplies the injective `x+i·y` encoding by a nonzero field element, so it
cannot increase a doubling fiber. It proves a positive survivor count for
all 4+32+23 shifted-claim slots at once. Matching each slot and its shift to
the selected native sample construction remains a separate proof obligation.

Run the native control with
`bash formal/s31/tests/run_pcs_fri_projected_ood_guard_native.sh`.

## Obligation for the paired P05 theorem

The accepted native quotient path already fails closed for a degenerate
projected line. A paper-facing soundness reduction must therefore define its
successful OOD event using **every sampled projected point**, including any
shifted and periodicity points that the selected protocol retains. It must
bound the resulting aborted set under the actual Fiat–Shamir seed law and
account for conditioning on successful guard checks. The existing raw guarded
support count `(q²−1)²` does not discharge this lower-height event. This
control proves no probability bound, random-oracle law, batch width, or
release security bits.
