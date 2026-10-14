# Accepted sparse OOD points to coefficient factors

The accepted sparse Gate proof has 61 source columns and 73 explicit OOD
claims at extended circle log heights 17, 11, and 5. The verifier owns each
claim's raw top-domain point through the accepted key's mask order. The
[existing point check](../../../formal/s31/tests/pcs_fri_p05_projected_map_native.zig)
reconstructs those points from the key-owned offsets, sampled seed, and
canonical mask step. This slice follows each raw point into the **native
sampled-coefficient plan's actual factor vector**.

| Extended log height `h` | Source columns | Explicit claims | Point doublings `17−h` | Coefficient factors `h−1` |
|---:|---:|---:|---:|---:|
| 17 | 14 | 18 | 0 | 16 |
| 11 | 28 | 32 | 6 | 10 |
| 5 | 19 | 23 | 12 | 4 |

There are `18·16 + 32·10 + 23·4 = 700` checked factor slots across the
accepted claim roster. The four extra claims at each height are shifted mask
samples; each retains its own ordered raw point and factor slice.

## Hand calculation

For a height-11 claim, let `Q` be its raw top-domain point. The native plan
sets `P = [2⁶]Q`. If `P=(x,y)`, the first four factors are

```text
factor[0] = y
factor[1] = x
factor[2] = 2x² − 1
factor[3] = 2(2x² − 1)² − 1.
```

It continues through `factor[9]`. For height 5 it first doubles 12 times
and takes four factors. For height 17 it takes 16 factors at the raw point.
The exact projection and factor count matter: using `Q` without six
doublings for a height-11 column evaluates a different polynomial point.

[`sampled_values.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_values.zig)
passes `lifting_log_size - column.log_size` to the coefficient plan.
[`sampled_coefficient_plans.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_coefficient_plans.zig)
normalizes each point with `repeatedDoubleOnCircleQM31` and calls
`fillEvalFactorsForPoint` with the coefficient log. The latter writes
`y, x, doubleX(x), ...` in
[`point_evaluation.zig`](../../../deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig).

The [Lean theorem](../../../formal/s31/S31/Gadgets/PcsFri/CircleProjectedFactorVector.lean)
proves, for any field and any number of doublings, that the point-doubling
x-coordinate recurrence equals the circle-basis `nativeFactorValue`
recurrence. Its `Fin (h−1)` vector prevents a missing or extra factor.
This is an algebraic model theorem; it does not establish native byte-level
equivalence by itself.

The [native test](../../../formal/s31/tests/pcs_fri_p05_sparse_ood_factors_native.zig)
calls the **production `getOrCreateCoefficientEvalPlan`** for all 61 accepted
columns. For every one of the 73 ordered claims it independently recomputes
the projected point and all factors, then checks the plan's normalized point
and flat factor slice. It compares the plan against the second native folded
factor entry point as a source-indexing cross-check. Wrong coefficient log,
fold count, point order, and a mutated last factor each fail the checked
candidate audit. The runner executes the prior key/mask point check first.

## Boundary

This is a finite accepted-object differential for the ordinary
sampled-coefficient plan. It does not prove that the accepted proof's FFT
coefficient arrays match the source polynomials, that all fallback routes
produce the same claims, or that the native verifier tests original and own
quotient whole-oracle degrees. It does not establish the paper's multi-Q
batch mapping or BCS reduction. P05 stays open; paper batch width `M`, native
security bits, and release admission stay unset.

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.CircleProjectedFactorVector
cd ../..
bash formal/s31/tests/run_pcs_fri_p05_sparse_ood_factors_native.sh
```
