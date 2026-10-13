# CAS05 native circle interpolation to Laurent quotient

This note records the exact scope of `NativeCircleQuotientRows.lean`. It is an
algebraic refinement of the experimental CAS05 paired source row formula, not a
PCS soundness claim.

## Source pins

The native formulas below are pinned to the experimental stwo-zig draft at
commit `0b494c95d5e1ef79f8f1f8388cd1b6c061748c51`:

- `src/core/constraints.zig`, `complexConjugateLineCoeffs`, constructs
  `a = v' − v`, `c = y' − y`, `b = v*c − a*y` for the claim `v` and sampled point.
- `src/core/pcs/transposed_paired_sparse.zig`, `fromVerifiedOpenings`, uses
  `numerator = c*opened − a*rowY − b` and
  `denominator = (x₀ − rowX)*y₁ − (y₀ − rowY)*x₁`.
- `src/prover/pcs/paired_two_height_experimental.zig`, `evaluateClaims`,
  `validateSourceDegree`, and `pairedHeight`, produce OOD claims, check source
  degree in the native circle basis, and compute the same quotient rows.
- `src/prover/pcs/paired_sparse_cascade_experimental.zig` commits those rows
  and line layers; `src/core/pcs/paired_sparse_cascade_experimental.zig`
  verifies the sampled folds. The outer byte entry point is
  `src/core/pcs/paired_sparse_cascade_wire.zig`.

These are source pins and tests, not a verified semantics for Zig execution.
The experimental outer protocol remains outside production PCS dispatch.

## One column, by hand

Write the sampled QM31 point and a claimed value over CM31 as

```text
P = (x₀ + u*x₁, y₀ + u*y₁)       v = v₀ + u*v₁
P' = (x₀ − u*x₁, y₀ − u*y₁)      v' = v₀ − u*v₁
```

The native guard requires `y₁ ≠ 0`. The affine interpolation of the claim is

```text
I(Y) = v₀ + (v₁/y₁)*(Y − y₀),     I(y₀ + u*y₁) = v.
```

At a source row `(X,Y)` with opened value `w`, the native line and conjugate
numerator satisfy exact identities:

```text
D(X,Y) = (x₀ − X)*y₁ − (y₀ − Y)*x₁
N(Y,w) = c*w − a*Y − b = (−2*u*y₁)*(w − I(Y))
native quotient = N/D = (−2*u*y₁)*((w − I(Y))/D).
```

The last equality is an algebraic equality even before checking `D ≠ 0`; the
native evaluator separately requires an inverse for `D`. The model's earlier
`PairedDenominator` and `QM31FieldInstance` results prove nonzero `D` at every
base circle row under the modeled circle, nonsquare tower, and `y₁ ≠ 0` guard.

Choose a CM31 imaginary unit `i² = −1` and Fourier coordinate `T = X+iY`.
On the circle, `T⁻¹ = X−iY`, so `Y = (T−T⁻¹)/(2i)`. The new file defines
`I(T)` as a Laurent polynomial with support in `[-1,1]`. It proves that its
evaluation at the sampled Fourier coordinate is exactly `v`, and that the
native line Laurent polynomial vanishes there when the sampled x and y
coordinates are `x₀+u*x₁` and `y₀+u*y₁`.

The theorem `native_claim_constructs_circle_quotient` composes these facts
with `CircleLaurentQuotient.native_circle_quotient_exists`. If the original
coefficient polynomial is in radius `n ≥ 1`, the Fourier coordinate has a
quadratic minimal polynomial over CM31, and the modeled OOD circle equations
and guard hold, it **constructs** `q` in radius `n−1` such that

```text
f(T) = I(T) + D(T)*q(T).
```

Thus the honest row formula has the right *own quotient* degree in this
coefficient model, up to the explicit scale `−2*u*y₁`. It is nonzero when the
quadratic tower generator `u` is nonzero, the field has odd characteristic,
and the native `y₁ ≠ 0` guard holds. The scale is essential: the native
quotient is not literally `q(T)`.

## What is still required for soundness

1. Prove a representation theorem identifying native `CirclePoly`
   `interpolateFromEvaluation` coefficients and its degree check with this
   Laurent model, including the precise filtration change from the published
   circle basis `L_n'`. This note does not infer a bounded polynomial from an
   arbitrary accepted vector of committed rows.
2. Prove that the native barycentric OOD evaluator and serialized QM31 claim
   refine the coefficient polynomial's extension evaluation; the theorem
   currently takes the equality as a premise.
3. Join the concrete sampled `QM31` field representation and x/y coordinates
   to the algebraic extension/Fourier coordinate and its quadratic minimal
   polynomial. Existing tower algebra lemmas help but do not prove the entire
   native execution path.
4. Join authenticated XDM04 and line commitments, their queried rows, and
   transcript challenges to these polynomial objects, then apply the relevant
   correlated-agreement/FRI and BCS/ROM bounds. No native security-bit figure
   follows from the quotient theorem alone.

The Lean file has no `sorry` or private axioms. Its conditional premises are
visible in the theorem statement rather than hidden behind an admitted bridge.
