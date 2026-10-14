# Gate's exact quotient-only edge gap

**Status:** P05 remains open. This is an algebraic theorem and a pinned native
16-row check for Gate's smallest occupied source domain. It identifies one
missing degree-correction condition in the experimental two-point circle
relation. It is neither an accepted forged proof nor a quantified soundness
claim for production PCS. The production-native quotient-only witness across
three domains is recorded [separately](PCS_FRI_NATIVE_DEGREE_WITNESS.md).

## Four source slots versus five reconstructed slots

The first four native circle coefficient slots evaluate as

```text
f(x,y) = c0 + c1·y + c2·x + c3·x·y,       x²+y²=1.
```

All four-slot polynomials obey an elementary identity. Add their values at
`(1,0)` and `(-1,0)`, then do the same at `(0,1)` and `(0,-1)`. Both sums
are `2·c0`. The [Lean theorem](../../../formal/s31/S31/Gadgets/PcsFri/GateQuotientOnlyGap.lean)
proves this for every field of odd characteristic. The M31-valued source
`f(x,y)=x²` violates it: the first pair sums to `2`, the second to `0`.

Now take the native conjugate OOD line and an affine own quotient:

```text
D(x,y) = (x0·y1-y0·x1) - y1·x + x1·y
I(y)   = i0 + i1·y
q(x,y) = a + b·x + c·y.
```

The quotient-only reconstruction `f=I+Dq` is exactly

```text
f(x,y) = C0 + C1·y + C2·x + C3·x·y - (y1·b+x1·c)·x²

C0 = i0 + (x0·y1-y0·x1)·a + x1·c
C1 = i1 + (x0·y1-y0·x1)·c + x1·a
C2 = (x0·y1-y0·x1)·b - y1·a
C3 = x1·b - y1·c.
```

The substitution uses only `y²=1-x²`. The formal `reconstructed_in_four_slots_iff`
proves the **exact criterion**: this reconstructed function lies in Gate's
four-slot source space if and only if `y1·b+x1·c=0`. A broad radius-one
quotient membership check alone cannot enforce that equation. Proving a way
to enforce it on a committed oracle, or switching to a proven
degree-corrected ensemble, is a separate protocol task.

## Concrete canonical 16-row check

The [native regression](../../../formal/s31/tests/pcs_fri_gate_quotient_only_gap_native.zig)
uses the pinned stwo-zig gitlink `59e1f115250b8af01712b9bf3d71616e53094964`,
the exact bit-reversed log-4 canonical circle domain, and
`Q=SECURE_FIELD_CIRCLE_GEN.mul(17)`. It puts the **M31** value `x²` in each
source row and claims its real OOD value `Q.x²`. Native interpolation returns
exactly coefficient slots `0` and `4`, each `1/2=1073741824 (mod p)`; slot 4
is outside the permitted four slots. Native `evalAtPoint` returns `Q.x²`.

The test computes the conjugate-line numerator, denominator and every row's
own quotient. The 16 quotient rows fit `a+b·x+c·y`, but their coefficients
satisfy `y1·b+x1·c ≠ 0`. For comparison, the
[honest four-slot test](../../../formal/s31/tests/pcs_fri_gate_four_block_own_quotient_native.zig)
checks that the same expression is zero for its correct source and OOD claim.
Both tests check the native `-2·u·y1` quotient scale. Run them with:

```sh
bash formal/s31/tests/run_pcs_fri_gate_four_block_own_quotient_native.sh
bash formal/s31/tests/run_pcs_fri_gate_quotient_only_gap_native.sh
```

This check uses source rows and native arithmetic but does not construct a
Merkle commitment, FRI proof, or accepting verifier transcript. The Lean
radius-one result is a Laurent-support statement; it is not yet a refinement
to the paper's circle-code filtration or to production's quotient-only
degree bound. The release ledger therefore keeps P05 open and native proven
security bits unset.
