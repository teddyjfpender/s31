# Gate's four-slot source and its two-point own quotient

**Scope.** Gate's smallest occupied CAS07 source domain has 16 circle rows
and at most four ordered source coefficients. The [Lean theorem](../../../formal/s31/S31/Gadgets/PcsFri/GateFourBlockOwnQuotient.lean)
proves the exact degree implication for that four-slot coefficient model.
It does not derive the coefficients from an adversarial commitment or transfer
the S-two paper's circle-code theorem to CAS07.

## Compute the quotient by hand

Write the four-slot source as

```text
f(x,y) = c0 + c1·y + c2·x + c3·x·y.
```

The conjugate OOD point has coordinates
`P=(x0+u·x1, y0+u·y1)` over the quadratic extension of CM31. Its two
claimed CM31 limbs are `v0,v1`, so a *correct* claim satisfies
`f(P)=v0+u·v1`. When `y1≠0`, the native affine interpolation and circle line
are

```text
I(y)   = v0 + (v1/y1)·(y-y0)
D(x,y) = (x0-x)·y1 - (y0-y)·x1.
```

Both `f(P)-I(P)` and `D(P)` are zero. In Fourier coordinates
`t=x+i·y`, the four-slot source has Laurent support in `[-2,2]`, while
`I` and `D` have support in `[-1,1]`. The guarded OOD point has a quadratic
minimal polynomial over CM31. The native line is a nonzero scalar times
that minimal polynomial shifted by `t⁻¹`. Dividing `f-I` by it therefore
produces **one CM31 Laurent polynomial `q` supported in `[-1,1]`**:

```text
f = I + D·q.
```

The [formal corollary](../../../formal/s31/S31/Gadgets/PcsFri/GateFourBlockOwnQuotient.lean)
also proves the actual row equations for **every** base Fourier unit `t`:

```text
own(t)    = (f(t)-I(t))/D(t) = q(t)
native(t) = N(t)/D(t) = (-2·u·y1)·q(t),
N(t)      = -2·u·y1·(f(t)-I(t)).
```

There is no extra row-by-row nonzero assumption: an irreducible quadratic
minimal polynomial has no CM31 root, so `D(t)≠0` at every CM31 Fourier
unit. The `-2·u·y1` factor is the exact conjugate-line numerator scale; it
must be retained when comparing a native row with the own quotient.

The [all-input four-slot map](../../../formal/s31/S31/Gadgets/PcsFri/GateFourSlotNativeMap.lean)
now gives explicit coefficients for `f=c0+c1·y+c2·x+c3·x·y` at every guarded
two-point sample. With `s=x1²+y1²`, its own quotient has the form
`q=A+B·x+C·y`, where `B=c3·x1/s` and `C=-c3·y1/s`; hence
`y1·B+x1·C=0`. The theorem also proves the exact claimed limbs and row
reconstruction. It does not establish that native committed columns equal
those four-slot polynomials or that the full FRI verifier enforces their
degree bound.

## A finite native check and a sharpness counterexample

The [focused Zig regression](../../../formal/s31/tests/pcs_fri_gate_four_block_own_quotient_native.zig)
uses the pinned stwo-zig gitlink
`59e1f115250b8af01712b9bf3d71616e53094964`. Its runner rejects a
checkout at a different submodule commit. It takes source coefficients
`[3,5,7,11]`, the secure circle sample `G^17`, and the exact 16-row
canonical log-4 domain. It compares the actual native
`CircleCoefficients.evalAtPoint` and 16-row `evaluate` results with the
four-slot formula, then checks the native `complexConjugateLineCoeffs`
numerator and quotient equation at each row. The resulting quotient fits

```text
q(x,y) = A + B·x + C·y
A = (163111111, 1581935086) in CM31
B = (289486897, 1518859802) in CM31
C = (283670729, 1724306845) in CM31.
```

The test checks these values by solving from three rows and validating all
16; it also checks `B≠0` and that no `a+b·y` expression fits all 16 rows.
Thus the tempting stronger inference “a four-slot source always has a
two-slot `{1,y}` own quotient” is **false** for this correct claim. Radius
one is the proved bound; equating it with the first two native circle slots
would overstate the result. Changing the OOD claim by `+1` also makes the
16 quotient rows fail the radius-one fit, so correctness of the claim is a
necessary premise in this finite example.

Run the regression from the S31 repository root:

```sh
bash formal/s31/tests/run_pcs_fri_gate_four_block_own_quotient_native.sh
```

## What remains conditional

The Lean statement assumes the exact ordered four coefficients and the
`hnativeClaim` equation at the OOD point. It also assumes the modeled
Fourier/sampled coordinate identities, the circle equations, `y1≠0`, and a
quadratic minimal polynomial. Other existing Lean modules derive some of
these from a modeled guarded QM31 circle point; this theorem does not
interpret the compiled sampler or prove that a committed column is the
four-slot polynomial. The finite native regression tests one honest
coefficient vector and one OOD sample. It is not an accepted-proof theorem.

To discharge P05, the verifier's authenticated original rows and derived
quotient rows must refine these **same** coefficient polynomials, with the
native numerator scale and claim ordering preserved. A separate proof must
derive a common original/own-quotient agreement set from FRI acceptance and
establish the relevant two-point circle-code filtration and small-domain
condition. The [P05 blocker matrix](pcs-fri-v01-blockers.json) remains open:
`native_proven_security_bits = null` and
`proven_release_admissible = false`.
