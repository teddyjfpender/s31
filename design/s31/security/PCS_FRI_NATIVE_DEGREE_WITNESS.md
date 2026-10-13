# A native P05 quotient-degree witness

**Result:** For three actual canonical circle domains, the pinned row-quotient
arithmetic admits a base-field original outside the claimed circle FFT space
whose quotient lies inside that space. This is an executable counterexample to
the inference “quotient is low degree, so the original is low degree.” It is
**not** an accepted forged PCS proof or a quantified security break. The
proven-profile release gate remains closed.

## Exact experiment

[`pcs_fri_quotient_degree_gap_native.zig`](../../../formal/s31/tests/pcs_fri_quotient_degree_gap_native.zig)
uses the pinned engine gitlink
`59e1f115250b8af01712b9bf3d71616e53094964`. It runs the same construction
on canonical circle domains with `N = 8, 16, 32` rows. It supplies nominal
column log size `log₂(N)−1` and lifting log size `log₂(N)` to the native
quotient evaluator. With verifier blowup two, the corresponding FRI degree
bound is `N/2`. For each `N`, put `m=N/4`. The independent
rank test uses the exact circle FFT space

```text
L′_(N/2)(F) = F[x]_<m + y · F[x]_<m
             = span_F { x^j, y·x^j | 0 ≤ j < m }.
```

| Domain rows `N` | Claimed space | `m` | Multiplier `h` |
| ---: | --- | ---: | --- |
| 8 | `L′₄` | 2 | `1` |
| 16 | `L′₈` | 4 | `x²` |
| 32 | `L′₁₆` | 8 | `x⁶` |

Choose the actual secure-field circle sample
`Q = SECURE_FIELD_CIRCLE_GEN.mul(17)`, claimed value `v = 0`, and one column.
Write `Q.x = prx + pix·j` and `Q.y = pry + piy·j`, with the four coefficients
in `CM31`. The native row denominator is the circle line

```text
D(x,y) = (prx·piy − pry·pix) − piy·x + pix·y   in CM31[x,y].
```

It vanishes at `Q`. Let `bar` mean conjugation in `CM31/M31`. The test
constructs the **values** of the base-field polynomial, with
`h(x)=x^(m−2)`,

```text
f(x,y) = D(x,y) · bar(D)(x,y) · h(x),     f(Q) = 0.
```

After using the circle relation `y² = 1 − x²`, the coefficient of `x^m` in
`f` is `Norm(piy) − Norm(pix)`. The test checks it is nonzero for this `Q`,
then independently rejects the `N` original values against `L′_(N/2)(M31)`
by Gaussian elimination. The expression has no `x` or `y·x` exponent above
`m`, so it remains inside the larger `L′_N` space. The first case specializes
to `L′₄ = span{1,y,x,x·y}` and `f ∈ L′₈`.

The test calls the **actual native** `core.pcs.quotients.friAnswers` on every
row of each domain, with the stated log sizes, sample, value, coefficient
ordering and bit-reversed domain order used by the verifier. For the single
sample, the batch coefficient is `random_coeff^0 = 1`. The native numerator is `c·f`,
where `c = conjugate(Q.y) − Q.y`. Every returned quotient row equals

```text
q(x,y) = c · bar(D)(x,y) · h(x).
```

Its highest `x` power is `m−1`, so `q ∈ L′_(N/2)(QM31)`. A separate QM31
rank check accepts all native quotient values in the same basis. All
denominators are checked nonzero. Run the witness with:

```sh
bash formal/s31/tests/run_pcs_fri_quotient_degree_gap_native.sh
```

The test constructs queried rows and calls the native quotient evaluator.
It does not construct Merkle commitments, a FRI proof, or run the full PCS
verifier. It therefore says nothing about whether a malicious prover can
produce an accepted proof for this column. Its purpose is to expose the
specific degree implication that cannot be used to justify the native path.
The three finite cases do not establish a general theorem for all domain
sizes, although the displayed construction explains why they share a shape.

## Protocol decision

The [S-two whitepaper theorem map](https://github.com/starkware-libs/stwo/blob/dev/.agents/papers/llm/Stwo_Whitepaper.llm.md)
describes the published degree-corrected batch-evaluation theorem as running
FRI on both the original and quotient words, with a small-table condition.
The current [`CommitmentSchemeProof`](../../../deps/stwo-zig/src/core/pcs/mod.zig)
contains one `fri_proof`; the [prover](../../../deps/stwo-zig/src/prover/pcs/scheme.zig)
supplies one lazy quotient provider to FRI; and the
[verifier](../../../deps/stwo-zig/src/core/pcs/verifier.zig) supplies one
`friAnswers` quotient word. A corrected direct-Gate protocol would therefore
need a versioned proof format and transcript, original-plus-quotient batching
at their distinct domain heights, degree-aware FRI input and query checks,
and prover/verifier tests against the same relation. Changing only the degree
bound of the existing quotient FRI does not supply a low-degree test of the
original word.

The whitepaper also discusses a weaker quotient-only relation `L⁺` with an
altered list bound. Its official theorem map does not identify a quantified
soundness theorem for this exact native protocol, including its query and
lifting choices. Such a theorem is a possible research route, not a current
release claim. In either route, P05 and the full proven-profile gate stay open
until native-to-theorem correspondence, parameters and the cryptographic
reduction are complete.
