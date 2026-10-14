# The recursive coefficient word lies in the paper's circle FFT space

The [S-two whitepaper](https://eprint.iacr.org/2026/532.pdf), Section 1,
Eq. (21), defines its circle FFT space as

```text
L′ₖ(F) = F[x]_<2^(k−1)  +  y · F[x]_<2^(k−1).
```

This is stronger than saying the corresponding Laurent polynomial has
radius at most `2^(k−1)`. The radius bound also admits one top direction
outside the `2^k`-dimensional FFT space. The earlier
[recursive Laurent proof](PCS_FRI_CIRCLE_RECURSIVE_BASIS_DEGREE.md) alone did
not establish the stronger space membership.

[`CircleFftPolynomialSpace.lean`](../../../formal/s31/S31/Gadgets/PcsFri/CircleFftPolynomialSpace.lean)
builds a pair of ordinary polynomials `(P,Q)` from **every** coefficient in
the native-shaped recursive word. At coefficient log zero the pair is
`(c₀,0)`; at log one it is `(c₀,c₁)`. For higher logs it splits the vector
into two halves and multiplies the upper pair by the matching native
double-angle x factor. Lean proves both component degrees strictly below
`2^(k−1)` for every `k ≥ 1` and every coefficient list. It also proves that
evaluating `P(x)+yQ(x)` equals the recursive field evaluator and the
previously constructed Laurent word at each nonzero Fourier point.

For four coefficients, the pair is

```text
P(x) = c₀ + c₂x
Q(x) = c₁ + c₃x
f(x,y) = (c₀+c₂x) + y(c₁+c₃x).
```

Both component degrees are below two. For eight coefficients, split them
into two four-coefficient pairs `(P₀,Q₀)` and `(P₁,Q₁)` and write

```text
v₂(x) = 2x²−1
P(x) = P₀(x) + v₂(x)P₁(x)
Q(x) = Q₀(x) + v₂(x)Q₁(x).
```

Each component degree is below four. Induction gives the same statement
for all coefficients of the accepted sparse Gate source heights:

| Extended source height | Coefficient log `k` | Coefficients | Strict degree cap for each of `P,Q` |
| ---: | ---: | ---: | ---: |
| 17 | 16 | 65,536 | `<32,768` |
| 11 | 10 | 1,024 | `<512` |
| 5 | 4 | 16 | `<8` |

This closes the **model-level original-word FFT-space** gap. The theorem's
list interface is total and pads/truncates malformed lengths, so native
coefficient-array length and provenance still need refinement. The selected
prover must be shown to interpolate the committed source column into this
exact vector, and its iterative/packed sampled evaluator must match the
recursive model. The paper's domain, quotient-space, correlated-agreement,
two distinct OOD point, and BCS premises remain open. P05 and release
admission remain closed.

Focused check:

```sh
(cd formal/s31 && lake build S31.Gadgets.PcsFri.CircleFftPolynomialSpace)
```
