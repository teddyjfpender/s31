# The circle basis dot product equals recursive evaluation

The [recursive source-word theorem](PCS_FRI_CIRCLE_RECURSIVE_BASIS_DEGREE.md)
now bounds every coefficient slot, but accepted sampled values can be
computed by several native paths. The common mathematical target is a dot
product of coefficients against the subset products of the point factors.
[`CircleBasisDot.lean`](../../../formal/s31/S31/Gadgets/PcsFri/CircleBasisDot.lean)
proves that this full dot product equals the source-transcribed recursive
evaluator for **every** list of coefficients and every power-of-two size.
Missing slots read as zero in the formal statement.

For four coefficients, the factors are `factor[0]=y` and `factor[1]=x`:

```text
slot j       0    1    2    3
binary j    00   01   10   11
basis[j]     1    y    x    y·x

dot = c₀ + c₁y + c₂x + c₃yx
    = (c₀ + c₁y) + x(c₂ + c₃y).
```

The proof splits the `2^(k+1)` sum into its low and high halves. Each high
slot has the same low-bit weight as its corresponding low slot, multiplied
by `factor[k]`. That is exactly the recursive merge rule. The result is
independent of coefficient values and applies at the accepted coefficient
logs 16, 10, and 4. `basisDot_eq_coefficientWord_eval` composes this equality
with the all-slot Laurent theorem: the mathematical dot at a secure-field
point evaluates the bounded circle polynomial built from the same
coefficients. The composed theorem
`accepted_basis_dot_two_q_own_quotients` then yields separate base and
shifted own quotients at the exact accepted height radius **if both
projected sampled claims equal these dot products**.

The Laurent theorem needs an element `i` with `i² = −1`, which native M31
does not contain. [`CircleBasisM31Embedding.lean`](../../../formal/s31/S31/Gadgets/PcsFri/CircleBasisM31Embedding.lean)
instantiates it in the modeled CM31 field: each M31 coefficient `a` maps to
the CM31 pair `(a,0)`, and its image in QM31 is the native-shaped
`QM31.fromBase(a)`. It proves the full dot of that embedded list evaluates
the corresponding bounded Laurent word. This is an explicit mathematical
coefficient-field bridge. The native M31 array-to-list conversion and Zig
machine arithmetic are still unproved.

The theorem `basisDot_split` also proves the low/high factorization for
arbitrary split sizes. At accepted source height 17, the ordinary native
split path uses 16 coefficient bits: a 10-bit low basis and a 6-bit high
basis. `accepted_height17_split_equals_recursiveValue` proves that the
corresponding mathematical split dot product equals the full recursive
evaluation. Heights 11 and 5 have coefficient logs 10 and 4, below the
native split threshold of 12.

Native source paths requiring refinement are:

| Source | Selected operation | Remaining proof obligation |
|---|---|---|
| [`point_evaluation.zig`](../../../deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig) | `fillSubsetProductBasis`, scalar/packed dot, iterative carry | Array entries, limb arithmetic, accumulation and loop bounds realize the proved dot product. |
| [`sampled_coefficient_split.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_coefficient_split.zig) | Low/high factor split for ordinary large plans | Mathematical factorization is proved; verify batch/ragged indexing and arithmetic in the native kernels. |
| [`sampled_coefficient_plans.zig`](../../../deps/stwo-zig/src/prover/pcs/sampled_coefficient_plans.zig) | Chooses split, iterative, parallel or subset route | Prove every reachable route gives the same sampled value, including fallback and audit modes. |

This theorem does not establish that the accepted 73 claims came from those
exact arrays or that the native FFT interpolant equals the formal source
word. It does not supply original/quotient degree tests, a two-Q soundness
reduction, native-to-paper batch width `M`, or security bits. P05 remains
open and release admission remains false.

## Reproduce

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.CircleBasisDot
lake build S31.Gadgets.PcsFri.CircleBasisM31Embedding
```
