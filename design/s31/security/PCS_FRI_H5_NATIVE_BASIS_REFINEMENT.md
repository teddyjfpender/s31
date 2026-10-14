# The 16-slot sampled-value kernel at source height five

An accepted sparse Gate proof has source columns at heights 17, 11, and 5.
For a height-5 column, the native circle coefficient array has `2^(5-1)=16`
M31 slots. This note covers **one** ordinary prover kernel for those slots:
`fillSubsetProductBasis` followed by `evalWithSubsetProductBasis`. It is a
candidate implementation refinement, not a verifier or PCS soundness claim.

## The array written by the native loop

Let the four QM31 factors be `f[0], ..., f[3]`. A coefficient slot's binary
index selects the factors multiplied into its basis weight. For example,
`index=13=1101₂` has weight `f[3]·f[2]·f[0]`.

The [native fill](../../../deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig)
sets `basis[0]=1`. At every later index `j`, it computes
`previous=j & (j-1)` and `bit=ctz(j)`, then writes
`basis[j]=basis[previous]·f[bit]`. At four factors the whole 16-cell output
fits the low block; the packed high-block branch is not entered.

| `j` | binary | `previous` | `bit` | basis weight |
|---:|:---:|---:|---:|:---|
| 0 | 0000 | — | — | 1 |
| 1 | 0001 | 0 | 0 | `f0` |
| 2 | 0010 | 0 | 1 | `f1` |
| 3 | 0011 | 2 | 0 | `f1·f0` |
| 4 | 0100 | 0 | 2 | `f2` |
| 5 | 0101 | 4 | 0 | `f2·f0` |
| 6 | 0110 | 4 | 1 | `f2·f1` |
| 7 | 0111 | 6 | 0 | `f2·f1·f0` |
| 8 | 1000 | 0 | 3 | `f3` |
| 9 | 1001 | 8 | 0 | `f3·f0` |
| 10 | 1010 | 8 | 1 | `f3·f1` |
| 11 | 1011 | 10 | 0 | `f3·f1·f0` |
| 12 | 1100 | 8 | 2 | `f3·f2` |
| 13 | 1101 | 12 | 0 | `f3·f2·f0` |
| 14 | 1110 | 12 | 1 | `f3·f2·f1` |
| 15 | 1111 | 14 | 0 | `f3·f2·f1·f0` |

[`CircleH5BasisCells.lean`](../../../formal/s31/S31/Gadgets/PcsFri/CircleH5BasisCells.lean)
unrolls this table as a length-16 array and proves, for every valid index,
that the cell equals the previously proved subset-product `basisWeight`.
It proves each predecessor is earlier and each cell satisfies the
predecessor/factor recurrence. The [Zig fixture](../../../formal/s31/tests/pcs_fri_p05_h5_basis_native.zig)
checks that native bit-clearing and `ctz` produce those same tables for all
15 nonconstant indices, then compares all cells over 64 deterministic
secure-field cases.

## Four coefficient groups

The scalar tail in the native evaluator consumes coefficients in four
groups of four. With `a[j] ∈ M31`, it computes the value

```text
V = (Σ_{j=0..3} a[j]·basis[j])
  + (Σ_{j=4..7} a[j]·basis[j])
  + (Σ_{j=8..11} a[j]·basis[j])
  + (Σ_{j=12..15} a[j]·basis[j]).
```

The Lean theorem `fourBlockAccumulation_eq_basisDot` proves this exact
16-index grouping equals the all-slot circle basis dot. Its concrete
`h5_sixteenSlotWord_equals_laurent` corollary uses a `Fin 16 → M31`
coefficient word. Each coefficient is embedded as `(a,0) ∈ CM31`, then
into QM31; the result evaluates the bounded CM31 Laurent word. The
length-indexed input excludes implicit missing coefficient slots.

The native scalar code performs each four-term group with `m31.dot4Packed`
on four QM31 coordinates. The fixture compares its result with independent
QM31 multiplication and addition, including coefficients at `p−1`, and
rejects wrong coefficient/factor/basis lengths at a checked candidate
boundary. A second [five-column fixture](../../../formal/s31/tests/pcs_fri_p05_h5_plan_tail_native.zig)
exercises `CircleCoefficients.evalManyAtPointsWithFlatFactors`: one packed
four-column group and one scalar tail, at two factor points. It rejects a
15-slot native polynomial.

## Scope still open

The Lean theorem models the 16-cell low loop and four-group field sum; it
does not prove Zig SIMD instructions, `dot4Packed` reduction, or the
actual accepted prover's selection and coefficient provenance. The native
fixtures are differential tests, not exhaustive proofs. The accepted
73 sampled values still need to be tied to the exact FFT arrays and
projected OOD factors. Heights 11 and 17, fallback routes, original and
own-quotient whole-oracle degree tests, and the two-instance BCS/paper
soundness join remain open. Native-to-paper `M` and proven bits remain null.

## Reproduce

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.CircleH5BasisCells
cd ../..
bash formal/s31/tests/run_pcs_fri_p05_h5_basis_native.sh
```
