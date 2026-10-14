# Source-height 11 and 17 basis cells

The accepted sparse Gate proof has 28 source columns at circle height 11 and
14 at height 17. Their circle coefficient words have `2^10 = 1,024` and
`2^16 = 65,536` M31 slots. This note checks one mathematical and native
sampled-value path for words of those sizes. It extends the
[16-slot height-five example](PCS_FRI_H5_NATIVE_BASIS_REFINEMENT.md).

## What one basis cell means

For factors `f[0], ..., f[k−1] ∈ QM31`, define

```text
basis[j] = product of f[r] for every set bit r of j,  0 ≤ j < 2^k.
value    = sum over j of coefficient[j] · basis[j].
```

For example, `j=513=512+1` has bits 9 and 0 set, so
`basis[513]=f[9]·f[0]`. The native
[`fillSubsetProductBasis`](../../../deps/stwo-zig/src/prover/poly/circle/point_evaluation.zig)
first fills 256 low cells. At `j=513`, it takes high block `513 >> 8 = 2`
and low offset `513 & 255 = 1`. The high block clears its only set bit to
zero and multiplies `f[9]`; the low cell is `f[0]`. Their product is exactly
`f[9]·f[0]`. For height 17 the same rule applies through bit 15, including
the packed high-block multiplication.

The native low and high schedules use `previous=j & (j−1)` and
`bit=ctz(j)`. The [Lean module](../../../formal/s31/S31/Gadgets/PcsFri/CircleBasisPrefixRecurrence.lean)
proves a prefix invariant by induction on the number of written cells. Its
`BitSchedule` certificate states the exact equations

```text
previous = quotient · 2^(bit+1)
j        = previous + 2^bit
bit < k, quotient < 2^(k−bit−1).
```

These equations imply `previous<j` and prove the basis recurrence for every
power-of-two length. The theorem then factors each full cell into its low
and high cells and proves that the column-major blocked dot equals the
all-slot `basisDot`. `certifiedM31Word_eq_laurent` embeds every M31 slot as
`(a,0) ∈ CM31` and connects that dot to its bounded Laurent polynomial.
Its `Fin (2^(low+high))` input prevents a short coefficient word from being
silently padded. Instantiating `(low,high)=(8,2)` and `(8,8)` gives the
height-11 and height-17 mathematical words.

## What the native check covers

The [source-bound Zig fixture](../../../formal/s31/tests/pcs_fri_p05_general_basis_native.zig)
checks all 1,024 and 65,536 native basis cells against an independent
set-bit product. For every nonzero index it checks the certificate equations,
predecessor order, factor bound, and native recurrence. It compares the
scalar basis dot and the iterative carry evaluator against an independent
QM31 reference. It also checks native-width packed batch columns, the
height-17 low-10/high-6 split evaluator, and every full cell against the
split product. Cases include nonconstant factors, random secure-field
factors and M31 coefficients, and `p−1` coefficients. A high-bit-only word
detects mutation of factor 15; wrong logs and each wrong array length are
rejected at the candidate wrapper boundary.

The [runner](../../../formal/s31/tests/run_pcs_fri_p05_general_basis_native.sh)
pins the accepted source roster to coefficient logs 10 and 16 before the
native test. The test does not inspect or authenticate the coefficient
arrays inside the accepted proof. It establishes a differential result for
the selected kernel at actual sizes, and a conditional mathematical theorem
for arbitrary sizes. It does not prove Zig machine instructions, SIMD
reductions, or that every possible factor word passes the native path.

The accepted FFT coefficient-array provenance, projected OOD factor
provenance, alternate sampled-value routes, authenticated original and own
quotient whole-oracle degree tests, two-instance BCS reduction, and exact
paper Protocol 3/4 mapping remain open. In particular, paper batch width
`M`, proven native security bits, and release admission remain unset.

## Reproduce

```sh
cd formal/s31
lake build S31.Gadgets.PcsFri.CircleBasisPrefixRecurrence
cd ../..
bash formal/s31/tests/run_pcs_fri_p05_general_basis_native.sh
```
