# Native circle FFT rows and coefficient words at sparse source heights

The sparse Gate candidate has source heights 5, 11, and 17. Its corresponding
native circle coefficient arrays contain `2^4`, `2^10`, and `2^16` M31 cells.
The algebraic [circle FFT-space theorem](PCS_FRI_CIRCLE_FFT_POLYNOMIAL_SPACE.md)
applies to any arrays of these lengths, but it does not itself show that the
selected native interpolation produces the array for a committed source
column.

[`pcs_fri_sparse_fft_provenance_native.zig`](../../../formal/s31/tests/pcs_fri_sparse_fft_provenance_native.zig)
checks a finite native link at **all three lengths**. It fills every
coefficient slot with a deterministic canonical M31 value, calls the pinned
circle FFT to produce bit-reversed domain rows, interpolates those rows back,
and checks every recovered coefficient. At five rows for each height, it also
constructs the factor schedule directly, then computes the circle-basis
subset product independently at five source rows and one secure-field point
outside the M31 source domain:

```text
factor[0] = y, factor[1] = x, factor[2] = 2x²−1, ...
basis[j]  = product of factor[bit] for each set bit of j
row_value = sum_j coefficient[j] · basis[j]
```

The test compares its factors with the native factor vector, and its
independent sum with the FFT row value and native point evaluator. For four
coefficients, the sum is
`c₀ + c₁y + c₂x + c₃xy`; the same bit rule covers all 65,536 slots at
coefficient log 16. It uses the native domain's bit-reversed row index, so
the comparison also checks the row-order convention.

```sh
bash formal/s31/tests/run_pcs_fri_sparse_fft_provenance_native.sh
```

This is a **finite differential test over synthetic dense columns**. It
cannot prove FFT correctness for every M31 input, that accepted Gate columns
are these tested columns, or that their committed source rows and verifier
opened rows have this provenance. A source-to-array refinement, all
reachable optimized evaluator routes, and the paper's domain/quotient join
remain open. P05, the batch width `M`, native security bits, and release
admission remain open.
