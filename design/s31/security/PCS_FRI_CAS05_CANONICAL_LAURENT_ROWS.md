# CAS05 canonical rows and the first Laurent basis block

`CanonicalCircleLaurentRows.lean` closes two local gaps left by the native
interpolation quotient bridge: the first nonconstant native circle basis block
is represented by a finite Laurent polynomial, and the canonical domain's
bit-reversed adjacent rows have opposite circle-group indices. These are
algebraic/index results. They do not identify arbitrary accepted committed
rows with a low-degree polynomial.

## Native source pins

The S31-pinned stwo-zig source at `59e1f115250b8af01712b9bf3d71616e53094964`
provides:

- `src/prover/poly/circle/point_evaluation.zig`: factor zero is `y`, factor
  one is `x`, and the carry evaluator merges the first four coefficients as
  `(c₀+c₁y) + x(c₂+c₃y)`.
- `src/core/poly/circle/canonic.zig`: `CanonicCoset.new(k).circleDomain()` is
  `CircleDomain.new(Coset.halfOdds(k-1))`.
- `src/core/circle.zig`: `subgroupGen(s)` is generator index `2^(31-s)`;
  `halfOdds(s)` uses initial `subgroupGen(s+2)` and step `subgroupGen(s)`;
  `Coset.indexAt` adds the step; `CirclePointIndex.neg` negates modulo `2^31`.
- `src/core/poly/circle/domain.zig`: the second natural-order half contains
  pointwise negations of the first half.
- `src/core/utils.zig`: bit-reversed storage addresses use
  `@bitReverse(i) >> (wordBits-k)`.

The experimental CAS05 draft at `0b494c95d5e1ef79f8f1f8388cd1b6c061748c51`
adds `src/core/pcs/transposed_merkle_sparse.zig`:
`pairBase(raw,height) = (raw >> (height+1)) << 1`; the sparse checker reads
this row and the immediately following row at each height.

## A four-coefficient example

With `i²=-1` and `T=x+i*y` on the circle, set

```text
y(T) = (T-T⁻¹)/(2i)       x(T) = (T+T⁻¹)/2
P(T) = c₀ + c₁*y(T) + c₂*x(T) + c₃*x(T)*y(T).
```

The Lean proof expands the exact first four native evaluator slots and proves
`nativeFourBlock(c₀,c₁,c₂,c₃,x,y) = P(T)` at every invertible Fourier
coordinate. It also proves `P` has Laurent support in `[-2,2]`; this bound is
derived from its coefficients and does not assume a low-degree oracle.

For a native-shaped OOD claim `v=v₀+u*v₁`, the theorem
`four_block_native_claim_constructs_own_quotient` now obtains a radius-one
quotient `q` with `P=I+D*q`, using the sampled point and claim equality in the
native four-slot expression. It still requires the quadratic minimal
polynomial and modeled OOD circle/guard equations from the previous theorem.
This constructs a polynomial from four chosen coefficients. It does not show
that a full verifier-accepted committed column equals that polynomial at every
row, or that the column has a global degree bound. Those conclusions require
inverse-FFT correctness and authenticated row-to-polynomial binding.

## Bit-reversed sparse pairs

For a canonical domain of size `2^k`, let `h(j)` be `halfOdds(k-1).indexAt(j)`.
The first half has group index `h(j)` and the second half has `-h(j)`. The
proved bit-reversal recurrence gives, for every in-range pair:

```text
bitReverse_k(2m)   = bitReverse_(k-1)(m)
bitReverse_k(2m+1) = 2^(k-1) + bitReverse_(k-1)(m)

storageIndex_k(2m)   =  h(bitReverse_(k-1)(m))
storageIndex_k(2m+1) = -h(bitReverse_(k-1)(m)).
```

For example, at `k=3`, storage rows `2` and `3` select natural indices `2`
and `6`: the same half-coset position in opposite halves. For raw query `5`
at height `1`, CAS05's `pairBase` is `2`, so those are exactly the opened
rows. The theorem `canonical_sparse_pair_conjugate_indices` proves this law
for all sparse heights, not just the example.

If the index-to-Fourier-coordinate map respects group negation, the proved
`four_block_sparse_pair_conjugate` then gives the same four coefficients at
`(x,y)` and `(x,-y)` for the opened pair. That group-negation law is an
explicit premise, rather than a claim that Lean executes the native M31
generator tables.

## Remaining joins

1. Extend the four-slot coefficient/basis identity to every native circle
   factor, including the repeated `doubleX` factors and the entire FFT and
   inverse FFT. Establish its filtration equivalence with published `L_n'`.
2. Prove the native M31 generator table and machine `@bitReverse` implement
   the algebraic index and coordinate models. The source formulas are pinned,
   but Zig execution is not interpreted in Lean.
3. Show the committed source rows and barycentric OOD claim are evaluations of
   one such coefficient polynomial. The accepted Merkle openings alone bind
   rows, not a polynomial representation.
4. Connect the resulting degree-corrected oracle to correlated agreement,
   FRI, and the BCS/ROM transcript reduction. This work assigns no native
   security bits and does not enable production CAS05 dispatch.
