# Gate's 16 circle rows and Fourier coordinates

This audit covers only Gate's smallest occupied CAS07 source domain: top log
size `20`, source height `16`, so canonical log size `k=4` and **16 rows**.
The source degree limit is four ordered circle coefficients. The proved
four-slot Laurent radius is `n=2`; the P05 uniqueness lemma would need a
**common** agreement set with more than `2n=4` distinct Fourier coordinates.

## Exact row calculation

`CanonicCoset.new(4).circleDomain()` constructs a half-coset with initial
circle-generator index `2^26` and step `2^28`. Natural positions `0..7` use
indices `(1+4j)2^26`; positions `8..15` use the negatives of the same eight
indices modulo `2^31`. The stored row is first reversed over four bits:
`natural = bitReverseIndex(row,4)`. Lean's `rowIndex_injective` and
`rowIndex_eq_reduced` prove that all 16 resulting indices differ and are
multiples of `2^26`. Their reduced exponents modulo 32 are:

```text
stored row:       0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15
index / 2^26:    1 31 17 15  9 23 25  7  5 27 21 11 13 19 29  3
```

An index is not yet a circle point. The pinned native generator is
`G=(2,1268011823)` over `p=2147483647`, with addition
`(x,y)+(u,v)=(xu-yv,xv+yu) mod p`. For example, native repeated doubling gives
`[2^26]G=(1179735656,1241207368)`. Stored row 0 uses this point. Row 1 has
index `31·2^26 = -2^26 mod 2^31`; its point is the conjugate
`(1179735656,906276279)` because `-1241207368 mod p = 906276279`.
The Fourier coordinate `t=x+i y` in CM31 is the ordered pair `(x,y)`; these
two rows have different `t` despite sharing `x`.

The [Lean module](../../../formal/s31/S31/Gadgets/PcsFri/Gate16FourierRows.lean)
contains all 16 expected point pairs and proves both the point table and its
CM31 pair representation injective. Its `nativePoint_injective` and
`nativeFourier_injective` theorems deliberately require exact per-row equality
between native values and the table. The [native regression](../../../formal/s31/tests/pcs_fri_gate16_fourier_rows_native.zig) compiles the pinned `deps/stwo-zig`
gitlink `59e1f115250b8af01712b9bf3d71616e53094964` and checks the actual
`CirclePointIndex.toPoint` path, all 16 indices and point pairs, the CM31
`x+i*y` arithmetic, pairwise distinctness, and generator doubles at powers
`2^30` and `2^31`. Run it from the repository root:

```sh
bash formal/s31/tests/run_pcs_fri_gate16_fourier_rows_native.sh
```

This finite native check detects drift and supports the concrete 16-row
claim. It is not a formal refinement of Zig execution, M31 arithmetic, or
the generator order for arbitrary indices. The exact remaining formal bridge
is the per-row equality premise in `nativeFourier_injective`, grounded in the
native generator, canonical-domain and CM31 field implementations. A future
source-to-model refinement should discharge that premise against the pinned
implementation; until then the Lean result remains conditional at the native
boundary.

## P05 boundary

Distinct rows only make a five-row common set *possible*. Neither the finite
certificate nor the native regression extracts a common original/own-quotient
agreement set from an accepted FRI proof. The two-point circle-code
filtration, native query-event reduction, and BCS/ROM bound also remain open.
The [CAS07/P05 join](PCS_FRI_CAS07_P05_JOIN.md) and the
[v0.1 blocker matrix](pcs-fri-v01-blockers.json) therefore remain conditional:
`native_proven_security_bits = null`, `proven_release_admissible = false`.
