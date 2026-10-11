# Mixed chip-to-packed-wire correspondence

`SourceMixedPackCorrespondence.lean` closes the two packed-value premises of
`SourceMixedPublicClosure.lean` for the reviewed direct mixed program family.
It proves that the packed private input at Gate address 22 and the packed
final chip state at `22 + 10N` have the four expected M31 coordinates.

The compiler's `simd.pack` path for four scalar words uses six Qm31 rows:

```text
term1 = e1 × scalar1       term2 = e2 × scalar2
term3 = e3 × scalar3       sum1  = scalar0 + term1
sum2  = sum1 + term2       packed = sum2 + term3
```

Here `e1`, `e2`, and `e3` are the fixed extension-basis unit vectors. The
`PackPath` predicate selects these six rows from the modeled Gate list,
requires their exact input/output address links and local nine-residual AIR
acceptance, and requires the three basis constants at their selected Gate
addresses. The five temporary addresses are existential because their
allocation is not proved by this module. The packed output address is fixed:
22 for the input and `22 + 10N` for the last chip state (32 at `N=1`, 102
at `N=8`).

The source-shaped bridge reads the four scalar input events at 11–14
and the final four scalar output events at `23 + 10(N−1)` through
`26 + 10(N−1)`. Exact Gate event balance and unique produced values force
those bridge uses to equal yielded circuit values, which the six pack rows
then read along with the basis constants.
`PackRows.acceptsPack_sound` then proves that their final output equals the
four-coordinate packed state. Positive output multiplicity makes that packed
value a produced Gate tuple. `all_public_outputs_from_pack_paths` composes
this result with the public-tail theorem, deriving all eight public words
without assuming either packed-value membership.

The compiler-to-model proof that the selected rows and basis constants
actually occur in the native trace remains open. So do the native
proof-to-exact-event reduction, producer uniqueness authentication, and
all-row AIR authentication. The theorem states those obligations explicitly;
it does not claim full native verifier soundness.
