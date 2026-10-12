# Source determined physical soundness

`SourceDeterminedPhysicalSoundness.lean` composes the exact byte parser,
source-derived direct Gate row count, arbitrary decoded AIR trace, and ideal
Gate balance. It applies to every source in the bounded direct grammar, and
to the canonical alias extension, rather than a fixed finite source fixture.

For a source with `m` pointwise products, the grouped trace has `476 − m`
addition rows, one subtraction row, 27 ordinary multiplication rows, `m`
source pointwise rows and eight fixed pointwise rows. The byte checker caps
the total arithmetic instructions at 16, so this is a valid 512-row layout.
The caller does not choose an add count or assert that partition equation.

The caller still supplies `UnpartitionedTrace` facts about the arbitrary
decoded trace: source and public fixed cells match the modeled schedule;
installed arithmetic roots vanish; active Gate producers are unique; the
zero, basis and inverse values exist; and the four input and four output
public words appear as external Gate uses. Under *ideal exact* Gate balance,
`direct_bytes_balanced_implies_claim` and
`canonical_alias_balanced_implies_claim` force the public claim to equal the
source computation. Their false-claim counterparts prove that a fixed
incorrect claim cannot have ideal exact balance. The existing raw Gate
theorem bounds exceptional ideal challenge pairs after address and event
count assumptions.

`direct_false_claim_raw_pair_bound` and
`canonical_alias_false_claim_raw_pair_bound` make that algebraic consequence
explicit: for any fixed 512-row trace meeting the stated physical facts,
canonical address bound, and event multiplicity bounds, the count of
accepting ideal challenge pairs is at most
`(5s² + 2s + 1536) · |QM31|`, where `s` counts distinct use/yield tuples.
The ideal challenge space contains `|QM31|²` pairs. The theorem has no
caller-selected add row count, and does not assert a probability bound for
adaptive or Fiat–Shamir challenges.

For `let y = x .* x; y`, one source pointwise product puts the add partition
at 475 rows and the product at physical row 503. A hypothetical decoded
trace that satisfies the row roots but claims the wrong public output cannot
have balanced Gate read/produce events when the stated physical facts hold.

This result does not prove that a native proof authenticates all decoded
cells, that native Zig emits the modeled schedule for every admitted source,
or that LogUp/PCS/FRI/Fiat–Shamir implement the ideal premises. The
four-source native export fixture provides concrete cross-implementation
checks, not a universal replacement for those proof obligations.

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.SourceDeterminedPhysicalSoundness)
(cd formal/s31 && lake env leanchecker -v S31.Gadgets.Functional.Correspondence.SourceDeterminedPhysicalSoundness)
```
