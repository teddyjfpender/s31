# Independent review: mixed formal soundness path

Reviewed the current `SourceMixedAuthenticatedTrace`, `SourceMixedEventAlignment`,
`SourceMixedChipRowProjection`, `SourceMixedScheduledPublicPath`,
`SourceMixedProducerCheck`, and `CanonicalDagOptimization` Lean modules on
2026-10-11, before and after the producer-scan refinement described below.
This is a premise audit, not a PCS/FRI proof or native verifier refinement.
The counterexample lives in
`formal/s31/adversarial/SourceMixedProducerBound.lean`.

## Result

I found no invalid algebraic implication, omitted chip row in the ordered
projection, or hidden deduction from native verifier acceptance. The mixed
false-word result remains conditional on authenticated row values, source row
identity, local event projections, the fixed chip constant, the compiler's
public schedule, and a fixed pre-challenge witness. I found one concrete
native/refinement mismatch in the schedule's producer scan; it has since
received the focused source and native-test fix described below.

## Ordered chip rows and producer values

`ChipRows 8` has sixteen logical rows. Equality of its `inputEvents` with
`List.ofFn` of the source-shaped row tuples first forces the source row count
to sixteen. `List.ofFn_injective` then equates every ordered tuple. The
seven-coordinate chip tuple's injectivity recovers its call tag, step, and
four input words; the output equality similarly recovers all four output
words. `EventProjection.chip_step` correctly transports every chip arithmetic
equation to the corresponding source-shaped row. This argument genuinely uses
ordered equality: an unordered event permutation alone would not identify
the equation for each row index. The chip constant equality remains an
explicit native/source binding premise.

`unique_produced_of_checked_roster` is sound for its abstract claim. Every
emitted Gate yield is covered by one active row's logical producer or an
external yield in `checkedRoster`; a successful address scan makes that
roster duplicate-free. The theorem derives value uniqueness, not native
address-range or compiler correspondence.

## Producer-scan range mismatch

Before the fix, `LocalPublicSchedule.producerScan` existentially chose a
`bound`. Consequently an active producer at address 512 is accepted by
`scan 513 ∅ [512]`, although `scan 512 ∅ [512]` rejects it. Also,
`checkedRoster` filters zero-multiplicity rows before scanning, so an inactive
row with output address 512 is invisible to that scan. The standalone Lean
counterexample checks both cases.

For the pinned one-to-eight-call native source family, 512 is fixed:
`producer_roster_correspondence.zig::audit` requires `view.n_vars == 512` and
512 Qm31 rows (lines 85–97), then calls `scanAddresses(&rows, view.n_vars)`
(line 135). Its helper requires `bound == 512` and rejects every row address
`>= bound` **before** skipping zero-multiplicity rows (lines 58–66). Thus the
pre-fix Lean schedule's scan was enough for its uniqueness theorem but was
not a faithful model of this native fixed-family range check. The generic
uniqueness theorem correctly retains its arbitrary bound.

**Resolution status:** `LocalPublicSchedule.producerScan` now pins the scan
to 512, and `rowAddressRange` requires every modeled Gate output address to
be below 512, including inactive rows. The root agent also added a native
zero-multiplicity out-of-range regression. The focused Lean compile and
native regression passed; the full kernel replay/evidence gate for this
source revision was still pending when this report was committed. The
standalone counterexample remains as a regression against accidentally
replacing the fixed-family premises with the weaker generic scan.

Independent native tests make the honest schedule plausible: the N=1..8
producer-roster fixture checks the fixed rows, active output addresses, and
bridge endpoint multiplicities, while `trace_correspondence.zig` checks the
packed input/final values and public unpack/copy rows. There is still no Lean
construction of the entire `LocalPublicSchedule` from those native exports.

## Remaining proof boundary

The `AuthenticatedMixedTrace` fields bind modeled Gate rows to a source row
list and assert component residuals and the native claim fold. The
`EventProjection` fields identify local chip and bridge event lists with
source-shaped tuples. None of these structures is constructed from arbitrary
accepted native proof bytes, and the optional full-trace sidecar does not
return a Lean certificate. A complete accepted-proof theorem still needs
column/row decoding, fixed-column and transcript correspondence, Merkle
binding, PCS/FRI extraction or soundness, and a pre-challenge commitment
argument for the exceptional-pair bound.

The Gate contract's three nonzero denominator premises per row are essential.
The paired AIR residual is identically zero when both use denominators vanish,
regardless of its claimed fraction; the one-denominator yield equation can
also lose information at a pole when its numerator vanishes. The optional
trace audit rejects such poles, while a theorem from ordinary AIR acceptance
must either exclude them as an explicit challenge event or account for them
inside its soundness error. They cannot be silently inferred from the AIR
residuals alone.

The canonical DAG optimizer's semantic theorem is valid for every result
that passes its symbolic audit. Its nontrivial reversed/duplicate example is
outside the accepted `SSATextBytes` grammar: `parseLet` rejects a reversed
operand order and an already-seen `(operation, lhs, rhs)` key. The optimizer
does not yet establish a nontrivial source-byte-to-native-IR refinement, as
its module documentation acknowledges.
