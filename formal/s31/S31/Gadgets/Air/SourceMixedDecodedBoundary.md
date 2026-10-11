# Trace-owned mixed-chain boundary

`SourceMixedDecodedBoundary.lean` constructs the modeled Gate rows from a
decoded 512-row direct-Gate trace. Its `DeclaredAddressBounds` checks all three
address columns on **all 512 rows**, including padding. The pinned N=1 and N=8
fixed-column exports satisfy these bounds by kernel reduction. For each row,
`canonicalRowAt` keeps its flags, four-lane main values, multiplicity, and
addresses; the address proof only converts a checked natural address into
`Fin p`. Thus `canonicalRows_toGate` proves the exact equation

```text
canonicalRows(trace).map(toGate) = nativeRows(trace)
```

by construction. `boundaryFromTrace` retains the supplied boundary's call
metadata, words, public outputs, and baseline events while replacing its Gate
rows. The earlier decoded-to-boundary 512-row equality is therefore no longer
an external hypothesis **for this constructed boundary**. It does not assert
that an arbitrary boundary's preexisting row list equals the trace.

`pinnedBoundary` goes further for the reviewed `mixed_general_N` chain. It
sets each call to 16 rounds, its constant to `13 + call`, and its eight Gate
addresses to the proved `canonicalAddress` formula. It sets the first four
input words from `initial` and retains the template's other words, public
outputs, and baseline events. The first-state equation and the metadata
schedule now follow by reduction. `n1_pinned_local_schedule` and
`n8_pinned_local_schedule` construct `LocalPublicSchedule` with none of the
old row-list, address, constant, or first-state premises supplied by a caller.

The pinned local theorem still assumes:

| Premise | Remaining source of evidence |
| --- | --- |
| Every decoded fixed cell equals the N=1 or N=8 export | Bind the decoded trace to the pinned generated fixed-column fixture. |
| Template has no baseline yields | Source circuit roster/producer contract. |
| Packed initial and final values, zero, unit and inverse-unit `ValueAt` facts | Main-column witness and Gate-production correspondence. |

The theorem applies to the chain family returning sums and products of the
initial and final four-lane states. The separate `GeneratedMixedEightV2`
record program has a different public-output meaning. The template's
remaining words and `publicOutputs` are not inferred from the source or proof
by this constructor. A native proof-acceptance theorem and exact compiler-to-
trace authentication are still needed before the schedule can be claimed for
an arbitrary accepted proof.

The follow-on [main-cell certificate](SourceMixedPinnedMainCells.md) replaces
the remaining `ValueAt` fields by exact decoded output-main-cell equalities
at ten kernel-checked positive producer rows, and derives the complete
source shape from the fixed export.

Focused checks:

```sh
(cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedDecodedBoundary)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Air.SourceMixedDecodedBoundary)
```
