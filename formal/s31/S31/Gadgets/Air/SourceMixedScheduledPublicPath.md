# Source schedule to checked Gate rows

The mixed source family has a fixed address schedule: packed arithmetic rows,
lane unpacking through mask and inverse rows, and public copy rows. The older
`LocalPublicPath` theorem asks its caller to provide AIR acceptance separately
for each selected row. That makes a per-row arithmetic claim easy to overlook.

`SourceMixedScheduledPublicPath.lean` replaces those selected-row facts with
`ScheduledRow`: a row must occur in the source-owned row list with the expected
two input addresses, output address, opcode, and positive output multiplicity.
`AuthenticatedMixedTrace.gateRowsEq` connects that list to all 512 Gate rows;
`GateRows.arithmeticResidual` checks the nine QM31 operation constraints on
**every** row. The theorem `scheduled_row_accepted` derives the selected row's
arithmetic acceptance. The same conversion covers the two packed tail rows,
the eight public copy rows, and each unpack mask/inverse row.

The schedule no longer assumes the chip transition equation independently.
`SourceMixedChipRowProjection.lean` uses equality of projected input and
output event lists to identify the sixteen native rows with the chip AIR
rows. The seven-coordinate tuple is injective in its call, step, and four
values. The chip's arithmetic residuals then give
`output[lane] = input[lane]^2 + constant` on every row. The verifier-fixed
chip constant must equal the source boundary's constant; that binding remains
an explicit source-to-native obligation.

The schedule also carries a successful scan of the complete logical Gate
producer roster instead of an abstract value-uniqueness premise. The scan
uses the pinned native declared-variable bound of **512**. It checks output
addresses once per active row, including rows whose lookup
output is repeated by multiplicity. `SourceMixedProducerCheck` proves that
this decidable scan implies the value uniqueness needed by the packed and
bridge path theorems. Relating the modeled roster to native emitted rows
remains a compiler/trace obligation.

The native roster validates the output address of **every** Gate row before
skipping zero-multiplicity rows. `LocalPublicSchedule.rowAddressRange` models
that separate check, so an inactive row at address 512 cannot satisfy the
schedule merely because `checkedRoster` filters it out. The schedule assumes
this range property.

`SourceMixedFixedScheduleBridge.lean` now uses the exact N=1 and N=8 native
fixed-column exports in `GeneratedMixedFixedRows.lean`. Given an exact fixed
column match for a decoded 512-row trace and an equality identifying its row
list with the source-owned `Boundary.rows`, it derives `ScheduledRow` for
every positive-multiplicity selected cell. Concrete corollaries provide the
packed add and pointwise-multiply tail rows at addresses 33/34 for N=1 and
103/104 for N=8. Separate corollaries check that **all** exported row output
addresses are below 512, including inactive rows. This discharges the
`LocalPublicSchedule.add`, `.mul`, and `.rowAddressRange` facts for either
pinned source family once that decoded-to-source row equality is supplied.
The fixture does not construct the whole `LocalPublicSchedule`: its
`ValueAt` facts depend on main-column values and Gate production, while its
`producerScan` depends on the complete logical producer roster and baseline
yields. Authentication of the decoded fixed and main columns remains a
proof-system obligation.

The `GeneratedMixedEightV2` record ABI fixture is a different one-call
program. Its eight public words are a bit, two salt words, an aliased bit, and
four repeated-function outputs. This schedule applies to the
`mixed_general_N` chain whose eight public words are four sums and four
products of the initial and final states; the record descriptor alone cannot
specify this chain's Gate rows.

The final theorem says a false public word can close the source-shaped
reciprocal equation only at a challenge pair in the explicit exceptional set,
given this complete arithmetic trace contract and the source schedule.

Focused check:

```sh
(cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedFixedScheduleBridge)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Air.SourceMixedFixedScheduleBridge)
```

This is still conditional on the source row list being the committed row list,
on the five per-call event projections, the source schedule and checked
producer roster, and on the all-row trace contract. The ordinary
succinct native verifier does not export such a trace;
its acceptance has not yet been proved to imply these premises. The optional
full-trace native audit is a separate executable check of an attached witness.
