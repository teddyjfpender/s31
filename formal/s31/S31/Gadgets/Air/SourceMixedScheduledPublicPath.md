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

The final theorem says a false public word can close the source-shaped
reciprocal equation only at a challenge pair in the explicit exceptional set,
given this complete arithmetic trace contract and the source schedule.

This is still conditional on the source row list being the committed row list,
on the five per-call event projections, the source schedule and
producer-uniqueness premises, and on the all-row trace contract. The ordinary
succinct native verifier does not export such a trace;
its acceptance has not yet been proved to imply these premises. The optional
full-trace native audit is a separate executable check of an attached witness.
