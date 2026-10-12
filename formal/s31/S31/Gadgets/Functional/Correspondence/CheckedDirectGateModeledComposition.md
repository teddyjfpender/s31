# Checked direct-Gate modeled composition

`checked_direct_full_modeled_trace` joins three executable checks:

1. Exact S31 source and normalized-byte admission gives a bounded direct-Gate
   certificate and honest functional output.
2. The constant-island checker verifies the supplied fixed cells, coherent
   value table, row roles, seed values, and local arithmetic.
3. The address ledger checks bounded fixed-address event counts against
   supplied external feeder and sink addresses.

For every admitted input, the theorem constructs **one modeled 512-row wire**
with complete row coverage, matching selected fixed cells, zero installed
local arithmetic roots, the selected public output, and exact ideal Gate event
balance for that same wire. The shared source/public/constant addresses are
derived from boundary contracts; there is no separate agreement hypothesis.
`checked_u8_direct_full_modeled_trace` gives the same result for literal
`List UInt8` source and normalized bytes.

The island and ledger checks remain explicit premises. In particular, the
external address lists are caller supplied, and the theorem's `gateRows`
list is built from `joinedCells`. It does not establish that native committed
rows decode to that list, that native public components use those exact
feeder/sink events, or that STARK verification implies exact ideal lookup
balance. Those are separate compiler, native binding, and cryptographic
proof-system obligations.

Focused verification:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.CheckedDirectGateModeledComposition
lake env leanchecker -v S31.Gadgets.Functional.Correspondence.CheckedDirectGateModeledComposition
```
