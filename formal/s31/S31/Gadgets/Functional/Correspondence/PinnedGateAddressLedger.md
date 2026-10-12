# Full pinned square4 Gate address ledger

`PinnedGateAddressLedger.lean` independently reads all eight fixed words of
each of the 512 pinned native direct-Gate rows into `ColumnCell`. It checks
the address-only exact Gate ledger against public feeder addresses
`[2, 3, 4, 5, 6, 7, 8, 9, 10]`, with no external producer events. Their
production source is
`deps/stwo-zig/src/frontends/circuit/witness/trace.zig`: `U_VAR_IDX = 2`,
and `lookupSum` consumes that `u` address plus eight output addresses
`U_VAR_IDX + 1 + index`. The Lean theorem
`feeder_matches_pinned_native_fixture` separately compares this list with
`PinnedNativeSquare4Witness.trace.externalUses.map Prod.fst` and checks that
the fixture has no external yields.
The kernel checks that the bounded ledger passes and that both event sides
have length 1033.

`pinned_square4_balanced_for_coherent_wire` then proves exact ideal Gate
balance for **any** single coherent address-to-QM31 value map used by those
rows and feeder events. This isolates the multiplicity/address accounting
from the secret witness values. The separate native base witness already
checks its concrete main rows; this address theorem does not establish a
universal source-to-native fixed-roster correspondence, native main-column
coherence, LogUp soundness, or proof commitment authentication. The feeder
comparison is against a generated fixture; it does not prove that the native
verifier always derives those events.
