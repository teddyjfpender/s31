# Exact Gate balance from a fixed-address ledger

`CheckedGateAddressLedger.lean` reduces the ideal Gate balance problem for an
address-coherent circuit to a finite check on **fixed addresses and output
multiplicities**. `readAddresses` lists the two input addresses of every
gate plus external consumer addresses. `producedAddresses` repeats each gate
output address by its fixed multiplicity plus external producer addresses.
The executable `check` tests whether these address lists are permutations.
It first limits the roster to 512 rows, the sum of fixed output
multiplicities to 2048, and each external list to 1024 events. That bound is
checked before any `List.replicate` expansion.

`check_sound` proves that a successful address check implies exact
QM31-valued `GateLookup.balanced` for *any* wire assignment, provided each
gate's input and output values are read from that same address map and the
external events use the same map. This removes witness values from the
balance checker. A one-gate example passes; increasing its output
multiplicity without adding a read fails.

`PinnedGateAddressLedger.lean` checks the complete pinned native square4
fixed roster with its nine pinned feeder addresses: 512 rows, 1033 reads,
and 1033 yields. This is a nonvacuous complete-fixture check. For arbitrary
admitted source, the next join must combine the selected source/public cells
with the constant island certificate, establish the exact native feeder
address list, and show the full list passes `check`. It must also show actual
native main rows agree with one wire. The theorem does not assert that
committed columns or LogUp openings equal the checked list, or prove PCS/FRI
soundness.
