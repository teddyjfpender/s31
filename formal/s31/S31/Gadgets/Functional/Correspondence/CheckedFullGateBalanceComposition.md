# Joining local AIR arithmetic with the Gate address ledger

`joined_local_arithmetic_and_gate_balance_of_projected_wire` combines two
separately checked facts about the same modeled 512-row direct Gate roster:

1. `joined_local_arithmetic_of_projected_wire` constructs one decoded trace
   with all 512 row positions covered exactly once, exact modeled fixed cells,
   vanishing local arithmetic polynomials, and the selected public output.
2. `CheckedGateAddressLedger.check` compares the fixed roster's operand reads
   and output multiplicities with supplied external feeder/sink addresses.
   Its soundness theorem proves ideal exact Gate event balance for **any**
   coherent address-to-QM31 assignment, so it applies to the same merged wire
   from step 1.

The theorem keeps the address-ledger result as an explicit premise for
arbitrary accepted programs. It also keeps agreement between the honest
source/public values and the checked constant-island values explicit. The
external address lists must be bound to the actual public component. Native
fixed/main commitment equality, LogUp soundness and PCS/FRI verifier
authentication are further correspondence obligations.
