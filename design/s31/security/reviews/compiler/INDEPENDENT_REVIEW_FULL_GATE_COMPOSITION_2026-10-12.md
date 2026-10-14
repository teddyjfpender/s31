# Independent review: full modeled direct-Gate composition

Reviewed commits `4ae8dbc`, `62e2135`, `af4d432`, `2b569d6`, `1c09e22`,
and `280b7e6`, plus their immediate checker dependencies. This is a
theorem-contract and source review. I did not run a broad formal build while
the final aggregate gate was in progress. The formal agent's focused
`LEAN_NUM_THREADS=1 lake build` and `lake env leanchecker -v` for
`CheckedDecodedGateLedgerCorrespondence` both passed; the root reported the
same focused build and replay result for the high-level `List UInt8` corollary.

## What the new results prove

[`CheckedFullLocalArithmeticComposition.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedFullLocalArithmeticComposition.lean)
joins the source/public projection (`n + 25` cells) to a supplied, successfully
checked constant island (`487 - n` cells). Source admission supplies `n ≤ 16`.
The row-position proofs show that the two lists are disjoint, have no repeated
physical positions, and cover every row `0..511`. `checked_joined_fixed_matches`
then proves the synthetic decoded trace has the checked flags, addresses, and
multiplicities at all 512 positions. This is full **modeled** fixed-cell
coverage, conditional on `NativeConstantIslandCertificate.check = true`; it
does not compare the list with an arbitrary production compiler output.

`joined_local_arithmetic_of_projected_wire` combines the honest projected
cell arithmetic with checker-derived island cell arithmetic under one merged
address-to-value map. Its direct version explicitly assumes source/public
boundary facts and `SharedAgreement` at any constant address used by a
projected cell. Its accepted-byte corollary obtains the projected witness
from the already proved byte-admitted source/public construction. The final
`allArithmeticRootsZero` follows from local `cellAccepts` on each joined
cell; the desired all-row result is not an input premise.

[`HonestConstantIslandAgreement.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/HonestConstantIslandAgreement.lean)
removes the shared-agreement premise for that accepted-byte corollary. It
proves each projected port lies below `33 + n`, so the only shared constant
addresses are `0`, `1`, `2`, `15`, `16`, `25+n`, `28+n`, and `31+n`.
`InputBoundary`, `OutputBoundary`, and the unit condition pin those projected
values; the island check supplies matching `SeedValues`. The final
`checked_direct_joined_local_arithmetic_no_agreement` still takes a supplied
island and a successful executable island check. It does not manufacture or
authenticate an island for every admitted program.

[`CheckedFullGateBalanceComposition.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedFullGateBalanceComposition.lean)
adds `CheckedGateAddressLedger.check joinedCells externalUses externalYields =
true` as an explicit premise. Its conclusion combines the same local witness
with ideal exact Gate event balance on the same merged wire. The balance
conclusion is derived by the bounded address-permutation checker; it is not
assumed as `balanced`. The external address lists remain caller supplied.
Neither the theorem nor the checker proves that those lists are the native
public feeder, or that accepted LogUp sums imply exact event balance.
The balance target is `gateRows joinedCells wire`, while local arithmetic is
stated on `trace joinedCells wire`. `nativeRows (trace joinedCells wire)` is
in physical row order; `joinedCells` lists projected cells before island
cells (the square4 projected source cells begin at physical rows 502 and 503).
A row-permutation/event-equivalence lemma is needed before the balance
result can be stated directly for the decoded trace. The subsequent
`CheckedDecodedGateLedgerCorrespondence` module supplies that lemma; its
scope is reviewed below.

[`CheckedDirectGateModeledComposition.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedDirectGateModeledComposition.lean)
packages the accepted-byte, checked-island, and bounded-address-ledger
premises into one theorem. It uses the no-agreement local witness and then
`CheckedGateAddressLedger.check_sound` on that witness. This entry point
does not hide the two executable checker premises or assume ideal `balanced`
itself. Its Gate result is for `gateRows joinedCells wire`; the separate
decoded-row permutation bridge transports it to physical row order.

[`CheckedDecodedGateLedgerCorrespondence.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedDecodedGateLedgerCorrespondence.lean)
proves each selected decoded row equals `gateRow wire cell` from the complete
roster's fixed-cell canonicality and the synthetic main-row constructor.
It proves the grouped cell rows permute the physical `nativeRows` order and
transports the ledger-derived balance across that permutation. No desired
`balanced` fact is assumed to establish the row permutation. Its final
`checked_joined_decoded_gate_balance` still has explicit successful source,
island, and ledger checks plus separately supplied external addresses.
The default synthetic `trace` stores empty external event lists. The module's
`traceWithExternal` and `checked_joined_trace_gate_balance` explicitly set
those fields to `wireEvents` of the caller's address lists, then state
balance using the decoded trace's own lists. This closes the model-level
field mismatch. It does not show that the caller's addresses or values are
the production public feeder or any authenticated proof opening.
The direct native [`lookupSum`](../../../../../deps/stwo-zig/src/frontends/circuit/witness/trace.zig)
uses reserved `u` address `2` and eight public word addresses `3..10`;
the high-level theorem does not fix its `externalUses` argument to these
addresses or prove the corresponding ledger check for every admitted source.

## Audit conclusion and remaining joins

I found no circular premise or model-level checker soundness error in the
reviewed compositions and decoded-row bridge. The high-level theorems are
universal over the admitted
**direct functional fragment**, conditional on the supplied island check
and, for Gate balance, the supplied address ledger check. Their source
parameters are `List Nat`; `CheckedDirectGateModeledComposition` now also
provides a `List UInt8` corollary that makes the literal-byte API explicit.

The production boundary remains substantial: prove or check that each source
program's native fixed roster equals `joinedCells`; bind one coherent native
main wire and exact public feeder events to the proof; connect compressed
lookup closure to ideal exact Gate/Chip events with a quantitative error
bound; and account for PCS/FRI authentication. The new theorems do not cover
the mixed 1–8-call chip compiler. They do not establish that every source
has a passing constant-island or ledger certificate.
The existential trace construction is honest-witness satisfiability evidence.
It is not a soundness theorem for arbitrary prover-supplied traces.

I also ran the short static cross-artifact check:

```text
python3 -B src/frontends/s31/tests/acceptance/compiler_correspondence/native_fixed_root_binding.py
```

It matched all 4,096 pinned square4 fixed cells and 512 address-indexed
values, and rejected six altered artifacts. The pinned preprocessed root is
`c0ea49c8f9027d5bdf9ce7a59ded3fb3a1f6b541a0ed1bb6c65b3c7d1175570a`.
This is a concrete fixture consistency check, not a theorem equating PCS
openings with the generated Lean trace.
