# Joining source, public, and constant Gate rows

The direct Gate AIR has 512 physical rows. Checked source bytes determine a
projected source/public roster of `n + 25` cells for `n ≤ 16` instructions.
`NativeConstantIslandCertificate.check` accepts the remaining `487 − n`
constant/padding cells. The Lean theorem `checked_joined_roster_complete`
proves their row positions are distinct and in bounds, and that each physical
row 0 through 511 has one modeled cell. `checked_joined_fixed_matches` proves
that the synthesized trace contains each checked selector, address and
multiplicity at that physical row.

The source/public witness and the constant-island value table are built
independently. At any address used by both, they must hold the same QM31
value. `SharedAgreement` states this at the three ports of each projected
cell. `mergedWire` then uses the checked constant value at allowed constant
addresses and the honest source/public value elsewhere.

Under this agreement, `joined_local_arithmetic_of_projected_wire` joins one
concrete honest public/source witness to the checked island. Its corollary
`checked_direct_joined_local_arithmetic_exists` takes a stronger universal
agreement premise and obtains the witness from accepted bytes. Both construct
a decoded 512-row trace whose installed arithmetic polynomials all vanish,
and preserve the selected public output. They do **not** establish that the
modeled joined fixed columns equal arbitrary production fixed columns, that
the complete Gate lookup balances under the merged witness, or that PCS/FRI
authenticates the trace. The address-ledger checker and production binding
are distinct steps.
