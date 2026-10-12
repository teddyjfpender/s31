# Independent review: public input boundary in complete modeled traces

**Reviewed commit:** `7cd252a` (`Preserve public input boundary in complete modeled traces`).

**Result:** Pass for the stated synthetic-trace theorem. I found no circular or vacuous input-boundary premise.

`merged_input_boundary` starts with the `InputBoundary` of the independently constructed projected source witness. `mergedWire` replaces only `constantAddress` entries with the checked island value table. Every address used by `InputBoundary` is below 23 and differs from address 1. In that range, the only replacement candidates are 0, 2, 15, and 16. The original boundary pins those four values; `SeedValues` pins the island table to the identical zero and basis values. Thus `merged_input_prefix` proves equality of the two wires at each input pin, copy-row port, and pack-row port, and `merged_input_boundary` transports all eight fields of the boundary without assuming a new one.

The `SeedValues` premise in the complete direct theorem is extracted from `NativeConstantIslandCertificate.check_sound`; its Boolean checker includes seed equality and checked constant-cell arithmetic. The projected boundary comes from `checked_direct_public_boundary_exists` under exact byte admission. `HonestConstantIslandAgreement.checked_direct_joined_local_arithmetic_no_agreement` derives the shared-port agreement from those boundaries and the seed check. Neither `InputBoundary` on the merged wire nor an arbitrary shared-wire equality is a caller premise. The case07 and square4 instances discharge their source, island, and address-ledger checks with concrete definitions.

The conclusion keeps one existential `wire` for the selected output, `InputBoundary`, and `physical = traceWithExternal ... wire ...`. `traceWithExternal` retains `trace`'s `mainAt` columns, which read that same wire at each cell's three addresses. The case07 alias bridge changes only the source-denotation proof using a separately checked producer-only spelling; it forwards the same direct witness. The square4 bridge similarly forwards the same witness. Hence the new public boundary applies to the same modeled value assignment and physical trace in both instances.

I ran `lake env lean S31/Gadgets/Functional/Correspondence/CheckedFullLocalArithmeticComposition.lean` successfully on the reviewed source and inspected the changed theorem chain for `sorry`, explicit `axiom`, `unsafe`, and `native_decide` uses; none occur in the changed modules. This is a source elaboration check, not a fresh full-project kernel audit.

**Scope:** The theorem constructs a synthetic trace and proves a value-level public input boundary. It does not identify its `physical.main` with openings of an accepted native commitment, authenticate the external Gate feeder lists, or prove PCS/FRI/LogUp soundness. Those separate obligations must remain explicit when the result is cited.
