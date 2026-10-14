# Independent review: admitted alias joined fixed roster (2026-10-12)

**Revision:** `1c3c7ad`. **Result:** no flaw found in the stated *modeled fixed-roster* theorems. This review is static; the theorem author already ran a focused Lean build and kernel check. I deferred a second Lean run while the parent worktree measured the native V20 cost study.

## Premises and nonvacuity

`checked_alias_joined_roster_complete` requires the exact three-file `checkAliasCanonical` result and a successful `NativeConstantIslandCertificate.check` on an island and value table for the **same** certificate. `checked_alias_canonical_bytes_sound` extracts a parsed alias source, normalized-byte identity, canonical-IR identity, and `checkAliasRelation`; the last fact supplies the parser's 16-producer bound. There is no `checkRelation` premise for a separately written producer-only source in either new theorem or in the new budget-only disjointness lemma.

The premises are satisfiable for an actual alias example: `GeneratedNativeSourceCells.case07_source_to_native_cells.1` proves exact three-file admission for the eight-producer case07 source, and `Alias8ConstantIslandCertificate.alias8_constant_check` proves its 479-cell island check. The existing `Alias8CompleteModeledTrace` separately assumes a direct spelling for its larger arithmetic/lookup theorem; that premise does **not** enter this new roster proof.

## Row and fixed-tuple argument

`checked_alias_projected_rows` supplies distinct, bounded projected source/public rows. `checked_rows_count` equates the island row list with `constantPositions` and gives its `487 - n` length. `constant_positions_nodup` and `projected_constant_rows_disjoint_of_budget` establish distinct rows within and across the lists; the latter uses only the certificate's producer bound and row bands. The projected length is `n + 25`, hence the joined list has 512 rows. Each row is below 512, so a 512-element duplicate-free list covers all `Fin 512` positions. This is a valid finite-cardinality argument, including the endpoint bounds for the constant-add, subtraction, and multiplication bands.

`checked_alias_joined_fixed_matches` derives canonical fixed words for projected cells from alias admission and for island cells from the island checker. `zeroTrace_fixed` then proves selectors, addresses, and multiplicity of each joined cell match `trace (joinedCells certificate island) wire` at its unique row. The `wire` is arbitrary because this theorem concerns only fixed columns. It is the **same constructed trace** for every joined cell; the result does not establish arithmetic roots, input/output semantics, or lookup balance by itself.

## Boundary that must remain explicit

The trace's fixed columns are built from the supplied `joinedCells` list. Neither theorem identifies that list with the native preprocessed fixed columns, the preprocessed commitment root, or authenticated proof openings. In particular, `ConstantCellSound` only requires `cell.mults < p`; it does not pin an island cell's multiplicity to the native exporter. A different canonical island multiplicity can still pass this checker, so the present theorem must not be cited as native fixed-column equality or Gate multiset balance. Those need a separate native binding and ledger proof. This is a scope limitation of the existing island contract, not a counterexample to the new conditional roster theorem.

**Checks:** reviewed the changed proof and direct dependencies, exact case07 admission and island witnesses, and searched the two changed Lean modules for `sorry`, `admit`, `axiom`, and `opaque` (none). No native or Lean replay was run in this isolated worktree.
