# Independent review: derived roster for arbitrary Gate traces

Reviewed `DerivedRosterArbitraryTrace.lean` at `b06312b` with its dependencies. **No blocker found for the stated conditional theorem.** The focused Lean file compiled, and a separate Lean evaluation on the pinned case07 fixture returned `true` for `AliasDerivedGateMultiplicities.check case07Certificate constantCells nativeValues` and `512` for the derived joined-roster length.

## Premises and row coverage

`hcheck` is an executable conjunction of the constant-island certificate, projected multiplicity equality, and the bounded address ledger. `derivedIsland` erases the input island multiplicities and recomputes them from the joined read schedule plus nine public feeder addresses. The theorem does **not** assume the claimed count equality: `checked_joined_has_read_counts` derives it from `hcheck` for both projected and island cells. The case07 evaluation shows this check is satisfiable on one pinned fixture, although it is not an arbitrary-trace witness.

`checked_alias_joined_roster_complete` derives 512 cells, pairwise distinct row indices, and every index below 512 from byte admission and the island row-position check. Cardinality then gives an entry for each `Fin 512` row. `hfixed` matches every roster entry to the decoded trace's selector, three addresses, and multiplicity. Thus every physical row has its fixed words covered; no row is left to an unquantified padding case. The theorem's output presents existence per row; uniqueness follows from the imported roster theorem, though it is not restated in the output.

## Scope of the source claim

The `some claimed` conclusion calls the existing arbitrary-trace source theorem. Its non-source premises remain explicit: full-roster fixed-cell agreement, vanishing local arithmetic roots, unique produced values, designated constant and basis events, input and output pins, and **ideal exact Gate balance**. In particular, the supplied constant-island `values` table is locally checked but is not shown here to equal the decoded trace's main-column values; the event facts make the needed values explicit. The proof extracts projected fixed agreement from `hfixed`; the extra island fixed agreement establishes the full-roster output rather than replacing those runtime premises.

This theorem does not derive `hfixed`, `RuntimeFacts`, or `hbalance` from native verifier acceptance. It does not authenticate committed rows or prove LogUp, Fiat–Shamir, PCS/FRI, or a complete compiler-to-native correspondence. A future end-to-end theorem must discharge those premises for authenticated openings. The module and companion prose state these limits accurately.

## Checks

```text
lake env lean S31/Gadgets/Functional/Correspondence/DerivedRosterArbitraryTrace.lean  # exit 0
lake env lean /private/tmp/s31-derived-arbitrary-review-case07.lean                    # true; 512
```
