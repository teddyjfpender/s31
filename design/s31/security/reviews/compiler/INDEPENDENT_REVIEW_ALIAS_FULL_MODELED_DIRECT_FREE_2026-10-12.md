# Independent review: direct-free alias full modeled trace (2026-10-12)

**Revision:** `7b90caa`. **Result:** no flaw found in the stated conditional *modeled witness existence* theorem. It does remove the producer-only direct-source-spelling premise. It does not establish soundness of a native accepted proof.

## Premise and construction audit

`checked_alias_full_modeled_trace` takes exact three-file `checkAliasCanonical` admission, an executable constant-island check, and an executable bounded address-ledger check. Its statement has no `checkRelation`, direct source bytes, direct denotation, assumed arithmetic roots, assumed fixed matches, assumed `balanced`, or caller-supplied shared-wire agreement. The alias checker parses the source once and encodes the normalized relation and canonical IR from that parsed certificate. The alias public-boundary theorem obtains an eager execution and a coherent wire for the source, public input, and selected output, including an earlier selected producer followed by later executed producers.

The new shared-agreement lemma bounds every projected port below the island's fresh allocation and derives the eight shared seed values from the input/output boundary and checked island table. `mergedWire` therefore preserves projected values at all their ports and island values at all island ports. The proof establishes local arithmetic acceptance for every joined cell under that single assignment, including all 512 rows. The selected output stays outside the constant-address set, so merging cannot overwrite it. `InputBoundary` survives merging and pins the four public input scalars and their packing circuit.

The roster theorem derives 512 distinct in-range physical positions from admitted producer count, projected-row placement, and checked constant-row positions; it then proves complete coverage and a permutation with `0..511`. Canonical fixed words prevent field reduction from silently changing a declared address or multiplicity. `fixedMatches` is proved against `trace (joinedCells certificate island) wire`, whose fixed columns are **constructed from those same checked cells**. This is a correct internal consistency statement, not an independent native fixed-column equality.

The ledger checker compares bounded address multisets. Because every decoded row reads its main values from the same `wire`, the address permutation lifts to a QM31-valued Gate event permutation. The row-position permutation transfers that balance to the constructed trace's `nativeRows`. `traceWithExternal` sets the trace's external event lists to `wireEvents wire` of the two caller-supplied address lists. Thus the conclusion's Gate balance concerns the synthetic trace and its own supplied external events; it does not authenticate a native feeder or sink.

## Remaining soundness boundary

- `hisland` and `hledger` are real executable checks, but the theorem is conditional on their successful results. The alias byte check alone does not prove a checked island or suitable external address lists exist for every admitted source.
- The existential trace is built in Lean. The theorem does not show that a prover's committed columns, fixed preprocessed root, public boundary, external events, or queried openings equal that trace. The interaction columns are inherited from the synthetic trace and no LogUp/PCS/FRI verifier-soundness conclusion follows.
- The byte checker is a Lean parser/encoder model. Equality to the production Python/Zig parser, emitter, package artifacts, and verifier for arbitrary inputs remains a separate compiler-correspondence obligation.

**Checks:** inspected the complete `7b90caa` diff and the alias, constant-island, boundary-agreement, roster, trace, and ledger dependencies; searched the changed modules and immediate admission/ledger dependencies for `axiom`, `sorry`, `admit`, `unsafe`, and `native_decide` (none); `lake env leanchecker -v S31.Gadgets.Functional.Correspondence.AliasCheckedFullModeledComposition` exited 0 against the compiled module. No blocker found within the theorem's stated scope.
