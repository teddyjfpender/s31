# Independent review: mixed Gate and chip event signs

Date: 2026-10-11. Scope: the one-to-eight-call direct mixed source family and its conditional Lean event model. This is a source review, not a proof that native verifier acceptance implies the Lean premises.

## Native sign ledger

| Event | Native contribution to the claimed-sum fold | Source |
| --- | ---: | --- |
| Qm31 row input 0 and input 1 | `+1` each | `deps/stwo-zig/src/frontends/circuit/witness/components.zig`, `qm31_ops.lookups`; `air_eval/manual/circuit.zig`, `evaluateQm31Ops` |
| Qm31 row output | `−multiplicity` | Same two sources |
| Eight public output tuples at addresses 3–10 and fixed `u` at address 2 | `+1` each | `deps/stwo-zig/src/frontends/circuit/witness/trace.zig`, `lookupSum`; `statements/circuit_statement.zig`, `publicLogupSum` |
| Chip row input and successor output | `+1`, `−1` | `deps/stwo-zig/src/integrations/circuit_cpu/tagged_pair_chip.zig` and `tagged_many_chip.zig`, `FillContext.fill` |
| Bridge's eight Gate tuples | `+1` each after summing its 16 constant rows | `tagged_pair_bridge.zig` and `tagged_many_bridge.zig`, `FillContext.fill` |
| Bridge initial chip endpoint and final chip endpoint | `−1`, `+1` after summing 16 rows | Same bridge sources |

The verifier adds the circuit claim, public tuple reciprocals, and every chip and bridge claim, then requires zero (`direct_many_arithmetic.zig`, `verifyBorrowed`). Therefore the source-shaped native closure is

```text
reciprocalSum(circuitUses ++ chipAndBridgeUses)
  = reciprocalSum(circuitYields ++ chipAndBridgeYields).
```

Here `SourceMixedRoster.GateSource.circuitUses` contains arithmetic input, public feeder, and bridge Gate events. `circuitYields` contains arithmetic output and other producer events. `IndexedManyTaggedTupleBridge.jointUses` contains chip row inputs and bridge final endpoints; `jointYields` contains chip row outputs and bridge initial endpoints. The helper name `publicOutputYields` in `TaggedPairSourceCorrespondence.lean` is historical: its tuples have **positive native use** sign. `Boundary.publicFeeder_native_events` equates tuple contents, not signs.

## Reviewed repair

The earlier `SourceMixedPath.lean` rational-closure premise paired `circuitYields ++ jointUses` against `circuitUses ++ jointYields`. Although an exact permutation in that order still gives separate Gate and chip balances after relation-tag projection, its reciprocal identity is not the native claim fold: compressed Gate and chip terms could cancel across tags. The patched `hjoint` and `hclosed` now pair `circuitUses ++ jointUses` against `circuitYields ++ jointYields`. Gate and chip projection are performed on that native order.

The earlier good-challenge premise used raw `badPairs7`. That set includes every non-pole challenge when an honest witness already has exact event balance, so it could not be instantiated on an honest trace. The patched conditional theorem uses `imbalancePairs7`, defined as empty for exact balance and as the false-closure set for imbalance. `exact_joint_has_no_imbalance_pairs` makes honest-trace non-vacuity explicit. A numerical soundness bound still requires the separate event-count bounds and a proof linking the native Fiat–Shamir challenge to the modeled exception event.

## Earlier pair theorem circuit sign convention

`TaggedPairSourceComposition.source_pair_claims_imply_exact_events` states its circuit-claim premise as `sum(circuitPositiveInputs) − sum(circuitNegativeOutputs)`. These abstract parameters now name the native Qm31 orientation: positive physical row-input uses and negative physical row-output yields. This renames only the theorem binders; it does not provide native compiler-to-event correspondence. Downstream pair modules still use the older abstract names `circuitYields` and `circuitUses`; a caller must pass positive physical row-input events to the former. The mixed repair does not instantiate the pair theorem.

## Remaining limits

The repaired mixed theorem starts from exact event balance or a closed modeled reciprocal identity outside a modeled exception set. It does not derive either premise from a successful STARK verification. It also takes the compiler-to-Lean row and event roster, local AIR acceptance, unique produced values, selected pack and public-tail rows, and source address equality as premises in the downstream theorems. In particular, the producer scan in `SourceMixedProducerCheck.lean` must cover every active row and every baseline producer; native `validateUniqueProducers` scans declared outputs and deliberately excludes permutation scratch addresses. For this reviewed direct arithmetic family, the circuit has no permutation operation, but the full native-to-model roster correspondence has not been formalized. The Lean `CanonicalAddress` type proves addresses are below the M31 modulus; it does not itself prove that they are below the compiled circuit's `n_vars`. The source's checked lookup budget bounds native occurrences; transferring its bounds to the Lean event lists remains a separate obligation.
