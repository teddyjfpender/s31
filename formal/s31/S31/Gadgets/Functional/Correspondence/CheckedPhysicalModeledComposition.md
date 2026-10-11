# One physical modeled trace

`checked_u8_physical_modeled_trace` is the current end of the direct-Gate
modeling chain. Given literal source and normalized bytes, an input, a
constant-island certificate, and explicit public feeder/sink address lists,
three executable checks construct **one** 512-row decoded trace:

```text
checkRelation(source bytes, normalized bytes) = certificate
NativeConstantIslandCertificate.check(certificate, island, values) = true
CheckedGateAddressLedger.check(joined cells, feeder addresses, sink addresses) = true
                              ↓
        physical rows + external events from one coherent wire
                              ↓
  every physical row covered; selected fixed cells match;
  all installed local arithmetic roots vanish;
  selected output equals source denotation;
  decoded Gate rows balance the trace's own external events
```

The trace is constructed in Lean. It does **not** claim that an arbitrary
prover's committed columns equal it. The island and address-ledger checks are
conditional, and the supplied external addresses are not yet bound to the
native public component. LogUp compression, interaction consistency,
preprocessed/main commitment openings, FRI, and the verifier's quantitative
soundness bound remain separate obligations. The theorem covers the bounded
direct functional fragment; it is not a theorem for mixed chip programs.

Focused check:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.CheckedPhysicalModeledComposition
lake env leanchecker -v S31.Gadgets.Functional.Correspondence.CheckedPhysicalModeledComposition
```
