# Derived fixed roster and arbitrary physical traces

`DerivedRosterArbitraryTrace.lean` connects two existing pieces of the bounded
four-lane direct Gate proof:

1. Exact source, normalized JSON, and canonical IR bytes select the same
   positional certificate. The constant island checker validates the other
   physical rows. Its output-use multiplicities are computed from scheduled
   reads, rather than taken from the island input.
2. The arbitrary-trace source soundness theorem turns locally valid physical
   rows, ideal exact Gate balance, and public boundary events into the source
   output.

For **any** 512-row decoded trace, the new theorem checks the full 512-row
roster and transfers its 4096 fixed-cell obligations into the arbitrary-trace
proof. It also proves each row has a roster entry whose output multiplicity
equals the global scheduled read count. If the remaining runtime premises
hold, the trace's public claim equals the denotation of the original `.s31`
bytes. This applies to alias spellings and source programs with dead rows.

The runtime premises remain explicit: the decoded trace's fixed cells match
the roster, all installed local arithmetic roots vanish, active producer
values are unique, the constant/basis events and public pins have their
specified values, and ideal Gate uses and yields balance exactly. The theorem
does **not** derive those conditions from the native verifier Boolean or prove
native Python/Zig lowering, fixed commitment authentication, LogUp reduction,
PCS/FRI soundness, or Fiat–Shamir soundness. It is one conditional compiler
correspondence join, not an end-to-end proof.

Focused check:

```sh
cd formal/s31
lake env lean S31/Gadgets/Functional/Correspondence/DerivedRosterArbitraryTrace.lean
```
