# When a public lookup event must equal its Gate pin

The [statement audit](ControlGadgetStatementPins.md) finds the verifier's
eight public values and their addresses. Its Lean theorem previously took
`wire(3+i) = encoded(claim[i])` as an explicit premise. This continuation
derives that equality from a **conditional global Gate equation**. It also
derives the matched generic Gate AIR equations from positive physical rows.

## The equation and the ownership step

Each generic Gate row reads two `(address, value)` tuples and yields its
output tuple as many times as its fixed multiplicity says. Other components
can also supply Gate tuples. The public statement contributes eight reads:

```text
(3, encode(x))
(4, encode(result[0])), ..., (7, encode(result[3]))
(8, encode(0)), (9, encode(0)), (10, encode(0))
(2, fixed u)  # reserved ninth public Gate use
```

The installed LogUp closure is a rational sum in two challenges. In the
Lean model its row contributions, external reads, and external yields obey

```text
Σ rowContribution(row, α, z)
  + Σ reciprocal(external read, α, z)
  - Σ reciprocal(external yield, α, z) = 0.
```

The existing Gate challenge theorem says that, if addresses and event
counts are canonical and `(α,z)` avoids its explicit exceptional sets,
this equality forces **exact event multiset balance**. Exact balance puts
every public read in the produced event list. A checked one-producer roster
then makes the value at each address unique. Consequently the public word
at address `3+i` equals the Gate wire at `3+i`.
Lean checks that this eight-then-`u` event list maps exactly to the existing
seven-word model of the native `trace.lookupSum` loop, including its fixed
relation tag and padded seventh coordinate.

`ControlGadgetGlobalGateJoin.lean` makes that argument for all eight slots.
For every matched control Gate, a `positiveOwner` premise identifies its
actual physical row, operation flag, two input addresses, output address,
positive multiplicity, and accepted local AIR. The theorem uses exact
balance and unique ownership to transport that row's values onto one shared
wire map. It then derives the `AirRows` premise of the earlier control
statement theorem. The composed theorem concludes the claimed input is `x`,
the four claimed result words are the selected branch's inverse lanes, and
each selected lane times its claimed inverse is one in M31. A separate
rejection theorem proves that a changed public word cannot satisfy good
global closure if a different positive producer value owns that address.

## What is source checked

`scripts/compiler/control_gate_pin_roster_audit.py` verifies the sealed
package and the earlier exact control topology, then captures fixed columns
from its native prover. In the current package, 329 positive QM31 rows have
distinct output addresses. Physical rows 4–11 own public addresses 3–10,
each with multiplicity one. Five positive conversion outputs are distinct
and do not collide with these QM31 outputs. The checker also compares every
physical row's one-hot operation flag and input/output addresses with the
captured `add`/`sub`/`mul`/pointwise graph in physical order. Tests zero a public row's
multiplicity, duplicate an output owner, collide a conversion output, and
swap two ABI pins, alter a flag, and change a graph row; each mutation is rejected.

This executable check covers the observed QM31 and M31-to-u32 producer
columns. It does **not** prove that every possible Gate-yielding component
is covered by the Lean `externalProducerCoverage` premise or that an
arbitrary accepted proof authenticates the asserted row values. The
per-row AIR, complete external producer roster, global rational equation,
good challenge event, and PCS/FRI authentication remain explicit theorem
premises. The native verifier's eleven component claims and public output
sum are source modeled elsewhere, but the complete native claim-to-exact
Gate event projection remains an open compiler/LogUp edge. This release
blocker is not discharged by this theorem.

## Focused checks

```sh
python3 scripts/compiler/control_gate_pin_roster_audit.py "$PACKAGE"
python3 -m unittest scripts.tests.test_control_gate_pin_roster_audit
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.ControlGadgetGlobalGateJoin)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.ControlGadgetGlobalGateJoin)
```
