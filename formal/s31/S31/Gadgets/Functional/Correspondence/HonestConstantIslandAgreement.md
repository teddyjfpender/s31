# Honest source/public and constant-island agreement

`HonestConstantIslandAgreement.lean` closes the shared-value premise in the
modeled 512-row direct-Gate arithmetic composition.

The projected source, input-pack, and output-unpack cells use addresses below
`33 + n`, where `n` is the admitted instruction count. The constant island
can share only eight addresses in that range:

| Address | Value | Why the public/source wire agrees |
| --- | --- | --- |
| `0` | zero | input boundary |
| `1` | basis unit 0 | output mask basis |
| `2` | basis unit 2 | input basis |
| `15` | basis unit 1 | input basis |
| `16` | basis unit 3 | input basis |
| `25+n` | inverse basis 1 | output inverse boundary |
| `28+n` | inverse basis 2 | output inverse boundary |
| `31+n` | inverse basis 3 | output inverse boundary |

The independently checked island's `SeedValues` pins the same values in its
finite value table. `honest_extended_shared_agreement` proves this directly
for the constructed `extendedWire`. The stronger
`checked_boundary_shared_agreement` proves it for any wire satisfying the
checked source's input/output boundary contracts. The source-byte admission
derives the port bounds; the caller does not provide them.

`checked_direct_joined_local_arithmetic_no_agreement` combines these facts
with `CheckedFullLocalArithmeticComposition` to construct one modeled
512-row trace with exact row coverage, fixed-cell matches, zero local
arithmetic roots, and the selected public output. Its only data premises are
successful exact source/normalized byte admission and a successful
`NativeConstantIslandCertificate.check` on the supplied island cells/value
table. The island check is conditional: the theorem does not construct an
island for every source.

This proof does **not** bind modeled fixed cells or values to the production
native emitter's committed columns, establish Gate event balance or
authentication, or prove PCS/FRI/verifier behavior. These are separate
obligations. The bound and agreement apply to the bounded direct-Gate
fragment, not all S31 programs.

Focused verification:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.HonestConstantIslandAgreement
lake env leanchecker -v S31.Gadgets.Functional.Correspondence.HonestConstantIslandAgreement
```
