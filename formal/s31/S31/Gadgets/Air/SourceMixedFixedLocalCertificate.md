# Pinned mixed-chain schedule certificate

`SourceMixedFixedLocalCertificate.lean` assembles the `LocalPublicSchedule`
for the **`mixed_general_1` and `mixed_general_8` chain programs**. These
programs return four sums and four products of their initial and final
four-lane states. This certificate does not describe the separate
`GeneratedMixedEightV2` record program, whose eight public words have a
different meaning.

The certificate uses all 512 rows of each pinned native fixed-column export.
`SourceMixedFixedProducerCertificate.lean` reads every output address and
output multiplicity, omits zero-multiplicity rows from the logical producer
list, and kernel-checks that the native 512-variable producer scan succeeds.
The proof assumes the boundary has no separate baseline yields, as the
source-shaped chain model requires. The previous fixed schedule bridge checks
that **every** exported row has an output address below 512, including rows
whose multiplicity is zero.

`SourceMixedFixedOutputSchedule.lean` checks the exact physical rows for all
eight public outputs. For each lane, a pointwise mask reads packed sum or
product. Lanes 1–3 then multiply by an inverse basis constant. A final add
copies the scalar to public Gate addresses 3–10. The N=1 and N=8 proofs each
check the mask, inverse, and copy cell against the generated fixed-row list;
the same list was checked against the production compiler's full export. The
unit and inverse-unit **values** remain explicit `ValueAt` premises because
fixed columns only specify addresses and operations.

`n1_local_schedule` and `n8_local_schedule` therefore construct every field
of `LocalPublicSchedule` from these checked rows plus the following named
premises:

| Premise | Why the fixed export is insufficient |
| --- | --- |
| Decoded trace rows equal the source-owned canonical row list | Binds the fixed export to the actual Gate trace and source boundary. |
| No baseline yields | Ensures the complete logical producer scan contains exactly the active Gate rows. |
| Canonical call addresses, constants, first state | Binds chip-call metadata and the source input to the boundary. |
| Packed initial/final values, zero, unit and inverse-unit values | These are main-column and Gate-production facts, not fixed-column cells. |

The fixed export is a pinned native differential fixture. The theorem does
not establish that a succinct verifier authenticates the decoded trace or
that its accepted proof implies these premises. The separate native
full-trace auditor can check a concrete witness but is not a general
proof-to-premise theorem.

The follow-on [trace-owned boundary](SourceMixedDecodedBoundary.md) eliminates
the decoded-to-boundary row-list premise by constructing the canonical row list
from the decoded trace. Its pinned N=1/N=8 constructors also set the chain's
round count, call addresses, constants, and first input state by definition;
the remaining main-value and source/proof-binding obligations are explicit.

Focused kernel check:

```sh
(cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedFixedLocalCertificate)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Air.SourceMixedFixedLocalCertificate)
```
