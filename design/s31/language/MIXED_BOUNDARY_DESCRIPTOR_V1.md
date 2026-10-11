# Bounded mixed component descriptor v1

Status: **source-inspected descriptor for 1–8 calls; native proof bytes only
for the separate fixed N=3 mixed profile**. This descriptor is a typed audit
and admission contract, not a verification key or a cryptographic transcript.

For N calls, source compilation yields a circuit slot followed by N ordered
`(chip, bridge)` pairs. Calls 0 and 1 use the registered pair AIRs; later calls
use the registered many AIRs. The [N=4 source example](../../../src/frontends/s31/examples/boundary/mixed_four.s31.json)
starts from a private four-word input, applies four repeated square-and-add
functions, and exposes two four-word outputs. Its roster has nine slots:

| Proof and sum index | Source | Call |
| ---: | --- | ---: |
| 0 | Bound circuit AIR | — |
| 1, 2 | Pair chip, pair bridge | 0 |
| 3, 4 | Pair chip, pair bridge | 1 |
| 5, 6 | Many chip, many bridge | 2 |
| 7, 8 | Many chip, many bridge | 3 |

`inspectSource` re-parses literal S31 source, rebuilds its canonical IR and
compiled endpoint addresses, validates the V4 source provenance, queries the
registered pair and many verifier AIR handles, checks the complete live PCS
geometry, and computes a selected schedule digest. The descriptor copies that
source digest and selected manifest digest and records an ordered versioned
component contract: proof index, sum index, call ID, bundled AIR identity or
native program ID (1/2 = pair chip/bridge, 3/4 = many chip/bridge), and
program binding digest. Its own SHA-256 digest is
canonical over those fields and has no independent authority.

`requireSource(candidate, source, AIR)` repeats reconstruction and requires
exact typed equality. Reordering chip and bridge roles, dropping a call,
changing a native program binding, or recomputing the candidate digest after
either alteration does not pass. Changed public outputs, a changed private
computation, and changed input visibility also fail against the original
descriptor. The tests use a four-call source with 80 main and 120 interaction
columns; these are geometry observations, not whole-prover cost measurements.
The generated source matrix also checks all counts 1–8 with chained live calls.
It observes `12 + 17N` main columns, `8 + 28N` interaction columns, contiguous
slot offsets, and the canonical pair/pair/many role policy. Each count rejects
a resealed program binding, role swap, and truncated roster. These formulas
describe the tested bounded source family, not an arbitrary S31 program.

The N=3 `verifyEmbeddedWithDescriptor` entrypoint checks this descriptor
against compile-time source and official AIR bytes before its existing
bounded proof decoder and native verifier. Every tested N≠3 count is rejected
as `UnsupportedMixedProofCount`; there is no other mixed proof serializer or
native verifier yet. The source-inspected descriptor does not prove lookup, PCS, or
FRI soundness, full compiler correspondence, or witness confidentiality.
