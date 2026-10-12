# One-call chip manifest binding: independent negative control

The direct-chip verifier derives a component manifest from the embedded S31
relation, circuit geometry, native chip AIR, and optional private bridge AIR.
`mvp_runtime.validateCompiledKey` checks the generated manifest against the
supplied key before using it to verify a proof. The native proof verifier then
inspects the exact live AIR handles before postcard decoding and uses those
handles for the final STARK verification.

## Test gap found

The existing `acceptance_component_manifest_chip.py` control changed a key's
component manifest but left `manifest_precommitment_sha256` unchanged. Such a
key fails a simple digest consistency check, so that rejection did not by
itself demonstrate source-derived AIR binding.

The repaired control independently computes the typed manifest digest, the
`S31-DIRECT-CHIP-MANIFEST-TRANSCRIPT-V2` effective source digest, and the
direct circuit identity hash. It first checks that this calculation reproduces
the honest native key. After a mutation, it updates the key's dependent chip
specification, private boundary, digest, circuit hash, and manifest circuit
hash. The resulting false key is internally coherent. A verifier built with
that key must still reject it with `InvalidVerificationKey` because its
embedded source reconstructs the authentic manifest.

The focused native cases change the private bridge's AIR program-binding
digest, a private output endpoint address, and a fixed preprocessed column's
value digest. The same acceptance path separately checks package sidecar and
cost-report tampering, an honest proof and altered public claim, malformed
postcard wires, and a prior proof-envelope version. Fast unit tests check that
the forged keys are actually re-sealed and differ from the honest key.

## Boundary of this result

This is an exact-binding negative test for the current one-call direct-chip
profile. It does not establish compiler source-to-AIR correspondence, the
correctness of the native chip or bridge AIR equations, or PCS/FRI soundness.
It does not cover the general multi-call mixed boundary registry.
