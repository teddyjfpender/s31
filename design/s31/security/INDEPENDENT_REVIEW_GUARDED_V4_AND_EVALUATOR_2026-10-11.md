# Independent review: guarded V4 provenance and direct Gate evaluator cells

Reviewed S31 `fc5527bdff7c88a6614382698046e8550d758268` and engine
`149c23803f9ba01703ff0192e63a696dddf69c63` against their source-pinned
V4 and conditional compiler-correspondence claims. This is a source and test
review, not a cryptographic proof or a claim that all verifier paths were
audited. I found no new false-proof admission in the sealed V4 entrypoint.

## Findings

### P2: guarded engine provenance is still caller-authorized for circuit slot 0

`direct_many_provenance.validate` checks the source-byte digest, pinned bundle
digest, a pinned direct-circuit source hash, and recomputed native chip/bridge
program digests. For circuit slot 0 it only compares the slot's
`program_binding_sha256` with the supplied descriptor's copy
([engine `direct_many_provenance.zig:52-62`](https://github.com/teddyjfpender/stwo-zig/blob/149c23803f9ba01703ff0192e63a696dddf69c63/src/integrations/circuit_cpu/direct_many_provenance.zig#L52-L62)).
It never derives that value from the pinned bundle. It also does not validate
`SelectedSchedule.manifest_digest`; both fields are publicly mutable in the
in-process schedule ([engine `direct_many_schedule.zig:98-100`](https://github.com/teddyjfpender/stwo-zig/blob/149c23803f9ba01703ff0192e63a696dddf69c63/src/integrations/circuit_cpu/direct_many_schedule.zig#L98-L100)).
Jointly replacing both slot-0 hashes, or changing only the manifest digest,
therefore passes this guard even though one-sided mutations are tested.

This **does not admit a false proof through sealed V4**: S31 regenerates the
source topology, selected AIR, typed manifest, and descriptors in `inspectMany`
([`bounded_compiled_binding.zig:384-471`](../../../src/frontends/s31/runtime/bounded_compiled_binding.zig#L384-L471));
`verifySourceBound` rebuilds that inspection, checks the envelope identity and
calls the guarded adapter before accepting proof bytes
([`many_native_package.zig:122-157`](../../../src/frontends/s31/runtime/many_native_package.zig#L122-L157),
[`many_native_package.zig:184-198`](../../../src/frontends/s31/runtime/many_native_package.zig#L184-L198)).
The guarded engine adapter must remain an internal helper, not a general
standalone authenticated-source verifier.

The engine can recompute the **slot-0 AIR program hash** without parsing S31:
the algorithm is full pinned bundle bytes, selected bundle index `1`, and each
rebound selected part's semantic hash under `S31-DIRECT-GATE-PROGRAM-V1`
([`component_manifest.zig:303-316`](../../../src/frontends/s31/runtime/component_manifest.zig#L303-L316)).
Move or share that computation at the guarded adapter and compare it with the
slot-0 descriptor. Canonical source node IDs and the full manifest digest do
require S31 parser/compiler/manifest semantics. Keep their regeneration in a
verifier-owned S31 wrapper and add negative controls for joint slot-0 mutation
and manifest-only mutation. `SelectedSchedule` being mutable is acceptable only
while the wrapper remains the sole proof-byte admission path.

### P3: boundary status text understates the current test matrix

The general-boundary design says counts 5-7 remain open
([`GENERAL_AUTHENTICATED_CHIP_BOUNDARY.md:9-13`](../language/GENERAL_AUTHENTICATED_CHIP_BOUNDARY.md#L9-L13)),
while `many_native_package.zig:313-390` runs honest native proofs and each
claimed-sum mutation for every count 2-8. Update the status and distinguish
native acceptance coverage from independent soundness and confidentiality.
This is a documentation accuracy issue, not a proof acceptance issue.

## Lean bridge and fixture scope

`DirectGateEvaluatorCells.lean:144-163` proves the raw Gate interaction result
only under explicit equalities between installed evaluator outputs and the
modeled pair/last formulas, authenticated zero residuals at every row, and
public claimed-sum closure. The nine arithmetic residuals are checked by a
separate theorem (`:68-75`); they are not implied by the interaction theorem.
`DecodedDirectGateTrace.lean:25-35` leaves the previous-row permutation and
external event lists abstract. These are visible premises, not hidden axioms.

The fixture exporter builds arithmetic cells from a documented source vector
but creates synthetic interaction and previous-row cells
([`export_s31_direct_gate_evaluator_fixture.py:153-177`](../../../scripts/export_s31_direct_gate_evaluator_fixture.py#L153-L177)).
Its Python equations and Lean `by decide` results agree for those values;
neither checks actual proof openings or executes the installed `STWZEVA/1`
bytecode. `correspondence.py:602-623` pins fixed/main/interaction spans and
selected component shape, while `:387-524` independently replays the complete
value-free Gate schedule. Acceptance mutates all three span classes and
rechecks the fixture (`acceptance_compiler_correspondence.py:188-222`). The
documentation (`GATE_LOGUP_NATIVE_REDUCTION.md:227-275`) states the remaining
installed-evaluator, mask, row-authentication, and PCS obligations accurately.

No circularity was found in the stated *bounded package/row replay* claim:
source bytes are parsed independently, normalized bytes and native topology
are compared, and the fixture checks a separately written Lean cell model.
There would be claim overreach if this fixture were presented as a proof of
installed evaluator semantics or full compiler correspondence.

## Decision

- **Go** for the **experimental sealed V4** guarded increment, with the
  source-pinned S31 verifier as the required proof-byte entrypoint.
- **No-go** for advertising the guarded engine adapter as a standalone general
  authenticated circuit-to-chip boundary until slot-0 and verifier-owned
  manifest provenance are enforced at its documented boundary.
- **Go** for the **conditional direct Gate evaluator-cell bridge** as a bounded
  formal/testing increment. **No-go** for a full compiler-correspondence or
  native soundness claim based on this bridge or synthetic fixture.
