# Independent review: mixed manifest private endpoint join

Reviewed commit: `0c9784b0548e83c94147d46f8022abcdfb88414a` (2026-10-12).
Scope: `mixed_boundary/inspection.zig` and `registry_manifest.zig`.

## Result

No blocking defect found in the new endpoint-to-program-binding check. For
every non-circuit slot, `fromSchedule` obtains the canonical call ID and source
kind from `registry.forSlot`, then recomputes the slot binding with
`nativeProgramBinding(source_kind, slot.air_source_sha256, schedule.calls[id])`.
The hash includes the native kind, AIR source digest, call and source node IDs,
rounds, constant, and all four input and output addresses. The producer in
`inspectSource` calls that same function with the same `Call` when it creates
the chip and bridge slots. Its call addresses come from the V4 manifest's
compiled endpoints. `compileSourceTopology` obtains those addresses from the
direct bounded compiler's Gate map; `attachCompiledEndpoints` checks call,
node, rounds and constant identity before installing them in that manifest.
`selectedFromSource` then transfers the typed manifest calls into the native
plan without changing those addresses.

The three new negative controls recompute the selected-schedule diagnostic
digest after changing a many-call input address, changing a many-call output
address, or changing a pair-bridge binding. They first assert the digest is
current, then observe `InvalidMixedProgramBinding` from `fromSchedule`.
The changed address controls are therefore exercising the intended join,
not merely a stale-checksum rejection. The existing source comparison also
rejects the changed call/binding. The generic loop checks both chip and bridge
slots for every registered call; the focused endpoint mutations use call 2 of
an N3 roster.

## Verification

- `zig build test-mixed-registry -Doptimize=ReleaseSafe`: pass.
- `zig build test-mixed-composition-admission -Doptimize=ReleaseSafe`: pass.

## Boundary of the finding

`fromSchedule` is an internal consistency check, not a verifier key. A caller
that changes both an endpoint and every dependent binding can make a
self-consistent diagnostic schedule; `requireSource` and the native package
instead reconstruct the schedule from verifier-owned source and official AIR
bytes. In `general_package.zig`, this reconstruction and typed-manifest join
occur before proof allocation. This review did not establish arbitrary
compiler correctness, witness confidentiality, PCS/FRI security, or a new
proof profile. The mixed package explicitly treats `private` as language
visibility rather than hidden base-trace data.
