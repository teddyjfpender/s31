# Independent review: mixed registry manifest and native schedule identity

Date: 2026-10-11. Scope: S31 commit `9862fb5` (`registry_manifest.zig`,
`general_package.zig`) and the pinned `deps/stwo-zig` mixed schedule and
general proof adapter. This review concerns the experimental 1–8 call general
profile. It does not certify the AIR, PCS/FRI implementation, or formal
compiler correspondence.

## Result

I found no accepted resealed roster or polynomial-shape mutation on the
source-embedded general proof path. The trust chain is:

1. `general_package.verifySourceBoundWithWitness` calls `inspection.inspectSource`
   using verifier-owned source and AIR bytes before bounded proof decoding.
2. `inspection.inspectSource` checks the generated source component roster
   against live native AIR facts, builds the direct circuit and native plan,
   checks the fixed root, and invokes `direct_mixed_schedule.inspect` to
   reconstruct ordered engine handles, polynomial columns, masks and PCS
   geometry. Its selected digest covers those active fields.
3. `registry_manifest.fromSchedule` checks the closed registry policy and
   contiguous offsets, compares each typed entry with the native geometry,
   and rejects a stale selected digest. `general_package.selectedFromSource`
   derives the engine plan and transcript manifest digest from that result.
4. The engine's `validateSourceAndGeometry` independently reconstructs its
   geometry from the supplied circuit view, AIR bundle and plan; it checks
   exact geometry equality, source hash, fixed root and circuit program
   binding. `checkRuntimeHandles` compares the actual component handles with
   the selected constraints, degree bounds, split and fixed indices. The
   verifier mixes the manifest-derived circuit identity and uses the selected
   ordered slots for claims, columns and handles.

This is an end-to-end statement about the **source-embedded wrapper**. Neither
a diagnostic SHA-256 nor a caller-supplied `SelectedSchedule` is a verifier key.
`requireSource` independently regenerates the complete `Manifest` from the
literal source and official AIR bytes and compares all fields; a candidate
cannot gain authority by recomputing its own digest.

## Field trace

| Manifest field | Source and live binding | Proof use |
| --- | --- | --- |
| Source hash, canonical IR hash, fixed root, call IDs/rounds/constants/endpoints | Source inspection, compiled topology, fixed-root recomputation | Source hash, fixed root and plan feed engine identity and validation; calls configure chip/bridge handles |
| `selected_manifest_sha256` | Selected schedule digest covers slots, column logs and widths, sampled mask-point digest, PCS/Fri geometry, local AIR dependency digest and source manifest | Input to registry digest, then transcript identity |
| Registry key/ID/version/role | Closed `registry.forSlot` policy; pair calls 0–1, many calls 2–7 | Controls chip/bridge constructor and handle order through source-derived slot kind |
| Proof index and claimed-sum index | Required equal to the canonical slot index | Engine iterates `circuit, chip(i), bridge(i)` and hashes that ordered claim list |
| Trace/evaluation logs, main/interaction offsets and widths, constraint offsets/counts | Source component facts, registered native AIR facts, contiguous-span checks and native geometry comparison | Engine builds commitments with those column logs and AIR handles with those offsets and degrees |
| Fixed-column indices and lookup relation IDs | Native handle inspection and `requireNativeGeometry`; relation-domain layout guard | Runtime handle checks and LogUp AIR components |
| Circuit AIR and program binding hashes | Official AIR bundle, bound direct-arithmetic program and engine `validateSourceAndGeometry` | Selects the circuit AIR verified by the engine |
| Native AIR and program binding hashes | Native fact source hash plus source call parameters; local AIR closure checked against pinned engine sources | Native chip and bridge handles are independently reconstructed by the engine |

The typed manifest records the three active tree widths, but does not expose
all PCS, FRI, mask-point or local dependency fields as separate typed fields.
Their binding is **indirect**, through the source-rebuilt selected digest and
the engine's exact geometry reconstruction. The direct
`requireNativeGeometry` helper only checks positive mask width, not equality
of every mask width or mask point; it also does not compare PCS settings or
composition geometry. This is acceptable for the current source-embedded
path because that helper is never the sole authority. It must not be reused
as a standalone admission function for caller-supplied geometry.

Likewise, the circuit slot has no native AIR source hash in the engine
geometry. Its typed hash is checked through the official AIR bundle and
direct-program binding, not by the chip-style per-slot hash comparison.
Inactive fixed-array padding is omitted from the manifest digest, but
`requireSource` compares the complete reconstructed struct and the wrapper
never accepts an external manifest as proof authority.

## Focused evidence

`zig build --build-file src/frontends/s31/build.zig test-mixed-registry
-Doptimize=ReleaseFast -j1` passed after this review's test addition.
The existing N=1–8 test checks authentic source reconstruction, native plan
parity, ordered slots and changed live call ID, relation, AIR hash, column
log and zero mask. The new test reseals each of 15 mutations with a valid
diagnostic checksum, then requires exact rejection by `requireSource`:
selected manifest, canonical IR, circuit/native AIR and program bindings,
fixed index, trace/evaluation logs, chip main/interaction widths, constraint
count, and global geometry totals. It also checks direct rejection of a
changed native constraint offset, fixed index and main tree width.

These are mutation tests of the admission wiring, not a cryptographic
security proof. The remaining claim depends on the collision resistance of
the transcript/hash commitments, the soundness of the native AIR and PCS,
and faithful compilation of source semantics into the direct circuit.
