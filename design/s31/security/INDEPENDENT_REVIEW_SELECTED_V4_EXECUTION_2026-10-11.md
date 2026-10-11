# Independent source review: selected V4 execution

Reviewed S31 `bcc1988` with engine `21e408e2f` against the earlier
[selected-schedule checkpoint](INDEPENDENT_REVIEW_SELECTED_SCHEDULE_2026-10-11.md).
This review inspected source and tests. It did not run Zig tests or native
proofs, and it does not independently certify AIR algebra or PCS/FRI soundness.

## Disposition of the earlier findings

1. **Earlier high execution-authority blocker: closed for the sealed V4 path.**
   `proveSealed` and `verifySourceBound` now pass the regenerated
   `SelectedSchedule` to the selected engine adapters
   (`src/frontends/s31/runtime/many_native_package.zig:44-61,123-125,184-198`).
   Those adapters derive their compatibility `Request.plan` from selected
   calls, then revalidate the selection against a freshly constructed fixed
   circuit and live verifier geometry before proof work
   (`deps/stwo-zig/src/integrations/circuit_cpu/direct_many_arithmetic.zig:202-243,487-518`;
   `deps/stwo-zig/src/integrations/circuit_cpu/direct_many_schedule.zig:131-176`).
   Selected slots supply ordered main and interaction columns, claimed sums,
   prover and verifier handles, and verifier column logs
   (`direct_many_arithmetic.zig:89-162,289-350,358-420,560-583,590-661`).
   The legacy `Request.plan` still builds the fixed circuit and extracts call
   endpoints; because it is a projection of the selected calls and revalidation
   checks the exact canonical slot roster, it is not a second independently
   supplied order in this path. Legacy engine entrypoints remain public for
   in-memory callers and are not source-authenticating APIs.

2. **Earlier medium mutable-capability finding: still open by design.**
   `SelectedSchedule`, `GeometrySelection`, and their fields remain publicly
   constructible and mutable. `selectGeometry` checks live geometry but copies
   `source_digest` and each `program_binding_sha256` without authenticating
   their provenance; `bindManifestDigest` accepts any digest
   (`deps/stwo-zig/src/integrations/circuit_cpu/direct_many_schedule.zig:18-100,215-271`).
   `revalidate` repeats geometry checks, not source or program-binding checks
   (`direct_many_schedule.zig:135-176`). The selected engine adapters are
   therefore unsafe as standalone proof-admission capabilities. This is not
   an observed bypass of the sealed verifier: `inspectMany` recompiles source,
   checks compiled endpoints and fixed root, binds official AIR, regenerates
   the typed manifest, selects live geometry, and computes the manifest digest
   (`src/frontends/s31/runtime/bounded_compiled_binding.zig:324-410`). The
   native verifier's public entry takes compile-time source and AIR, compares
   source, manifest, and circuit identity bytes before bounded proof decoding,
   and its CLI embeds those files (`many_native_package.zig:94-198`;
   `many_verifier_main.zig:20-26`). Keeping this wrapper mandatory is a
   soundness condition. The relying party must also authenticate the verifier
   executable and fix expected public words independently.

3. **Earlier medium mutation-coverage finding: partially closed.** The
   source-inspection test now changes source, program-binding, and manifest
   digests and checks a fresh source inspection disagrees
   (`bounded_compiled_binding.zig:1045-1058`). The proof-byte tests cover
   source, envelope identity, each claimed sum for N=1 and N=2..8, public
   output changes, reordered calls, and changed endpoint addresses with
   envelope digests resealed (`many_native_package.zig:201-251,313-427`).
   Source inspection also checks changed live relation/source facts and
   preflight width limits (`bounded_compiled_binding.zig:973-998`). These are
   stronger than the earlier selector-only controls. An exhaustive field-by-
   field mutation matrix for every selected slot, PCS field, and count has not
   been added; engine-level digest mutation controls are still outside proof
   admission by design. No native test was rerun in this source-only pass.

## Additional checks and remaining limits

- **Transcript and PCS.** The selected identity derives from effective
  source/manifest digest, fixed root, selected circuit log, live PCS blowup,
  and selected calls (`direct_many_schedule.zig:109-120`;
  `private_many_boundary.zig:202-243`). Prover and verifier mix the same
  selected-derived plan/profile, FRI config, root, identity, public words,
  ordered sums and commitments (`direct_many_arithmetic.zig:242-250,279-285,
  323-350,535-583`). The verifier checks the actual preprocessed commitment
  against the recomputed fixed root and PCS config before transcript replay
  (`direct_many_arithmetic.zig:513-527`). The source-pinned package uses live
  PCS geometry for preflight before bounded postcard decoding
  (`many_native_package.zig:153-183`). This is a code-path check, not an
  independent cryptographic proof.
- **Proof-byte regression.** N=1 and N=8 tests compare the complete selected
  V4 envelope to the legacy path, and the N=2..8 matrix verifies each count
  (`many_native_package.zig:300-390`). These equality tests construct both
  outputs in the same build; there is no externally frozen historical proof
  byte fixture. They were inspected, not executed, in this pass. The N=8
  source was added to the formal source-binding inventory at S31 `bcc1988`.
- **Runtime handle geometry.** The selected engine reconstructs challenged
  handles from selected slot parameters, then checks constraint count,
  evaluation degree, composition split, and preprocessed indices against
  preflight (`direct_many_arithmetic.zig:170-183,358-420,590-661`). Current
  chip and bridge trace logs and mask widths are fixed by their constructors
  (`tagged_many_chip.zig:99-165`; `tagged_many_bridge.zig:121-187`). If V4 is
  generalized to pluggable chips, revalidate the full challenged handle
  geometry, including column logs and mask widths, or prove it invariant under
  lookup challenges. No concrete mismatch was found in these fixed handlers.
- **Scope.** This remains a bounded, transparent, direct-M31 circuit plus
  tagged repeated-step chip and bridge profile. It is not yet a generic
  authenticated private circuit-to-chip interface. It does not guarantee
  witness confidentiality, and this review does not close the LogUp reduction,
  AIR evaluator, compiler correspondence, or PCS/FRI proof obligations.

## Recommendation

Retain the source-pinned wrapper as the only V4 proof-byte admission path and
keep the selected engine adapters explicitly marked as in-process geometry
adapters. Before promoting a general chip API, make source/program-binding
provenance unforgeable at that API boundary and extend mutation tests to all
selected slot and PCS fields. Preserve a frozen V4 proof-byte fixture if exact
historical wire compatibility becomes a supported contract.
