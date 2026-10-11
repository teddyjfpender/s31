# Independent source review: V4 selected schedule

Reviewed S31 `a3789b2d757cc5fa6f5681f75f55d6d97ff0d9c` and engine
`26540e0ef19a47b38ce306570319c4e2a2e55b13` against integrated S31
`03ffe10d8da914de097c1d09a3415fadffbdb66a` and engine
`078aa72869cfb2a7855b008e54ae27021d1ac2d1`. This was a source-only
review. No build, test, proof, or byte comparison was run for this checkpoint.

## Findings

1. **High: completion blocker, not an observed proof exploit.** The selected
   slots do not yet drive the native proof. S31 projects selected calls back
   into the legacy `Request.plan`
   (`src/frontends/s31/runtime/bounded_compiled_binding.zig:229-234`), and
   `many_native_package.zig:56-63,187-201` still invokes the legacy engine
   entrypoints. Those entrypoints reconstruct the roster, column order,
   claimed-sum order, and verifier handles from that plan
   (`deps/stwo-zig/src/integrations/circuit_cpu/direct_many_arithmetic.zig:123-136,175-181,203-207,315-318,360-408`). The source-derived selector is an
   additional consistency check today; it is not yet one execution authority.
   Keep the current proof profile described that way until both proof paths
   consume selected slots and reject any runtime handle disagreement.

2. **Medium: the selected type is not an authentication capability.** The
   engine selector checks fixed root, PCS, canonical call IDs, ordered kinds,
   spans, constraint offsets, degrees, preprocessed indices, relation IDs,
   and chip/bridge handle parameters
   (`deps/stwo-zig/src/integrations/circuit_cpu/direct_many_schedule.zig:138-211`).
   It does not inspect the candidate's `source_digest` or any slot's
   `program_binding_sha256` before copying them into the result (`:213-220`).
   `bindManifestDigest` accepts any digest (`:90-95`), and the public structs
   expose mutable fields (`:18-100`). In the current sealed path these values
   are regenerated from source, official AIR, and compiled endpoint addresses
   (`src/frontends/s31/runtime/bounded_compiled_binding.zig:329-410`,
   `:624-636`; `src/frontends/s31/runtime/bounded_component_manifest.zig:457-500`).
   The current source-pinned wrapper is therefore the authentication boundary.
   A future `proveSelected` or `verifySelected` must preserve that boundary;
   accepting a caller-built `SelectedSchedule` as inherently authenticated
   would not be justified by this selector.

3. **Medium: mutation coverage is too narrow for promotion.** The new selector
   test checks one call and eight mutations: proof and sum index, source kind,
   main width, relation ID, fixed index, fixed root, and PCS query count
   (`src/frontends/s31/runtime/bounded_compiled_binding.zig:1002-1044`). It
   does not try source or program-binding digest changes, call/endpoint order,
   main or interaction offsets, coefficient offset, degree, bundle identity,
   other PCS fields, or the eight-call maximum. Tests against the selector
   alone also cannot establish that later proof execution follows selected
   slot order.

## Positive checks from inspection

The source-pinned S31 entrypoint recompiles the source, compares endpoint
addresses and fixed root, rebinds the selected bundled AIR, regenerates the
manifest, and then selects against live verifier-handle geometry before
hashing the V4 manifest
(`src/frontends/s31/runtime/bounded_compiled_binding.zig:329-410`). The
selector's comparison covers every active slot and its claimed-sum index
(`deps/stwo-zig/src/integrations/circuit_cpu/direct_many_schedule.zig:165-211`).
The verifier checks the selected source, manifest, and circuit-identity bytes
before postcard decoding and uses selected live PCS preflight
(`src/frontends/s31/runtime/many_native_package.zig:115-178`). The selected
identity formula appears equivalent to the previous source/root/trace-log/PCS
identity formula by source inspection; proof-byte equivalence is untested.

## Promotion gates

- Make selected slots the only indexed source for trace columns, claim sums,
  prover/verifier handles, coefficient order, transcript identity, and PCS
  openings. Recheck challenged runtime handles against the selected facts.
- Keep selected schedule construction inside the source-pinned wrapper, or
  make the engine's admitted type impossible to construct from arbitrary
  caller digests. Explicitly test that source, program-binding, and manifest
  digest mutations cannot enter proof verification through the new adapter.
- Run Debug and ReleaseFast N=1–8 native proof/verify; mutate every claimed
  sum and every selected slot field, including endpoint, source, offset,
  relation, degree, root, and PCS fields. Reseal digests for semantic mutation
  controls so rejection is not explained only by a hash mismatch.
- Compare deterministic V4 transcript and envelope bytes with the integrated
  baseline where available; run the source-pinned black-box acceptance path
  and verify the V3 pair bytes separately.

This review did not audit the AIR evaluator algebra, lookup reduction, or
PCS/FRI soundness. It does not certify witness privacy; the current V4 profile
is transparent.
