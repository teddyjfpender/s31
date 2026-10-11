# Independent source review: manifest, public record ABI, and mixed boundary

Reviewed S31 commit `6ab79173fee0945c32168a616e365841fc03d84b` with the pinned
`deps/stwo-zig` engine. This was a read-only source review by an independent
agent. It did not run a native build, produce a proof, or establish end-to-end
STARK soundness. The later queued Lean and timing changes are outside this
reviewed revision.

## Result

No concrete P1 or P2 false-proof path was found in the reviewed paths.

* The direct-key verifier compares the supplied key with the package's
  embedded key, regenerates the source-derived component manifest, and checks
  the live component geometry before verifying. Preflight and final native
  verification share one `DirectHandles` owner; a separately reconstructed
  handle set cannot silently diverge between the two checks.
* The manifest precommitment includes component and program bindings, columns,
  call layout, and the private boundary. Its effective digest enters the
  circuit identity and transcript.
* Record ABI v2 requires a canonical typed statement, an exact ABI digest and
  paths, and public bit words in `{0,1}`. The prover validates the public bit
  projection before proving; the verifier projects the same bounded words
  into native verification. The mixed v2 entrypoint also uses this projection.
* For one through eight source-pinned mixed calls, the compiler materializes
  four scalar ports per arithmetic-produced SIMD feeder with `simd.unpack`.
  The engine constrains those ports with pointwise mask and inverse relations.
  Each call binds its exact port addresses and values to the tagged chip
  lookup. The compiled-binding check compares source IDs, call IDs, addresses,
  row counts, and fixed root; Gate multiplicities account for repeated feeder
  use. Existing mutation controls reject an address swap and a doubled use.

The review traced these claims through `src/frontends/s31/runtime/mvp_runtime.zig`,
`runtime/native_verifier.zig`, `runtime/component_manifest.zig`,
`runtime/mixed_boundary/general_verifier_main.zig`,
`language/record_abi.zig`, `language/bounded_call_admission.zig`,
`language/relation_compiler.zig`, and the pinned engine's `simd.zig`,
`direct_arithmetic.zig`, `tagged_many_bridge.zig`, and
`private_many_boundary.zig`.

## Remaining assumptions

This review does not prove the engine's pointwise M31 and chip AIR constraints,
the lookup multiset argument, commitment authentication, PCS/FRI, or the
Fiat–Shamir reduction. It does not prove that every accepted S31 program's
native circuit corresponds to its source semantics. Record ABI v2's Lean
path/word model still needs a refinement theorem for the production Zig parser
and Python compiler. These are explicit obligations for a full soundness
claim, not findings of an exploitable mismatch in this review.

The direct-gate manifest v2 route does not perform the chip route's postcard
shape preflight. It does retain the 16 MiB wire and 64 MiB decode limits; the
missing preflight is a resource-accounting difference, with no demonstrated
proof-admission exploit. Recheck this review after changing the verifier,
manifest schema, record ABI, or mixed-call compiler.
