# V4 component provenance adapter

This is an admission check for the existing experimental V4, 1–8 call proof
profile. It does not change the V4 envelope, transcript, AIR, PCS, or component
order. Its first registered native component kinds are the existing tagged
repeated-step chip and endpoint bridge. A new chip kind requires a new reviewed
descriptor version and native AIR registration; an arbitrary caller-provided AIR
is never selected by a descriptor.

## Threat model

The adversary may replace proof bytes and any public, mutable in-process
`SelectedSchedule` or descriptor before calling an engine adapter. The sealed
S31 prover and verifier embed or otherwise authenticate exact source and AIR
bundle bytes, recompile the source, and regenerate the manifest in the same
operation. SHA-256 collision resistance and the existing STARK assumptions are
assumed. The engine does not parse S31: it cannot establish that supplied
canonical node IDs came from source, nor independently regenerate S31's full
manifest digest. Those are explicit S31 wrapper obligations. The engine's old
unsealed adapters remain experimental and must not be used as proof-byte
admission APIs.

`private` is only language visibility. V4 trace commitments are transparent
and this adapter makes no witness confidentiality claim.

## Adapter invariants

Before native proving or verification, the guarded adapter checks:

1. SHA-256 of the exact source bytes equals the selected source digest; SHA-256
   of the exact AIR bundle equals the selected circuit slot's bundle digest and
   the fixed official bundle digest. The guarded adapter parses those bytes
   itself, so a caller cannot pair them with a different in-memory template.
2. The supplied native-template digest equals a digest recomputed from the six
   V4 sources, in the established V4 order and hash domain. The direct-circuit
   source resides in a separate Zig package, so the wrapper supplies its exact
   embedded bytes and the adapter first checks their pinned V4 SHA-256.
3. Exactly one version-1 descriptor exists per selected component, in proof
   order. Its source kind, call ID, and program binding match the selected slot.
   Unknown versions and kinds fail closed.
4. Each native descriptor's canonical source/input node IDs, selected call
   parameters, compiled input/output addresses, embedded AIR source bytes, and
   native-template digest reproduce the existing V4 program-binding hash.
   Immediately before PCS, the guarded prover and verifier repeat this check
   from the concrete chip and bridge component objects used as AIR handles.
   Chip ID, constant, height, and trace offsets must agree with the bridge's
   live call boundary and the source-derived selected slots.
   The guarded adapter also recomputes the circuit slot-0 binding from the
   pinned AIR bytes, selected bundle index, and semantic hashes of the bound
   direct-gate parts. It compares this independently with both the descriptor
   and selected schedule, rejecting a joint edit of their claimed hash.
5. S31 derives descriptors from its regenerated typed manifest and invokes the
   guarded adapter. It also validates provenance before decoding proof bytes.

These checks make a stale or edited native program binding observable at the
adapter boundary. They do not turn public Zig structs into unforgeable
capabilities. A caller that bypasses S31's source-pinned wrapper can construct
self-consistent fake source metadata, so the wrapper remains the only admitted
proof-byte entrypoint.

The circuit hash check uses the already rebound AIR in the prover and verifier;
it does not repeat the expensive circuit binding. S31 still owns the statement
that source syntax, canonical node IDs, compiled endpoints, and the complete
manifest digest correspond to that bound circuit. The engine cannot establish
those source semantics by hashing AIR bytes alone.

The native check binds the registered chip and bridge *source files* and their
runtime parameters. It does not cryptographically hash a compiler binary or
formally prove that compiled machine code equals those source files; this
remains a build-integrity assumption. The concrete handle checks run after
ordinary live-handle geometry checks and before PCS proving or verification.

## Versioning and extension rule

Version 1 is closed over `bundled_circuit`, `tagged_chip`, and `tagged_bridge`.
The descriptor is an in-process admission record, not a serialized proof field.
Adding a chip requires its own native AIR source hash, binding formula, live
handle preflight, lookup relation closure, claimed-sum placement, PCS geometry,
negative controls, and a reviewed version/profile decision. The existing V4
wire bytes must remain unchanged for version-1 descriptors.
