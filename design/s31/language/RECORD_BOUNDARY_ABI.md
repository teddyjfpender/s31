# Record-valued circuit boundary: versioned ABI design

Status: historical design sketch. The implemented `direct-gate` M31-leaf v2
boundary, including nominal record inputs and results, is specified in
[RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md](RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md).
The native verifier now binds the descriptor digest and canonical typed
statement to the sealed key. Other proof profiles and non-M31 leaves remain
outside this ABI. The named public statement can be read after native proof
verification with `s31 inspect-record-proof`.

## Why the relation format needs an explicit extension

Relation v1 lists public outputs as wire names. A field such as
`result.quotient` has no separate path or type in that list. Two fields may
also legitimately refer to the same wire, while v1 rejects repeated output
names. Renaming or adding a copy gate would either lose the intended field
binding or add proof work just to name a record. An unsealed sidecar mapping
from field names to wires would let the displayed statement differ from the
statement verified by the native verifier.

The extension must therefore bind the full typed field layout into the
verification key and proof statement. It must not infer an ABI from source
text at verification time.

## Proposed relation v2 surface

The record layout is a canonical tree: nominal type name, ordered field
names, and first-order leaf types. Struct and tuple children recurse in
declaration or tuple index order. A field path is an array of tagged segments,
for example `[{"field":"header"},{"field":"target"}]`; this avoids
collisions between names containing underscores and nested paths.

Each circuit input leaf has a unique path, visibility, relation name, kind,
and length. Each public output leaf has a unique path, a relation wire
reference, kind, and length. Distinct output paths may refer to the same
wire. The canonical relation encoding includes the layout tree and the leaf
descriptors. The key digest and native verifier must bind those bytes along
with the constraint graph and public input/output ordering. Field order is
declaration order, never the order of a constructor literal or JSON object.

The assignment format uses the same canonical path tree. Decoding must reject
unknown, missing, repeated, mistyped, and noncanonical leaves. Private input
leaves are present in the witness but absent from the public statement.
`bit` leaves retain Boolean constraints. Fixed-width integer leaves retain
their nominal width/sign checks, including byte range checks. The sum of
public input and output leaf words remains at most eight until the public
ABI itself is separately raised.

The preparatory [v2 codec](../../../src/frontends/s31/python/abi/record_v2.py)
now serializes a nominal layout digest and tagged root/field/tuple paths in
declaration order. It round-trips typed values and rejects altered layouts,
paths, counts, noncanonical field/bit/byte words, duplicate JSON keys, and
noncanonical JSON bytes. Its [controls](../../../src/frontends/s31/tests/python/test_record_abi_v2.py)
cover nested records and these malformed cases. This original codec is not
the proof boundary. The implemented [binding v2](../../../src/frontends/s31/python/abi/binding_v2.py)
and [native validator](../../../src/frontends/s31/language/record_abi.zig)
extend it with sealed relation, key and statement checks; the source compiler
admits the M31-leaf record boundary under `direct-gate` only.

## Required implementation and proof gates

1. Define a versioned relation and package schema with deterministic
   serialization. The native verifier rejects a relation/key/statement whose
   ABI digest differs, before proof verification.
2. Flatten source values recursively to first-order leaves and reconstruct
   typed record values for circuit execution. Prove flatten and reconstruct
   are inverse on well-typed values, and prove path encoding is injective.
3. Bind every public input leaf and output leaf to its declared wire, including
   two different field paths that share one wire. Check the resulting AIR
   constraints and native verifier statement parser against forged field
   values, reordered fields, changed visibility, and changed layouts.
4. Compare nested record circuits to manually flattened equivalents under the
   same relation version. Record grouping must add zero arithmetic gates,
   zero AIR rows, and zero witness columns. Any versioned ABI bytes or key
   bytes are reported separately from proof work.
5. Add compiler, independent oracle, native proof, changed-statement,
   malformed-ABI, and Lean model tests. The Lean claim must distinguish typed
   flattening from the still-open full Python-to-Zig refinement obligation.

This is a separate release boundary because changing only the parser would
make record field names look public without making them part of what the
verifier actually checks.
