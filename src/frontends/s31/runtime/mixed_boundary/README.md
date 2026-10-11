# Mixed native boundary (experimental)

`inspection.zig` reconstructs the selected mixed roster from source and live
AIR handles without consuming proof bytes. `package.zig` and `n4_package.zig`
contain separate N=3 and N=4 proof envelopes, sealed provers, and source-pinned
verifiers. Each verifier embeds the S31 source and official AIR bundle,
reconstructs its live schedule, checks the envelope and bounded proof shape,
then invokes the matching engine native verifier.

The `direct-mixed` and `direct-mixed4` build targets each compile three
source-embedded commands from one normalized version 1 S31 source file. Build
runs the witness-free manifest inspector in check mode and rejects any source
outside that target's exact N=3 or N=4 profile.
The command implementations and statement schema live here; the tiny files in
`entry/` are required only by Zig's module-root import rule.

```sh
cd src/frontends/s31
zig build install -Doptimize=ReleaseFast -Ds31-version=1 \
  -Ds31-lowering=direct-mixed \
  -Ds31-source="$PWD/examples/boundary/private_mixed3.s31.json" \
  -Ds31-name=private_mixed3
zig-out/bin/s31-private_mixed3-mixed-prover \
  examples/boundary/private_mixed3.valid.json \
  /tmp/mixed.proof /tmp/mixed.statement.json
zig-out/bin/s31-private_mixed3-mixed-native-verifier \
  /tmp/mixed.proof /tmp/mixed.statement.json
zig-out/bin/s31-private_mixed3-mixed-manifest > /tmp/mixed.manifest.json
```

For the fixed four-call profile, select `direct-mixed4` and inspect the
generated nine-component roster:

```sh
cd src/frontends/s31
zig build install -Doptimize=ReleaseFast -Ds31-version=1 \
  -Ds31-lowering=direct-mixed4 \
  -Ds31-source="$PWD/examples/boundary/mixed_four.s31.json" \
  -Ds31-name=mixed_four
zig-out/bin/s31-mixed_four-mixed4-prover \
  examples/boundary/mixed_four.valid.json \
  /tmp/mixed4.proof /tmp/mixed4.statement.json
zig-out/bin/s31-mixed_four-mixed4-native-verifier \
  /tmp/mixed4.proof /tmp/mixed4.statement.json
zig-out/bin/s31-mixed_four-mixed4-manifest > /tmp/mixed4.manifest.json
```

The statement holds eight canonical public words and source, selected
manifest, and circuit identity digests. The proof envelope carries the same
three digests. The verifier recomputes those values from its embedded source
and AIR; the JSON manifest is an audit output, not an input or a key. The
manifest lists source-derived calls, compiled endpoints, all ordered
component slots and claimed-sum positions, AIR source hashes, column spans,
lookup relation IDs, and PCS geometry. The prover and verifier reuse their
already rebuilt inspection when writing or checking the statement.

The N=3 profile supports two pair-chip calls followed by one many-chip call;
N=4 adds a second many-chip call. Both use distinct wire and transcript tags
from V3/V4 and from each other. The engine adapter is not a standalone
source-authentication API; callers must use the source-pinned verifier. The
committed trace does not hide private witness values.

`descriptor.zig` adds a versioned, ordered descriptor for source-inspected
mixed plans of one through eight calls. It maps each call to a chip and
bridge, with the first two using pair AIRs and subsequent calls using many
AIRs. `requireSource` reconstructs the descriptor from literal source and the
official AIR bundle, then checks cardinality, role order, source and manifest
hashes, and program bindings. The N=4 test checks a nine-component roster and
resealed descriptor mutations. A descriptor alone never admits a proof;
`verifyEmbeddedWithDescriptor` checks it against source before invoking its
fixed N=3 or N=4 verifier.

`registry.zig` is the closed version 1 constructor table for the five current
mixed component identities: the bundled circuit, pair chip and bridge, and
many chip and bridge. The compiler-derived call index selects the chip and
bridge family: calls 0 and 1 use pair components; calls 2 through 7 use many
components. The registry checks each native constructor against a live engine
AIR handle, including trace widths, constraint count, evaluation degree and
lookup relation dependencies. `inspection.zig` and `descriptor.zig` now use
this common selection policy. The resulting proof and claimed-sum order is
always `circuit, chip(0), bridge(0), ...`; neither a proof nor JSON manifest
chooses or reorders these constructors.

`registry_manifest.zig` projects the source-inspected plan into a typed
one-through-eight-call roster. It records the source and canonical IR hashes,
fixed root, compiled input and output gate addresses, constructor IDs, AIR
bindings, trace and column geometry, relation dependencies, and exact proof
and claimed-sum indexes. `requireSource` regenerates the entire roster from
literal verifier-owned source and AIR bytes, so recomputing its diagnostic
SHA-256 cannot authorize an altered component. The N=3 and N=4 manifest
commands show the new registry IDs and diagnostic digest alongside their
existing audit fields. Their wire formats, selected-schedule digest domains
and proof transcript tags remain distinct and unchanged. The registry digest
does **not** enter either current proof transcript.

This is a generated audit manifest and shared admission policy, not a
generalized 1–8-call native proof adapter. Only N=3 and N=4 have source-pinned
mixed native proof admission. Counts 1, 2 and 5–8 have source-bound inspection
tests but no mixed proof envelope, prover or verifier. General proof admission
still needs dynamic bounded component arrays and claim parsing in the engine,
one transcript and PCS instance for each count, and verifier use of the same
source-derived registry to instantiate every live AIR. A future profile must
bind its registry revision and canonical roster under a new transcript tag;
the diagnostic digest here cannot be retrofitted into N=3 or N=4.

`test_source.zig` generates a chain of 1–8 live repeated calls for the focused
descriptor matrix. Every count checks the source-reconstructed roster and
geometry, rejects a resealed program binding, role swap, and shortened roster,
and counts other than three are rejected by the N=3 proof entrypoint before
proof decoding. These are descriptor tests; the separate N=4 package constructs
and verifies a native four-call proof.

`witness_audit.zig` is the next N=4 handoff check. It revalidates source and
descriptor authority, compiles a witness against a separate witness-free
topology, writes the circuit and selected pair/many chip and bridge base
traces, and checks their public outputs and all four input/output handoffs.
Its independent integer recurrence checks every chip step. The test changes
endpoint values, source, component order and role, a resealed descriptor
binding, and a claimed public output. The audit alone is not proof admission;
`n4_package.zig` supplies the separate proof-backed N=4 path.

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-n4-witness -Doptimize=Debug -j1
```

Run the focused honest and mutation controls:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=ReleaseFast -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-n4-native -Doptimize=ReleaseFast -j1
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_n4.py
zig build --build-file src/frontends/s31/build.zig test-mixed-descriptor -Doptimize=ReleaseFast -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-registry -Doptimize=ReleaseFast -j1
```

See [`MIXED_NATIVE_N3_PROFILE.md`](../../../../../design/s31/language/MIXED_NATIVE_N3_PROFILE.md)
and [`MIXED_N4_NATIVE_PROFILE.md`](../../../../../design/s31/language/MIXED_N4_NATIVE_PROFILE.md)
for the transcript, component rosters, and assurance limits.
