# Mixed native boundary (experimental)

`inspection.zig` reconstructs the selected mixed roster from source and live
AIR handles without consuming proof bytes. `package.zig` and `n4_package.zig`
contain the admitted N=3 and N=4 proof envelopes. `general_package.zig` is an
**uncompiled draft** for one through eight calls, with a distinct tag and
typed registry manifest digest. Each verifier embeds the S31 source and
official AIR bundle,
reconstructs its live schedule, checks the envelope and bounded proof shape,
then invokes the matching engine native verifier.

The `direct-mixed`, `direct-mixed4` and draft `direct-mixed-general` targets
each compile three source-embedded commands from one normalized version 1 S31
source file. The build
runs the witness-free manifest inspector in check mode and rejects any source
outside that target's admitted source shape. The general target requires
one to eight calls and exactly eight public M31 words; it has not yet passed
native proof admission.

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

The fixed-profile statement holds eight canonical public words and source,
selected manifest, and circuit identity digests. The draft general statement
also carries the typed registry manifest digest, which replaces the selected
manifest digest in its version-3 proof header. The verifier recomputes those values from its embedded source
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
does **not** enter either fixed-profile proof transcript. The draft general
profile derives it from source and mixes it into a distinct transcript and
circuit identity.

The general profile also runs `lookup_budget.zig` during source inspection,
before proof creation or bounded verifier decoding. It counts every Gate row,
chip round, bridge row and public output lookup term, then checks the
integerized absolute-weight bound below the M31 characteristic. The circuit
must have exactly nine output addresses: eight public words and the reserved
`u` wire. Each chip and bridge trace size is checked against its source call
and registered geometry. The JSON manifest reports `conditional_lookup_budget`
as an audit diagnostic; this field is derived from authenticated source and
live geometry, and is not an independent proof key or a registry-digest input.
The maximum admitted counts are `E = 722185` occurrences and
`B = 12585504 < 2147483647` integerized absolute weight. The direct
two-challenge calculation gives `(7E-6)/((2^31-1)^4) < 2^-101.73` **only**
for the lookup-compression algebraic event under the worksheet's fixed-tuple,
uniform-challenge and AIR-enforcement premises. AIR, PCS/FRI and transcript
failure probabilities are separate; the JSON value is not total proof
security. See `design/s31/security/LOOKUP_COMPRESSION_BUDGET_2026-10-11.md`.

The JSON reports include every **direct input** to the registry digest:
`registry_manifest_version`, root `registry_version`, source and IR hashes,
fixed root, `manifest_sha256`, `descriptor_sha256`, calls, ordered slots and
their registry identities, spans, lookup relations and AIR bindings, plus the
three geometry totals. The call, slot, fixed-column and relation counts come
from their JSON array lengths. Integers use little-endian unsigned bytes (`u8` for enum tags,
presence flags and list lengths, `u32` for other numbers); SHA-256 fields
decode from hexadecimal; the domain is
`S31-MIXED-REGISTRY-MANIFEST-V1\0`. The independent Python helper in
`tests/acceptance/mixed_boundary/registry_manifest_digest.py` recomputes
the digest from any of the three reports. The selected schedule digest
(`manifest_sha256`) and descriptor digest are **inputs** to this calculation;
deriving those two from first principles still requires the authenticated
S31 source, official AIR bundle, pinned engine and live PCS geometry. The
JSON itself is not verifier authority.

The draft general composer now has bounded dynamic arrays and claim parsing
for all eight counts, one transcript and PCS instance per proof, and live AIR
handles rebuilt from the source-derived registry. It remains isolated until
the engine and wrapper compile, native and black-box rejection tests pass,
and the tested engine commit is pinned into S31. The general proof's new tag
does not change N=3 or N=4 proof bytes.

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
zig build --build-file src/frontends/s31/build.zig test-mixed-general-native -Doptimize=ReleaseFast -j1
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_n4.py
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py
zig build --build-file src/frontends/s31/build.zig test-mixed-descriptor -Doptimize=ReleaseFast -j1
zig build --build-file src/frontends/s31/build.zig test-mixed-registry -Doptimize=ReleaseFast -j1
```

See [`MIXED_NATIVE_N3_PROFILE.md`](../../../../../design/s31/language/MIXED_NATIVE_N3_PROFILE.md)
and [`MIXED_N4_NATIVE_PROFILE.md`](../../../../../design/s31/language/MIXED_N4_NATIVE_PROFILE.md)
for the fixed transcript and component rosters. The draft general profile and
its admission gates are in
[`MIXED_GENERAL_NATIVE_PROFILE.md`](../../../../../design/s31/language/MIXED_GENERAL_NATIVE_PROFILE.md).
