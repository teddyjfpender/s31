# Mixed native boundary (experimental)

`inspection.zig` reconstructs the selected mixed roster from source and live
AIR handles without consuming proof bytes. `package.zig` contains the N=3
proof-byte envelope, sealed prover, and source-pinned verifier. Its verifier
embeds the S31 source and official AIR
bundle, reconstructs the seven-component live schedule, checks the envelope
and bounded proof shape, then invokes the engine's mixed native verifier.

The `direct-mixed` build target compiles three source-embedded commands from
one normalized version 1 S31 source file. Build runs the witness-free manifest
inspector in check mode and rejects any source outside the exact N=3 profile.
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

The statement holds eight canonical public words and source, selected
manifest, and circuit identity digests. The proof envelope carries the same
three digests. The verifier recomputes those values from its embedded source
and AIR; the JSON manifest is an audit output, not an input or a key. The
manifest lists source-derived calls, compiled endpoints, all seven ordered
component slots and claimed-sum positions, AIR source hashes, column spans,
lookup relation IDs, and PCS geometry. The prover and verifier reuse their
already rebuilt inspection when writing or checking the statement.

The profile supports two pair-chip calls followed by one many-chip call. It
has a distinct wire tag from V3/V4. The engine adapter is not a standalone
source-authentication API; callers must use the source-pinned verifier. The
committed trace does not hide private witness values.

Run the focused honest and mutation controls:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=ReleaseFast -j1
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned.py
```

See [`MIXED_NATIVE_N3_PROFILE.md`](../../../../../design/s31/language/MIXED_NATIVE_N3_PROFILE.md)
for the transcript, component roster, and assurance limits.
