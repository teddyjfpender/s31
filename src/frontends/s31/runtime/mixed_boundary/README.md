# Mixed native boundary (experimental)

`inspection.zig` reconstructs the selected mixed roster from source and live
AIR handles without consuming proof bytes. `package.zig` contains the N=3
proof-byte envelope, sealed prover, and source-pinned verifier. Its verifier
embeds the S31 source and official AIR
bundle, reconstructs the seven-component live schedule, checks the envelope
and bounded proof shape, then invokes the engine's mixed native verifier.

The profile supports two pair-chip calls followed by one many-chip call. It
has a distinct wire tag from V3/V4. The engine adapter is not a standalone
source-authentication API; callers must use the source-pinned verifier. The
committed trace does not hide private witness values.

Run the focused honest and mutation controls:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-native -Doptimize=ReleaseFast -j1
```

See [`MIXED_NATIVE_N3_PROFILE.md`](../../../../../design/s31/language/MIXED_NATIVE_N3_PROFILE.md)
for the transcript, component roster, and assurance limits.
