# Mixed source inspection context reuse

`study.py` compares two source-embedded ReleaseFast mixed packages with the
same source and saved assignments. For each claim it alternates binary order,
proves and externally verifies both proofs, requires exact proof and statement
bytes, and requires both changed-result claims to fail at
`InvalidMixedInteractionNonce`. Claim 0 warms both binaries; claims 1–40 form
the reported matched sample. The runner saves proofs and stderr in its output
directory and writes a compact result with binary, proof, statement, source,
manifest, and circuit identity hashes.

The measured instance uses the V10 `gate_weave_n1` source and raw claims in
`/tmp/s31-v10-geometry-transfer-a4230b3/gate_weave_n1`. The baseline package
was built at `a4230b3`; the context-reuse package was built at `9645893`.
Only `runtime/bounded_compiled_binding.zig` and
`runtime/mixed_boundary/inspection.zig` changed in the production frontend
between those commits. The [measurement note](../../../../../design/s31/measurements/MIXED_CONTEXT_REUSE_V1.md)
and [compact result](../../../../../design/s31/measurements/language/mixed-context-reuse-v1-result.json)
record the observed deltas and raw artifact location.

To rebuild the optimized package against the retained V10 source:

```sh
zig build --build-file src/frontends/s31/build.zig install \
  -Doptimize=ReleaseFast -Ds31-version=2 \
  -Ds31-lowering=direct-mixed-general \
  -Ds31-source=/tmp/s31-v10-geometry-transfer-a4230b3/gate_weave_n1/source.s31.json \
  -Ds31-name=mixed_cost_v10_geometry_transfer_gate_weave_n1 -j1 \
  --prefix /tmp/s31-mixed-context-reuse-9645893/package
```

Run the matched comparison from the S31 repository root on an otherwise quiet
host. The output path must be new:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_context_reuse/study.py \
  --baseline-prefix /tmp/s31-v10-geometry-transfer-a4230b3/gate_weave_n1/package/bin/s31-mixed_cost_v10_geometry_transfer_gate_weave_n1-mixed-general- \
  --optimized-prefix /tmp/s31-mixed-context-reuse-9645893/package/bin/s31-mixed_cost_v10_geometry_transfer_gate_weave_n1-mixed-general- \
  --source-dir /tmp/s31-v10-geometry-transfer-a4230b3/gate_weave_n1 \
  --out /tmp/s31-mixed-context-reuse-9645893/matched-v1 \
  --claims 40 --baseline-commit a4230b3 --optimized-commit 9645893
```

The source package build is excluded from the timed proof processes. This is
an exploratory paired measurement on one host and one selected program, not a
prospective general cost or speedup claim. FRI proof of work is unchanged;
its timing and process scheduling can mask the smaller inspection saving.
