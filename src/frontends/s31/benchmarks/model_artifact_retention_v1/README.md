# Frozen-model artifact retention gate

This **future-study tool** was added after the mixed-stage transfer v1 raw
phase, native audit and unscored evidence seal. It cannot restore or score
that run. It addresses the failure mode where a protocol pins only the hash
of a training-only cost model, while the exact `model.json` bytes remain in
an ignored measurement directory that is later removed.

Before a future held-out native build:

1. Compute the training model and freeze its exact SHA-256 in the prospective
   protocol. Run `retain.py seal` with that SHA, the protocol SHA, and paths
   **inside the repository** under `design/s31/measurements/language/`.
   The command copies the exact bytes without refitting and writes a
   canonical manifest. It refuses an existing artifact/manifest.
2. Review and commit **both** files in a separate model-artifact anchor
   commit. Record the full commit ID and model SHA externally. Retain or
   publish the commit before the held-out phase.
3. Make the held-out collector call `retain.py check` as its first preflight,
   before any package build. It requires the exact expected model/protocol
   hashes and the full anchor commit, reads model and manifest bytes from
   that commit, verifies they match the present files, and requires the
   anchor to be an ancestor of the checkout. Abort the held-out run on any
   mismatch. Include these identities in the held-out plan.

```sh
python3 -B src/frontends/s31/benchmarks/model_artifact_retention_v1/retain.py seal \
  --source zig-out/next-study-train/model.json \
  --artifact design/s31/measurements/language/next-study/model.json \
  --manifest design/s31/measurements/language/next-study/model-manifest.json \
  --expected-model-sha256 <full training-model SHA-256> \
  --protocol-sha256 <full prospective-protocol SHA-256>

# Review and commit artifact + manifest, record full commit ID, then:
python3 -B src/frontends/s31/benchmarks/model_artifact_retention_v1/retain.py check \
  --manifest design/s31/measurements/language/next-study/model-manifest.json \
  --expected-model-sha256 <same full SHA-256> \
  --protocol-sha256 <same full SHA-256> \
  --anchor-commit <full committed model-artifact anchor>
```

`check` proves local Git retention at the named ancestor commit. It cannot
prove a remote has the commit, and it does not itself enforce that a caller
runs it before native work; the next prospective collector must make that
call mandatory. The model bytes are an auditable release artifact and remain
separate from raw measurement data. This tool does not change any frozen v1
protocol, calibration, or result.

Native-free check:

```sh
python3 -B src/frontends/s31/benchmarks/model_artifact_retention_v1/test_static.py -q
```
