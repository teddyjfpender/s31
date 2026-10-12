# V23 quiet-host eight-call cost holdout

This is a one-attempt prospective test of the frozen V18 whole-prover cost model at the call count where V17 failed. It uses a new log-13 source: five live arithmetic branches, 1,024 operations each, one multiplication every five operations, four balanced join additions, and eight ordered repeated-square chip calls with 4,096, 128, 1,024, 256, 2,048, 64, 512, and 32 rounds. The source and exact 21 claims are frozen under `design/s31/measurements/language/`. They are distinct from the V17, V18, V21, and V22 source topologies.

The manifest forecast is one circuit plus eight chip/bridge pairs: 17 slots, 163 constraints, tree columns `[8, 148, 232, 8]`, and exact source-derived registry fields, call IDs, feeder IDs, constants, and slot logs. The runner checks the native manifest before any proof. It then requires 22 honest generated proofs accepted by the external native verifier and 22 changed-result statements rejected at the proof layer.

Warm predictions use the V18 model unchanged: the V17 log-13 four-call baseline plus four frozen average-call steps. This explicitly tests whether the model transfers to another eight-call source; V17's prior failure remains in the evidence. Build, first post-build, immediate repeat, and build-plus-22-process-sum forecasts use the unchanged five-record V18–V20 median rule. These lifecycle points are exploratory. All gates and prediction numbers are in the canonical protocol, frozen before the native run.

Before the one-attempt marker, two `ps` snapshots one second apart must show no Lean, lake, or Zig process and no other non-runner process at or above 10% CPU. A busy preflight consumes no attempt. The snapshot bytes and hash are bound into the marker. Once the marker exists, any native failure remains the one recorded attempt; the runner does not retry. The first post-build run measures immediate first use, not a controlled operating-system cold cache.

Static preflight, before any native observation:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v23_n8_holdout/freeze.py check
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v23_n8_holdout/*.py
```

After the preregistration commit is pushed and the host is quiet:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v23_n8_holdout/study.py run \
  --out /private/tmp/s31-v23-n8-holdout-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v23_n8_holdout/audit.py \
  --out /private/tmp/s31-v23-n8-holdout-artifacts --native --write
```

The protocol, attempt marker, result, score, and audit records live under `design/s31/measurements/language/`; raw binaries and proofs remain in the artifact directory. A single host and source cannot establish cross-host calibration, automatic lowering quality, or a Cairo speedup.
