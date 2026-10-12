# V22 quiet-host mixed topology holdout

This prospective one-attempt run tests the frozen V18 whole-prover cost model on a new six-call source with three live arithmetic branches. Each branch has 1,536 operations, with one multiplication in every four steps. Two additions join the branches. Six ordered repeated-square chip calls use 2,048, 256, 4,096, 128, 1,024, and 512 rounds. The source and exact 21 claims are saved in `design/s31/measurements/language/`.

The preregistered manifest is a log-13 circuit plus six chip/bridge pairs: 13 slots, 125 constraints, tree columns `[8, 114, 176, 8]`, and trace logs `[13, 11, 4, 8, 4, 12, 4, 7, 4, 10, 4, 9, 4]`. The runner checks every source-derived call, slot, registry field, and geometry field against the native manifest before proof timing.

The warm prediction uses the V17 log-13 four-call baseline plus two frozen average-call steps, with no target observations or refit. It forecasts a 222.022 ms 20-claim warm median, a 153.687–514.929 ms one-draw wall band, and 227,381 median proof bytes. The lifecycle forecasts use the five previously measured V18–V20 one-host records and exclude V21's contended attempt: 78.172 s package build, 1.212 s first verified proof, 0.285 s immediate repeat, and 84.110 s for the build plus 22 separately measured verified-proof process durations. These are local exploratory forecasts.

Before the one-attempt marker, the runner takes a `ps` snapshot and refuses to start if a Lean, lake, or another Zig process is present. It stores the snapshot and hashes it in the marker. A busy preflight consumes no attempt. Once the marker exists, any native failure remains the one recorded attempt; the runner never retries. The native run then builds an isolated package, proves 22 claims in fresh processes, and requires the generated external verifier to accept every honest statement and reject every changed-result statement at the proof layer. The audit independently checks hashes, manifest, score arithmetic, timing records, the preflight snapshot, and optionally replays all 44 verifier calls.

Prepare and commit the frozen protocol and source first:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v22_quiet_holdout/freeze.py check
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v22_quiet_holdout/*.py
```

After the preregistration commit is pushed and the host is quiet:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v22_quiet_holdout/study.py run \
  --out /private/tmp/s31-v22-quiet-holdout-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v22_quiet_holdout/audit.py \
  --out /private/tmp/s31-v22-quiet-holdout-artifacts --native --write
```

The protocol, attempt marker, result, score, and audit records live under `design/s31/measurements/language/`; raw binaries and proofs remain in the isolated artifact directory. One source and one host do not establish cross-host calibration, automatic lowering quality, or a Cairo speedup. The V17 eight-call model failure remains unresolved.
