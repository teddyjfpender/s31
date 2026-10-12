# V21 unseen mixed topology cost holdout

This is one prospective local test of whether the V18 whole-prover cost rule transfers to a mixed program that no prior cost study measured. The new source has four independent 1,024-operation branches, one multiplication in every five branch steps, a balanced join, and five sequential repeated-square chip calls of lengths 4,096, 512, 128, 2,048, and 256. It has 4,096 live arithmetic operations and compiles to an expected 13-log circuit plus five chip/bridge pairs. The source is saved as `design/s31/measurements/language/mixed-cost-v21-unseen-topology-source.json`.

The pre-native protocol freezes the exact source, 21 assignments and statements, 20-claim order, source-derived call IDs and slot layout, production and tool hashes, host and engine identity, predictions, and accuracy gates. The source, protocol, and tools must be committed before the one-attempt marker is created. The protocol predicts 11 component slots, 106 constraints, tree columns `[8, 97, 148, 8]`, and trace logs `[13, 12, 4, 9, 4, 7, 4, 11, 4, 8, 4]`. The compiled manifest must match these fields and every source-derived ordered call before timing begins.

The warm prediction uses the previously frozen V18 rule: take the V17 log-13 four-call baseline and add one V17-derived average-call step. The four-branch topology and one-in-five multiply ratio are an explicit extrapolation with no target refit. The median warm process prediction is **220.485 ms**, with a one-draw 90% band of **152.150–513.392 ms**. Median proof bytes are predicted at **212,278** with a **191,377–233,178** band. Lifecycle point forecasts are medians of five previously measured V18–V20 records: build **78.172 s**, first verified proof **1.212 s**, immediate repeat **0.285 s**, and build plus 22 separately measured verified proof processes **84.079 s**. Those are local exploratory point forecasts, not calibrated cross-host intervals.

The runner creates the one-attempt marker with `O_EXCL` before the native build, preserves failed attempts, and never retries within this protocol. It builds the isolated package, checks the manifest, proves 22 claims in fresh processes, accepts every exact public statement, and requires every changed-result statement to fail at the proof layer. The audit rechecks hashes, manifest, score arithmetic, timings, and optionally replays every native verifier call. A missed gate is recorded as a failure.

Before the native attempt:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v21_unseen_topology/freeze.py check
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v21_unseen_topology/*.py
```

After the preregistration commit is pushed, on a quiet host:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v21_unseen_topology/study.py run \
  --out /private/tmp/s31-v21-unseen-topology-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v21_unseen_topology/audit.py \
  --out /private/tmp/s31-v21-unseen-topology-artifacts --native --write
```

The canonical protocol, marker, result, score, and audit live under `design/s31/measurements/language/`. The raw proof and binary artifacts stay in the isolated output directory. One host and one source cannot establish general cost calibration, cross-host reliability, or a Cairo speedup; the V17 eight-call model failure remains a failure.
