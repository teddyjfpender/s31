# Direct-gate padded-geometry transfer diagnostic

This protocol tests a new cost question after the 512-row, 1–16-gate
prospective check: does a simple geometry-stratified estimate transfer to
different **programs** at both 512 and 1024 padded QM31 rows? The source is
an alternating four-lane M31 add/multiply recurrence. Training uses 32, 192,
and 384 gates; held-out programs use 96, 256, and 448 gates. The 32/192/96
programs are expected to pad to 512 rows, and 256/384/448 to 1024. The
runner rejects a build if its actual native `cost-report.json` disagrees.

The model predicts each metric by the median of training **program medians**
within that row stratum. Thus the 1024-row prediction has just one training
source. No slope, gate-count coefficient, old V8r1 model, or held-out refit is
used. The four fixed diagnostic median-error limits are 50% paired process
wall, 30% wall after subtracting both reported native PoW timers, 10% proof
bytes, and 15% prover peak RSS. The raw training min/max is reported as a
descriptive range, not a statistical interval. Source and assignment digests,
compiler fingerprint, engine gitlink, host, Zig version, metric rule, limits,
and this script's SHA-256 are sealed in `plan.json` before native work. The
training data and fixed estimates are sealed in `calibration.json` before any
held-out package build.

`direct-gate` programs above 16 gates are outside the bounded release
correspondence certificate. Every measured trial still requires the native
source-embedded verifier to accept the proof, reject a changed public claim,
and pass the independent Python value oracle. A later `audit` command replays
all saved native proof and changed-claim controls and recomputes the frozen
score. This is a local cost diagnostic, not a soundness result or a general
whole-prover predictor. Compilation, Python orchestration, and the audit
replays are separate from the paired prover-plus-verifier process target.

The completed [local result](../../../../../design/s31/measurements/GEOMETRY_TRANSFER_V1_RESULT.md)
retains all sealed artifacts and a 72-trial compact ledger under
`results-2026-10-11/`. All four diagnostic limits passed, but the 448-gate
wall median missed its frozen center by 40.71%; see the result before using
these numbers for planning.

From the repository root, after compiler/runtime source edits stop and the
native build slot is free:

```sh
python3 -B src/frontends/s31/benchmarks/geometry_transfer_v1/test_static.py -q
python3 -B src/frontends/s31/benchmarks/geometry_transfer_v1/test_saved_result.py -q
python3 src/frontends/s31/benchmarks/geometry_transfer_v1/study.py plan \
  --out zig-out/s31-geometry-transfer-v1
python3 src/frontends/s31/benchmarks/geometry_transfer_v1/study.py train \
  --out zig-out/s31-geometry-transfer-v1
python3 src/frontends/s31/benchmarks/geometry_transfer_v1/study.py heldout \
  --out zig-out/s31-geometry-transfer-v1
python3 src/frontends/s31/benchmarks/geometry_transfer_v1/study.py audit \
  --out zig-out/s31-geometry-transfer-v1
python3 src/frontends/s31/benchmarks/geometry_transfer_v1/independent_score.py \
  --out zig-out/s31-geometry-transfer-v1
```

Keep the exact plan and calibration files before publishing results; changing
the runner, compiler, engine, or host invalidates this local protocol. Raw
packages, assignments, proof bytes, native trial reports, and scores stay in
the ignored `zig-out` directory. Preserve partial failures; use a fresh
output root for a new protocol version or rerun. The measurement's limits
and interpretation are also recorded in
[`GEOMETRY_TRANSFER_V1.md`](../../../../../design/s31/measurements/GEOMETRY_TRANSFER_V1.md).
