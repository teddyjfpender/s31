# Whole-prover cost model v3

The [machine-readable protocol](whole-prover-cost-v3.json) was written before
native measurement. It addresses the version mismatch between the [v1
whole-prover run](STAGE_AWARE_COST_V1.md) and the [v2 arithmetic RSS
follow-up](ARITHMETIC_RSS_V2.md): all v3 wall, proof-byte and peak-RSS targets
must be trained and evaluated under **one compiler fingerprint**. This is a
prospective test of prediction, not a claim that proving became faster.

## What is measured

Each saved trial contains a native proof, native verification, a changed public
claim that the verifier rejected, and an independent output oracle check. The
runner starts a fresh prover and native verifier process for each witness.
`paired_prove_and_verify_wall_seconds` is the sum of those two process wall
times; package construction is separately timed and excluded from that target.
`proof_bytes` is the proof file size. `prover_peak_rss_bytes` is peak resident
memory of the prover process, not package-build or verifier peak memory.
Package-build memory is recorded as unavailable because the Python builder
launches Zig subprocesses. Zig compiler-cache state is disclosed, not cleared.
Cached native setup and warm reusable prover processes are outside this run.

The four families are direct-gate arithmetic recurrence, one-call direct-chip
arithmetic recurrence, generic-gate BLAKE2s hash chains, and direct-gate
fixed-width signed division. Each family has four or five training programs
and four held-out programs at different source or scale points. All programs
have twenty distinct witness assignments. The chip package must contain the
power-of-two repeated-step round count required by the native chip, the
compiler-generated typed `s31-component-manifest-direct-chip-v2`, exactly one
`chip_call` at `call_id: 0`, and a sealed native key that binds it. The
publisher rechecks each saved package, component manifest, proof digest, full
trial report, and changed-public-statement diff.

## Predictor and uncertainty

The model fits a simple per-family curve for each native stage using **training
program medians only**. Witness, setup, prove excluding PoW, runtime overhead,
unattributed process time, and native verifier process time remain separate.
Direct gate and chip profiles expose interaction PoW and FRI PoW timers; the
generic hash prover exposes only an opaque prove timer that includes PoW. The
whole wall prediction sums the stage predictions. Proof bytes and peak RSS
have their own curves. Direct-gate arithmetic RSS uses the fixed-baseline plus
per-padded-row positive affine form prospectively validated in v2; the other
family RSS fits remain log-linear.

PoW is stochastic. The model preserves all twenty trial timings per program,
reports each stage's median, p90, maximum and coefficient of variation, and
widens stochastic-stage intervals by the **full observed training trial ratio
range** plus leave-one-training-program-out median error. Other stages use
empirical p05/p95 ratios with the same leave-one-out widening. The intervals
are diagnostic ranges on this host, not calibrated confidence intervals or
guaranteed PoW tails. No held-out timing may be used to choose the model or
adjust the thresholds.

The predeclared local gate requires, for **each** family, four held-out
programs with twenty trials each; whole-wall program-median p90 relative error
at most 25%, trial interval coverage at least 80%, and median interval upper
bound at most 8× the measured median. Proof bytes and prover RSS each require
p90 program-median error at most 10% and trial interval coverage at least 80%.
Any family failing any criterion fails the local gate. Automatic lowering
selection remains disabled even if all criteria pass: profile soundness
equivalence, paired-profile comparisons, additional hosts and cached-setup
costs need separate evidence.

## Run after source and CPU freeze

Run these commands from the repository root. Keep the same compiler sources,
dependency commit, Zig version, host and proof policy throughout. Build each
split before its proof phase so its compiler fingerprint can be inspected.
The model is serialized **before** any validation package build or proof.

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v3.py \
  --split train --phase build --out zig-out/s31/whole-prover-v3-train
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v3.py \
  --split train --phase prove --out zig-out/s31/whole-prover-v3-train
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v3.py fit \
  zig-out/s31/whole-prover-v3-train/whole-prover-corpus.json \
  --out zig-out/s31/whole-prover-v3-model.json
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v3.py \
  --split validation --phase build --model zig-out/s31/whole-prover-v3-model.json \
  --out zig-out/s31/whole-prover-v3-validation
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v3.py \
  --split validation --phase prove --model zig-out/s31/whole-prover-v3-model.json \
  --out zig-out/s31/whole-prover-v3-validation
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v3.py evaluate \
  zig-out/s31/whole-prover-v3-model.json \
  zig-out/s31/whole-prover-v3-validation/whole-prover-corpus.json \
  --out zig-out/s31/whole-prover-v3-evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v3.py \
  zig-out/s31/whole-prover-v3-train/whole-prover-corpus.json \
  zig-out/s31/whole-prover-v3-model.json \
  zig-out/s31/whole-prover-v3-validation/whole-prover-corpus.json \
  zig-out/s31/whole-prover-v3-evaluation.json \
  --out design/s31/measurements/language/whole-prover-cost-v3-audit.json
```

The untracked `zig-out` directories hold the complete proofs, statements,
native reports and package artifacts. The tracked audit pins their digests and
summarizes held-out errors, intervals and controls; it is not a substitute for
the raw artifacts when independently replaying a trial.
