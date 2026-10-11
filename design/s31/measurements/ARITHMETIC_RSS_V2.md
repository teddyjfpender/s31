# Arithmetic RSS follow-up, predeclared v2

The [machine-readable protocol](arithmetic-rss-v2.json) is pinned before any
v2 native package build or proof timing. This is a **targeted follow-up** to
the arithmetic peak RSS failure in [stage-aware v1](STAGE_AWARE_COST_V1.md).
It is not a replacement validation of all whole-prover targets.

The v1 training programs show a fixed prover memory baseline plus increasing
memory as padded arithmetic rows grow. An ordinary log-linear line cannot
represent a fixed byte baseline. A positive affine model is a physical
hypothesis: one process/runtime baseline and one per-padded-row allocation
term. On the **v1 training split only**, leave-one-program-out errors for this
candidate were 0.25%, 0.38%, 3.81%, 2.77% and 5.05%. The v1 validation
programs revealed the original failure, so they are development evidence and
will never be used to claim that this candidate was validated.

The new training split uses five source programs at rounds 24, 96, 384, 1536
and 6144. The independent validation split uses four new round counts 48,
192, 768 and 3072 in **two** bodies: `square; add 11` and `square; multiply 3;
add 11`. This tests interpolation across padded tiers and transfer to another
direct-gate recurrence body. All programs have twenty distinct deterministic
witnesses; train and validation seeds and source digests must be disjoint.
Every trial requires native proof acceptance, changed-public-claim rejection,
and independent value-oracle agreement. The compiler fingerprint and proof
policy must match across the entire run.

Fit the positive affine model on training program **medians** only. Freeze the
model file before validation package builds. For context, fit a training-only
log-linear baseline in the same file; do not select a model by validation
error. The candidate interval adds the maximum training leave-one-program-out
absolute error to empirical training within-program p05/p95 residuals. It is
a diagnostic interval, not a calibrated confidence interval. The protocol
pins p90/max point-error, per-body interval coverage and interval-width gates.

The full prover wall, proof bytes, verifier wall and other stages may be saved
as raw telemetry, but **only prover peak RSS** enters this v2 accuracy gate.
Even a local pass cannot enable automatic lowering: other families, hosts,
full-process latency, proof bytes, cached setup and proof-profile soundness
still need independent validation.

## Prospective result, 2026-10-10

The [pinned audit](language/arithmetic-rss-v2-audit.json) records the frozen
model, held-out predictions, all predeclared thresholds, package geometry,
source and proof digests, and the native trial controls. Five training programs
and eight held-out programs used compiler SHA-256
`e1e3ca011bf671cd5af8f76966ea98eec3f8340870220802957f66e42d1e1dda`
on macOS arm64. The model was frozen at SHA-256
`8ee53fa40df5f5f6f739ebbe5f4c649833eb10b5ef401182fe3c826dc0cc077b`
**before** validation packages were built. All 260/260 native proofs verified;
all 260 changed-public-claim controls rejected; all 260 independent arithmetic
oracles agreed. The publisher also matched each saved proof and complete trial
report against the corpus.

The positive affine prediction for a program's median prover peak RSS was
`8,581,014 + 1,313.21 × padded_rows` bytes. The training-only log-linear
reference was retained for comparison. On the eight new held-out programs:

| Body | Programs | Median error | P90 error | Maximum error | Trial interval coverage | Median upper bound / measured median |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Both | 8 | 1.10% | 2.07% | 2.66% | 100% | 1.18× |
| Pair | 4 | 1.10% | 1.69% | 1.81% | 100% | 1.18× |
| Triple | 4 | 1.18% | 2.36% | 2.66% | 100% | 1.19× |

The predeclared **arithmetic RSS gate passed**: overall p90 error was below
10%, maximum error below 15%, each body's p90 below 12%, interval coverage
above 80%, and interval upper ratios below 1.5. The reference log-linear
model's overall p90 error was 15.44%. These are program-median relative errors;
the intervals are empirical diagnostic bounds, not calibrated 95% confidence
intervals or guarantees for a new host. The measured benefit here is improved
**prediction accuracy**, not a faster prover or smaller proof.

The earlier [v1 whole-prover run](STAGE_AWARE_COST_V1.md) used compiler SHA-256
`d9ee38fc2e0ecc38776e72e5b40598b896a9545e030b50dd290935561e7c185f`.
Its wall-time and proof-byte gates cannot be combined with this v2 RSS result
to assert a current-version whole-prover pass. A fresh wall/bytes/RSS corpus
under one compiler fingerprint is needed. Automatic lowering remains disabled.
All thirteen v2 packages were fresh at their output paths; their Zig compiler
cache was uncontrolled. Package-build peak RSS was unavailable because the
Python driver invokes Zig subprocesses.

## Reproduce after source freeze

Run from the repository root. The build and proof phases are separate so the
compiler digest and package cache state can be checked before timed proofs.

```sh
python3 src/frontends/s31/benchmarks/benchmark_arithmetic_rss_v2.py \
  --split train --phase build --out zig-out/s31/arithmetic-rss-v2-train
python3 src/frontends/s31/benchmarks/benchmark_arithmetic_rss_v2.py \
  --split train --phase prove --out zig-out/s31/arithmetic-rss-v2-train
python3 src/frontends/s31/benchmarks/arithmetic_rss_predictor_v2.py fit \
  zig-out/s31/arithmetic-rss-v2-train/arithmetic-rss-corpus.json \
  --out zig-out/s31/arithmetic-rss-v2-model.json
python3 src/frontends/s31/benchmarks/benchmark_arithmetic_rss_v2.py \
  --split validation --phase build \
  --model zig-out/s31/arithmetic-rss-v2-model.json \
  --out zig-out/s31/arithmetic-rss-v2-validation
python3 src/frontends/s31/benchmarks/benchmark_arithmetic_rss_v2.py \
  --split validation --phase prove \
  --model zig-out/s31/arithmetic-rss-v2-model.json \
  --out zig-out/s31/arithmetic-rss-v2-validation
python3 src/frontends/s31/benchmarks/arithmetic_rss_predictor_v2.py evaluate \
  zig-out/s31/arithmetic-rss-v2-model.json \
  zig-out/s31/arithmetic-rss-v2-validation/arithmetic-rss-corpus.json \
  --out zig-out/s31/arithmetic-rss-v2-evaluation.json
python3 src/frontends/s31/benchmarks/publish_arithmetic_rss_v2.py \
  zig-out/s31/arithmetic-rss-v2-train/arithmetic-rss-corpus.json \
  zig-out/s31/arithmetic-rss-v2-model.json \
  zig-out/s31/arithmetic-rss-v2-validation/arithmetic-rss-corpus.json \
  zig-out/s31/arithmetic-rss-v2-evaluation.json \
  --out design/s31/measurements/language/arithmetic-rss-v2-audit.json
```
