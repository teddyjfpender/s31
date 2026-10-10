# Whole-prover cost model v4: expected wall time

The [frozen protocol](whole-prover-cost-v4.json) defines a **new** train and
held-out corpus. It follows the [failed v3.1 audit](WHOLE_PROVER_COST_V3.md).
No v3.1 held-out observations are inputs to v4 fitting, interval calibration,
or model choice. Automatic lowering selection remains disabled.

## Training-only diagnosis

The v3.1 *training* split contains five direct-gate arithmetic programs with
the same 26-bit PoW policy. Their FRI PoW sample medians were about 50, 67,
67, 98 and 140 ms. The entire non-PoW prove-stage sample median was only
about 1.4–7.5 ms. The v3.1 log-linear fit assigned FRI PoW a negative slope
against padded rows, even though PoW difficulty did not change. That is a
symptom of fitting transcript-dependent 20-trial medians as if they were a
source-size trend. The training leave-one-program-out error and independent
min/max envelopes were then multiplied per stage, making the whole-wall upper
bound much wider than the observed whole-process distribution.

As an exploratory check **using that training split only**, a constant PoW
mean plus source-dependent non-PoW stage means gave 23.6% arithmetic p90
leave-one-program-out relative error against program trial means. The pooled
whole-wall out-of-fold trial ratio had a 95th percentile of 1.95. These are
diagnostics from 20 trials per old training program, not v4 validation or a
claim of reliable prediction. V4 collects 100 fresh assignments per program
to reduce sample-mean noise before any held-out decision.

## Predicted quantity and formulas

For one source program, the target is the arithmetic mean of 100 fresh prover
process wall times plus their native verifier process wall times. This is a
sample estimate of expected wall time under one host and one compiler
fingerprint. Package construction is measured separately and excluded from
the target. Every prover process constructs cold native setup. Zig compiler
cache state is observed but not reset. Verifier peak memory is recorded but
not predicted.

For each family and exposed stage, fit a log-linear curve to **training program
stage means** using the declared raw rows, padded rows, preprocessing cells,
hash work, or authenticated direct-chip manifest geometry. When the feature is
`constant`, fit the mean of the program means. Direct-gate and direct-chip
interaction and FRI PoW stages use this constant: the configured 26-bit
difficulty is fixed, and new transcripts supply independent stochastic work.
Generic hash proving still has opaque PoW inside its prove stage, which uses
`hash_work`. The predicted whole-process mean is the sum of its fitted stage
means, matching linearity of expectation.

For a trial interval, omit each training program in turn, fit the stage model
on the remaining programs, and divide every omitted program's observed
whole-process trial wall time by its out-of-fold predicted mean. Pool these
ratios **after** leaving the program out. The prospective lower and upper
trial limits are the 5th and 95th ratio percentiles times the full-training
predicted mean. This captures cross-stage dependence and process outliers
without multiplying worst-case stage limits. It is an empirical interval on
this host, not a calibrated confidence or PoW tail bound. Program mean
uncertainty and trial latency variability are separate quantities.

Proof bytes and prover peak RSS retain the v3.1 point-fit formulas and their
training leave-one-program-out interval construction. Direct-gate arithmetic
RSS is affine in padded rows; direct-chip RSS is affine in authenticated chip
trace cells; other families use log-linear RSS. Proof-byte fits use padded
rows, except direct chip uses the authenticated FRI domain rows. Their target
and gate remain per-program trial medians.

## Prospective decision gate

The v4 train split contains 18 programs and the held-out split contains 16.
They have distinct generated source bytes and assignment values. Each has 100
fresh trials, native verification, a rejected changed-public-claim control,
and an independent output oracle check. The model and its SHA-256 must be
recorded **before any held-out package is built**. Every package, source and
trial must share the protocol SHA, compiler fingerprint, host pseudonym,
profile and FRI policy. The generated one-call direct-chip manifest is sealed
in each chip package. A separate measurement-tool SHA-256 covers all S31
benchmark and frontend Python files; it must match across package builds,
timed trials, frozen model and audit replay. This closes a gap left by the
compiler fingerprint, which does not include benchmark scripts.

Each family needs at least four held-out programs. Their expected-wall
program-mean p90 relative error must be at most 25%; whole-wall trial interval
coverage at least 80%; and median ratio of interval upper bound to measured
program mean at most 8×. Proof bytes and prover RSS each need at most 10% p90
program-median error and at least 80% trial interval coverage. Failure of any
criterion fails the local gate. A local pass would still leave automatic
lowering disabled until separate soundness and cross-host work is done.

## Reproduction

Run from the S31 repository root on an otherwise idle host, using one pinned
compiler source and stwo-zig engine commit. Keep complete native artifacts in
ignored `zig-out`; publish the hashes and summary audit under
`design/s31/measurements/language/`.

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v4.py \
  --split train --phase build --out zig-out/s31/whole-prover-v4-train
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v4.py \
  --split train --phase prove --out zig-out/s31/whole-prover-v4-train
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v4.py fit \
  zig-out/s31/whole-prover-v4-train/whole-prover-corpus.json \
  --out zig-out/s31/whole-prover-v4-model.json
shasum -a 256 zig-out/s31/whole-prover-v4-model.json
# Record the exact model hash outside the corpus before proceeding.
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v4.py \
  --split validation --phase build --model zig-out/s31/whole-prover-v4-model.json \
  --out zig-out/s31/whole-prover-v4-validation
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v4.py \
  --split validation --phase prove --model zig-out/s31/whole-prover-v4-model.json \
  --out zig-out/s31/whole-prover-v4-validation
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v4.py evaluate \
  zig-out/s31/whole-prover-v4-model.json \
  zig-out/s31/whole-prover-v4-validation/whole-prover-corpus.json \
  --out zig-out/s31/whole-prover-v4-evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v4.py \
  zig-out/s31/whole-prover-v4-train/whole-prover-corpus.json \
  zig-out/s31/whole-prover-v4-model.json \
  zig-out/s31/whole-prover-v4-validation/whole-prover-corpus.json \
  zig-out/s31/whole-prover-v4-evaluation.json \
  --expected-model-sha256 THE_EXTERNALLY_RECORDED_HASH \
  --out design/s31/measurements/language/whole-prover-cost-v4-audit.json
```

The publisher checks saved proof/assignment digests, exact public statements,
source-to-package bindings, native verifier/oracle reports, and independent
fit/evaluation replay. It does not rerun every native proof or oracle. The
tracked audit cannot replace the raw packages and proof files for independent
reverification.
