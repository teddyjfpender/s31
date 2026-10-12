# Whole-prover cost evidence

The cost vector for a generated S31 proof has five measured parts: package
build, witness generation, native setup, proof generation, and native
verification. Proof generation includes interaction PoW and FRI/PCS PoW.
Proof bytes and peak resident memory are separate outputs. A raw or padded AIR
row count is an input feature, not a substitute for these measurements.

`s31 trial` now records process wall time and OS-reported peak RSS for both
the prover and generated verifier. Its internal runtime timer reports witness,
setup and proof generation. When the prover prints both PoW timers, the report
computes `prove_excluding_pow = prove - interaction_pow - fri_pow` and rejects
an inconsistent negative residual. The `total through verification` timer
allows an additional residual for serialization, internal self-verification,
and other native runtime work. The process-wall residual also includes startup,
allocator initialization, and the small `/usr/bin/time` wrapper cost. Those
residuals are descriptive, not independently timed stages.

Each `trial` executes a **new prover process**. Native setup builds its fixed
preprocessed commitment in that process, so every observation includes cold
native setup. Loading a prebuilt sealed package avoids compiler build time;
it does not reuse native setup. `s31 tune --warmup` launches a separate process
per profile. It can warm operating-system caches but cannot turn subsequent
measurements into cached-commitment proofs. A true repeated-witness,
in-process cached-setup benchmark needs a persistent native prover API and a
separate measurement mode.

## Reproducible corpus

From the repository root:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover.py \
  --samples 5 --out zig-out/s31/whole-prover-corpus
```

The corpus proves distinct assignments for a four-lane arithmetic record,
a private BLAKE2s Merkle parent, and signed `i32` division. It uses a direct
gate profile for arithmetic and division and the generic gate profile for
the BLAKE2s example. Each trial requires native verifier acceptance and
rejection of a changed public claim. Its output contains source and assignment
digests, package-build wall time, visible AIR size, proof size, per-process
memory, stage timers, and an observed cost summary. The original trial reports
and proof artifacts stay under `--out` for audit.

Package-build wall time covers source lowering, compiler fingerprinting, Zig
build or package verification, native package checks, and manifest writing.
`package_reused` says whether a valid sealed package already existed at the
output path. If true, the measured call verifies and loads that package; it
does not compile it. If false, a package is materialized, but Zig's shared
compiler cache is **uncontrolled**: this is not a guaranteed cold compiler
build. The corpus records package-build peak RSS as `null` because Python's
build routine invokes Zig subprocesses and this benchmark does not yet wrap
the complete build process with a resource meter. The native prover and
verifier RSS measurements remain available separately.

The summary reports minimum, median, maximum, median absolute deviation, and
interpolated p90 for each available metric. It counts observations separately
for each stage; an unavailable PoW timer or peak RSS is `null`, never zero.
At least five distinct witnesses are recommended for a first local comparison.
Even five is too small for a stable tail-latency estimate. Repeat on the same
machine and build when changing lowerings, and compare paired assignments.
PoW search depends on the transcript and can dominate small circuits, so
compare both complete latency and its measured components.

Peak RSS comes from Darwin `/usr/bin/time -l` or GNU `/usr/bin/time -f %M`.
It is the OS high-water mark of the measured native command under that tool's
semantics; it is not the sum of all concurrent memory use. On other hosts or
if the output cannot be parsed, memory is unavailable. Process wall includes
the resource-wrapper overhead. The profiler neither changes proof parameters
nor substitutes an estimated proof duration for a measured one.

## Model boundary

The current model describes an observed corpus and one fresh native process
per proof. It does **not** predict unseen AIRs, batch sizes, cached setup,
different hardware, or protocol-level soundness. The next reliable predictor
needs held-out programs, multiple scales per operation family, repeated
witnesses, and out-of-sample error bounds for latency, proof bytes and memory.
Automatic lowering selection should wait for that validation and an explicit
soundness-equivalence review of the candidate proof profiles.

## Held-out model experiment

The larger corpus generator varies arithmetic recurrence rounds (16, 64, 256,
1024), BLAKE2s chain depth (1 through 4), and signed division width (8, 16,
32, 64 bits). It creates four source programs in each family and, by default,
five distinct valid assignments per program. The generated arithmetic and
hash outputs are checked against the independent value oracle before native
proof measurements. The native trial still performs the public-claim mutation
control. The runner builds every package before proving, then rotates through
programs once per assignment index; the report records both orders. This
suite does not mix Bitcoin or recursive workloads into the fit.

Run it after package/compiler sources are stable; it builds twelve sealed
packages and can take substantial time and memory:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_multiscale.py \
  --samples 5 --out zig-out/s31/whole-prover-multiscale
python3 src/frontends/s31/benchmarks/whole_prover_predictor.py \
  zig-out/s31/whole-prover-multiscale/multiscale-corpus.json \
  --out zig-out/s31/whole-prover-multiscale/held-out-evaluation.json
```

The evaluator holds out one **entire source program** at a time. It trains a
two-parameter log-linear fit using only other programs in the same family:

```text
log(predicted cost) = intercept + slope × log(static scale)
```

For all three targets—complete prover-plus-verifier wall time, proof bytes,
and prover peak RSS—static scale is the sum of padded component rows. The
separate family intercept can absorb a fixed table cost, but this one-feature
model cannot predict a new fixed-table layout. Each program contributes one
median measured cost; its assignments never cross the train/test boundary.
The evaluator rejects duplicate source
digests, mixed compiler/proof profiles within a family, and repeated
assignment digests. It reports measured and predicted values, absolute and
relative error for each held-out program, plus median/p90 errors by metric.
Per-program measured MAD and p90 show witness and PoW variability separately
from model prediction error.

An empirical interval expands the prediction by the largest training
leave-one-program-out log error. This is a diagnostic envelope, **not a
calibrated confidence interval**. It does not incorporate the within-program
MAD into its bounds. The cost-accuracy gate requires at least
three families with four programs each, p90 relative error at most 20%, maximum
relative error at most 35%, and at least 80% held-out coverage by these
empirical intervals for each metric. The evaluator disables automatic
lowering selection even if that gate passes: one host, a few scales, variable
PoW, and no profile-soundness equivalence are insufficient grounds for a
compiler decision. A failed gate is direct evidence that this simple model
should not be used to predict a candidate lowering's cost.

### Measured outcome, 2026-10-10

The [pinned audit summary](language/whole-prover-heldout-2026-10-10.json) records
one local host, twelve sealed programs, five distinct assignments each, and
60/60 native proof acceptances, changed-claim rejections, and independent
oracle passes. All twelve packages have one compiler digest. The generator
and saved trial reports are the reproducible source of each number.

| Held-out target | Median relative error | P90 relative error | Maximum |
| --- | ---: | ---: | ---: |
| Prover plus native verifier process wall | 30.6% | 79.1% | 100.8% |
| Proof bytes | 2.33% | 6.74% | 9.79% |
| Prover peak RSS | 1.03% | 4.17% | 8.02% |

All three targets have 12/12 held-out predictions. An empirical interval was
available for only 10/12 programs per target because two arithmetic scales
share a 512-row padded tier. The wall-time interval covered 7/10 of those
held-out values. The accuracy gate failed and automatic lowering selection
remains disabled. Package-build wall time was measured separately and ranged
from about 50 to 71 seconds in this run; Zig's shared compiler cache was not
isolated, so those numbers are neither cold-build baselines nor a predictive
compiler model.

| Family | Whole-process wall median error | Proof-byte median error | RSS median error |
| --- | ---: | ---: | ---: |
| Arithmetic recurrence | 62.5% | 2.30% | 2.31% |
| BLAKE2s chain | 9.42% | 1.35% | 0.042% |
| Signed division | 40.1% | 4.30% | 2.31% |

To diagnose the wall-time failure, the pinned report also applies the same
frozen padded-row fit to native stages **after** the headline evaluation. These
are exploratory errors and do not enter the gate. Arithmetic and signed
division show median held-out errors of 20.6% and 11.7% for proving excluding
PoW, versus 53.3% and 48.0% for FRI PoW. Their observed FRI-PoW median
absolute deviations are about 70.2% and 44.5% of the respective stage
medians. Cold native setup errors are 7.3% and 5.6%. Generic BLAKE2s does not
print separate PoW timers, so its PoW and non-PoW stage errors are unavailable.
The 16- and 64-round arithmetic programs both pad to 512 rows, while their
raw work differs; this is a real step in the cost surface, not evidence for a
smooth latency law.

### Original follow-up proposal (superseded)

The following was the design sketch after the first held-out corpus. The
later, executable [stage-aware v1 protocol](stage-aware-cost-v1.json) was
committed before its native timings and is the authoritative split and gate
for that run. Its one-host signed quotient-only transfer leaves the proposed
second-host and unsigned-transfer checks for future work.

Freeze the next model and its thresholds **before** collecting new native
timings. Use new source programs and independent witness seeds: arithmetic
round counts 32, 128, 512 and 2048; BLAKE2s chain depths 5 through 8; signed
128-bit division as an extrapolation control; and unsigned 8–64-bit division
as a separately labeled transfer test. Measure at least twenty distinct
witnesses per program on two named hosts, rotate program order, and retain
complete process wall, stage timers, proof bytes, RSS and package-cache state.
Do not merge unsigned and signed results into one family accuracy number.

Predeclare a stage-aware feature set: raw and padded rows by component,
preprocessed/fixed-table cells, FRI schedule, and both PoW difficulty settings.
Fit deterministic setup and non-PoW stages separately; treat PoW as a measured
distribution conditioned on its policy rather than a deterministic function
of AIR rows. Add process startup and native verification only after those
components are measured. Evaluate on the new programs and second host without
refitting to their outcomes. A persistent native prover API is needed to
measure cached setup separately. Keep automatic lowering selection disabled
until the prospective error gate and a profile-soundness comparison both pass.

The first prospective follow-up and its measured outcome are recorded in
[Stage-aware cost v1](STAGE_AWARE_COST_V1.md). Its independent held-out set has
500 total training/validation native proofs and materially better wall-time
prediction, but the predeclared local gate still fails on arithmetic peak RSS.
