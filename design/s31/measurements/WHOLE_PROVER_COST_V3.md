# Whole-prover cost model v3.1

The [machine-readable protocol](whole-prover-cost-v3.json) was frozen before
the v3.1 native measurement. It addresses the version mismatch between the [v1
whole-prover run](STAGE_AWARE_COST_V1.md) and the [v2 arithmetic RSS
follow-up](ARITHMETIC_RSS_V2.md): all v3 wall, proof-byte and peak-RSS targets
must be trained and evaluated under **one compiler fingerprint**. This is a
prospective test of prediction, not a claim that proving became faster.
Before the first timed training proof, the runner was tightened to record a
stable SHA-256 pseudonym of the host name and the CPU model. The model requires
exact train/held-out host-object equality. No raw host name is saved in the
tracked audit. This pre-timing tooling amendment did not change the protocol
JSON or any source program, package, target or accuracy threshold.

## Training-only correction before held-out work

The first v3 train split built all 18 packages and verified all 360 native
proofs, but fitting stopped: the generic circuit cost report records the same
292 raw rows, 512 padded rows and 4,096 preprocessed cells for **every**
direct-chip program. Chip work lives in a separate component, so a log fit on
generic padded rows has no distinct training feature. There were **no**
validation packages, proofs or outcomes at that point. The initial train
artifacts remain in a separate untracked directory as a failed-fit diagnostic
and are excluded from the v3.1 fit and audit.

V3.1 adds two features derived only from the generated, sealed typed component
manifest. `chip_trace_cells` sums `2^trace_log_size × (base_trace_columns +
interaction_trace_columns)` over the generic and chip AIR components.
`chip_fri_domain_rows` is their maximum `2^trace_log_size`. They encode total
committed trace work and the largest FRI tier, respectively. The training-only
geometry that exposed the omission is:

| Chip rounds | Generic circuit rows | Chip rows | Total trace cells | Largest FRI domain |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 512 | 16 | 10,512 | 512 |
| 64 | 512 | 64 | 11,328 | 512 |
| 256 | 512 | 256 | 14,592 | 512 |
| 1,024 | 512 | 1,024 | 27,648 | 1,024 |
| 4,096 | 512 | 4,096 | 79,872 | 4,096 |

For chip programs, witness and non-PoW prove stages use trace cells; proof
bytes and verifier wall use the FRI domain; setup, PoW and process overhead
use a constant. Chip RSS uses the same positive-affine baseline-plus-work form
as direct-gate arithmetic RSS, with trace cells as its work feature. On the
failed-fit **training data only**, its positive fit had a baseline of 8,748,853 bytes
and at most 2.09% leave-one-program-out relative error. Other families' raw,
padded, preprocessing and hash-work features varied as planned. Every recorded
native stage timer was positive, so no timer floor was introduced. The model
formula and gates were frozen before a fresh v3.1 training build/proof run; the
new model must still be frozen before any held-out build or trial.

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
publisher rechecks each saved package, component manifest, source-to-package
binding, assignment digest, assignment-to-public-statement match, proof digest,
full trial report, and changed-public-statement diff.

## Predictor and uncertainty

The model fits a simple per-family curve for each native stage using **training
program medians only**. Witness, setup, prove excluding PoW, runtime overhead,
unattributed process time, and native verifier process time remain separate.
Direct gate and chip profiles expose interaction PoW and FRI PoW timers; the
generic hash prover exposes only an opaque prove timer that includes PoW. The
whole wall prediction sums the stage predictions. Proof bytes and peak RSS
have their own curves. Direct-gate arithmetic RSS uses the fixed-baseline plus
per-padded-row positive affine form prospectively validated in v2. Direct-chip
RSS uses a positive affine fit over sealed-manifest trace cells. Hash and
fixed-width RSS fits remain log-linear.

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

## Pinned v3.1 outcome

The [tracked audit](language/whole-prover-cost-v3-audit.json) records the
prospective validation under compiler fingerprint
`1ed227604daba04c04835dd809809eca545f86ca768d3fadfd33b7e4a8cc7344`
and protocol SHA-256
`e93c880b08e9e9ac7a0d1a58be837cb5896758b446a81b469d78280ae26702ef`.
The model SHA-256
`c3210b36a4f0bee0efc7efbac60e78894f23f12a211f85c347cd0ffca02c9721`
was recorded externally at 2026-10-10 17:52:55 UTC, **before** validation
package builds and proofs. The publisher requires that exact hash, then
independently refits training and replays held-out evaluation. The measured
compiler revision is an audit of that pinned source; subsequent compiler
changes require a new cohort before these predictions can be used.

Fresh training comprised 18 packages and 360 verified proofs; fresh validation
comprised 16 packages and 320 verified proofs. Every proof passed its native
verifier and independent output oracle, and every changed-public-claim control
was rejected. Saved-artifact checks matched 680 assignment digests, 680 public
statements, 680 proof digests and 34 source-to-package bindings. The native
verifiers and oracles were **not rerun** by the publisher; it checks their saved
reports and artifacts. Package-build wall time was separately measured:
training min/median/max 50.89/51.72/67.78 seconds; validation
51.51/52.03/68.20 seconds. Builds were fresh packages under an unspecified
existing Zig cache state; package-build RSS was unavailable.

| Family | Paired wall p90 error | Wall interval coverage | Wall upper / measured median | Proof bytes p90 error | Prover RSS p90 error | Prover RSS coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Arithmetic | 56.11% | 98.75% | 11.14× | 3.58% | 1.69% | 100% |
| Direct chip | 24.75% | 96.25% | 8.46× | 2.40% | 3.13% | 78.75% |
| Fixed width | 23.74% | 100% | 26.10× | 2.36% | 2.54% | 100% |
| Hash | 5.49% | 100% | 2.35× | 0.43% | 0.04% | 100% |

The predeclared **local gate failed**. Arithmetic wall error exceeded 25%; the
arithmetic, chip and fixed-width wall intervals exceeded the 8× width limit;
chip RSS coverage fell below 80%. Proof-byte p90 errors and RSS p90 errors
were below their 10% thresholds in all four families. These are prediction
errors, not proving speedups. In the held-out stage diagnostics, arithmetic
FRI PoW had 90.6% median relative error and 103.1% p90 error, while its
non-PoW prove stage had 15.6% median error. PoW variance and constant-stage
fits dominate the weak wall predictions. No held-out-informed retuning was
performed, and **automatic lowering selection remains disabled**. The model
predicts fresh-process prover plus verifier wall time; it does not predict
compile-to-proof latency, cached setup, or verifier peak memory.

The untracked `zig-out` directories hold the complete proofs, statements,
native reports and package artifacts. The tracked audit pins their digests and
summarizes held-out errors, intervals and controls; it is not a substitute for
the raw artifacts when independently replaying a trial.
