# Prospective stage-aware whole-prover cost experiment

The [frozen protocol](stage-aware-cost-v1.json) is the machine-readable design
for this experiment. It must be committed before new native timing is collected.
The earlier [held-out report](language/whole-prover-heldout-2026-10-10.json)
was used to choose features and expose failure modes; it is development data,
not validation evidence for this experiment.

## What the model predicts

Every proof uses a fresh native prover and verifier process. The output target
is their **combined process wall time**, with proof bytes and prover peak RSS
reported separately. Package build is measured but is not folded into this
latency predictor because the Zig compiler cache is uncontrolled. Native setup
is cold in every trial. No claim about cached setup is possible yet.

For direct-gate arithmetic and signed division, the prover reports individual
PoW timers. The model fits source-dependent medians for witness generation,
native setup, proving excluding PoW, interaction PoW, FRI PoW, native runtime
bookkeeping, unattributed process overhead, and native verification. PoW is
random search: the model also keeps a distribution of trial-to-program-median
ratios for each PoW stage. It never treats one PoW sample as a deterministic
function of AIR rows.

The generic BLAKE2s gate prover currently does not report PoW timers. Its
complete native `prove` timer is therefore one opaque stochastic stage. The
model does not label any part of it as PoW or claim isolated hash PoW behavior.
The other stages are still separate.

For each positive static feature and stage, fit one log-linear line per family
to the **training program medians**. Process overhead uses one constant median.
The feature-to-stage mapping is pinned in the JSON protocol. These deliberately
small models can fail on padded-row steps, fixed-table changes, extrapolation,
OS scheduling and different machines; the prospective evaluation measures
those failures rather than adjusting features after the fact.

Each stage interval combines a maximum leave-one-training-program-out log
residual with the empirical training trial/within-program-median p05 and p95
ratios. Whole-wall endpoints sum stage endpoints. This is a conservative
diagnostic interval, **not a calibrated confidence interval**: trial stages
can be correlated, and twenty witnesses per program are insufficient for tail
guarantees. Validation reports both program-median relative errors and the
fraction of individual trials inside each interval. The protocol also caps
interval width so a huge interval cannot satisfy coverage alone.

## Split and acceptance rules

The training set contains 13 programs: five arithmetic recurrence scales,
four BLAKE2s chain depths, and four signed division widths. The validation set
contains twelve **different source programs**: four new arithmetic scales,
four deeper hash chains, and signed quotient-only programs at four widths.
Training and validation use disjoint deterministic witness seeds; each has
twenty distinct valid witnesses per program. This tests interpolation,
extrapolation and a modest fixed-width output-shape transfer. It does not test
an arbitrary new chip, another host, or another proof profile.

All packages must use one compiler digest and each family one proof profile and
FRI policy. The runner rejects missing independent value-oracle checks, reused
assignment digests and failed changed-public-claim controls. Build all packages
within a source-stable window. Fit and serialize the model from the training
corpus **before** running validation proofs. The evaluator rejects source or
assignment leakage across splits.

The numerical pass gates, including per-family wall error, per-trial interval
coverage and useful interval width, are pinned in the protocol. If any gate
fails, report the error without refitting on validation. Even a local pass
does not enable automatic lowering selection: soundness equivalence among
profiles and validation on more hosts/scales are independent requirements.

## Reproduce

From the repository root, with compiler/package/runtime sources stable:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_stage_v1.py \
  --split train --out zig-out/s31/stage-aware-train-v1
python3 src/frontends/s31/benchmarks/stage_aware_predictor_v1.py fit \
  zig-out/s31/stage-aware-train-v1/stage-aware-corpus.json \
  --out zig-out/s31/stage-aware-model-v1.json
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_stage_v1.py \
  --split validation --out zig-out/s31/stage-aware-validation-v1
python3 src/frontends/s31/benchmarks/stage_aware_predictor_v1.py evaluate \
  zig-out/s31/stage-aware-model-v1.json \
  zig-out/s31/stage-aware-validation-v1/stage-aware-corpus.json \
  --out zig-out/s31/stage-aware-evaluation-v1.json
```

Keep the full untracked `zig-out` corpora: they include proof files, native
verifier reports, changed-claim controls, package artifacts and raw timings.
The tracked summary should pin their digests and the exact model and protocol
used. The run should be repeated on a separately named host before any
general-purpose cost claim.
