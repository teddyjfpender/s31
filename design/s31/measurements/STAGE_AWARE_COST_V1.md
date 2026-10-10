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
  --split train --phase build --out zig-out/s31/stage-aware-train-v1
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_stage_v1.py \
  --split train --phase prove --out zig-out/s31/stage-aware-train-v1
python3 src/frontends/s31/benchmarks/stage_aware_predictor_v1.py fit \
  zig-out/s31/stage-aware-train-v1/stage-aware-corpus.json \
  --out zig-out/s31/stage-aware-model-v1.json
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_stage_v1.py \
  --split validation --phase build --model zig-out/s31/stage-aware-model-v1.json \
  --out zig-out/s31/stage-aware-validation-v1
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_stage_v1.py \
  --split validation --phase prove --model zig-out/s31/stage-aware-model-v1.json \
  --out zig-out/s31/stage-aware-validation-v1
python3 src/frontends/s31/benchmarks/stage_aware_predictor_v1.py evaluate \
  zig-out/s31/stage-aware-model-v1.json \
  zig-out/s31/stage-aware-validation-v1/stage-aware-corpus.json \
  --out zig-out/s31/stage-aware-evaluation-v1.json
python3 src/frontends/s31/benchmarks/publish_stage_aware_cost_v1.py \
  zig-out/s31/stage-aware-train-v1/stage-aware-corpus.json \
  zig-out/s31/stage-aware-model-v1.json \
  zig-out/s31/stage-aware-validation-v1/stage-aware-corpus.json \
  zig-out/s31/stage-aware-evaluation-v1.json \
  --out design/s31/measurements/language/stage-aware-cost-v1-audit.json
```

Keep the full untracked `zig-out` corpora: they include proof files, native
verifier reports, changed-claim controls, package artifacts and raw timings.
The tracked summary should pin their digests and the exact model and protocol
used. The run should be repeated on a separately named host before any
general-purpose cost claim.

## Prospective result, 2026-10-10

The [pinned audit](language/stage-aware-cost-v1-audit.json) is the reviewable
result. It independently refits the training corpus, replays the frozen model
on validation, checks every saved proof's length and SHA-256, checks each full
trial report against the compact corpus, and checks that each saved changed
statement differs at exactly the reported public word. The model was frozen
at SHA-256 `f77ba341f216baf68cbaef6920db9b0a64edae2513af90fd4ca7b0600b20105b`
before any validation package or proof was made. All 25 packages used compiler
SHA-256 `d9ee38fc2e0ecc38776e72e5b40598b896a9545e030b50dd290935561e7c185f`.
Thirteen training and twelve validation programs each had twenty distinct
witnesses. **500/500** native proofs verified, changed public claims rejected,
and independent value-oracle checks passed. Training and validation source and
assignment digests are disjoint.

| Held-out target, 12 programs | Median relative error | P90 relative error | Maximum |
| --- | ---: | ---: | ---: |
| Prover plus native verifier process wall | 7.86% | 20.93% | 23.38% |
| Proof bytes | 0.59% | 3.46% | 4.28% |
| Prover peak RSS | 1.70% | 8.75% | 18.03% |

| Family, four validation programs each | Wall p90 error | Proof bytes p90 error | Peak RSS p90 error | Wall trial interval coverage |
| --- | ---: | ---: | ---: | ---: |
| Arithmetic recurrence | 19.59% | 4.08% | **15.34%** | 95% |
| Signed quotient-only division | 22.41% | 1.72% | 2.39% | 95% |
| Deeper BLAKE2s chains | 7.94% | 0.45% | 0.07% | 95% |

The predeclared local gate **failed** because arithmetic peak RSS p90 error
exceeded its 10% limit. The 512-round arithmetic program was the largest miss:
10.81 MiB measured versus 12.76 MiB predicted, an 18.03% error. The other
wall, proof-byte, interval-coverage and interval-width criteria passed on this
host. This is a cost-model result, not evidence that the circuit or proving
algorithm became faster. Automatic lowering selection remains disabled.

The wall intervals use empirical training p05/p95 trial ratios widened by the
largest training leave-one-program-out stage error. They covered 95% of the
held-out **individual trials** in each family. Their median upper bound was
4.99 times the observed program median for arithmetic, 4.64 times for signed
division, and 1.82 times for hash. These are diagnostic predictive intervals,
not calibrated 95% confidence bounds or tail guarantees. Proof-byte trial
coverage was 100%, 100% and 98.8% respectively; RSS trial coverage was 100%
for all three families.

The largest measured stage by median share was FRI PoW for direct-gate
arithmetic (about 65%) and signed division (about 60%). It also had 22–23%
median held-out stage-median error. Their non-PoW prove-stage median errors
were 4.2% and 1.6%. Hash uses the generic gate prover, whose opaque prove
timer accounts for about 77% of the summed median stages; separate hash PoW
timers are unavailable, so that share cannot be assigned to PoW. These stage
shares are descriptive sums of program-median timers, not causal attributions
of each wall-time outlier.

Training package-build wall ranged from 52.75 to 70.75 seconds (median 55.03);
validation ranged from 51.85 to 67.66 seconds (median 52.12). Every package
was fresh at its output path, while the Zig compiler cache remained
uncontrolled. Package build is excluded from the predicted proof latency.
An earlier three-package build attempt was stopped before any timed proof when
a direct-chip manifest component label lifetime bug was found. Those packages
were discarded; the full 25-package run above used the fixed compiler digest.

The next model iteration should predeclare an arithmetic RSS baseline plus
padded-tier feature, validate it on **new** programs and witnesses, and repeat
the whole experiment on another host. It should also expose PoW timers for the
generic hash prover if that profile is to receive a stage-specific model.
Neither change should be tuned against the twelve held-out outcomes above.
