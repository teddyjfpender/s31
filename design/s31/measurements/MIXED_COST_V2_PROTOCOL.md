# Prospective mixed whole-prover cost baseline v2

The executable study is [the v2 runner](../../../src/frontends/s31/benchmarks/mixed_cost_v2/README.md).
This document fixes the interpretation before the first native trial. The
machine-readable protocol is `language/mixed-cost-v2-protocol.json`; it is
committed before building any v2 package. The exact fitted model, training
corpus, and model anchor are committed before the first held-out build.

## Question and units

Can a small training corpus predict **one fresh proof plus independent native
verification** on four unseen mixed-chip programs on one pinned machine? The
primary target is the sum of the prover and external verifier process wall
times, measured by monotonic endpoints. Package build wall is reported on its
own. This is a local whole-prover prediction experiment, with proof bytes as a
second target. It is neither an optimization comparison nor a cross-machine
estimate.

All eight programs have one record ABI v2 public input and one public output,
with four M31 lanes. Every proof uses a new valid eight-word public statement.
The training sources are control and deep32 at two and six chip calls each.
The held-out sources are feeder and fork at four and six calls each. There are
20 independently generated statements per source: 80 training and 80 held
out. Source shape, call count, generated source bytes, and all statement and
assignment hashes are committed in the protocol. Claims must be distinct
from each other and from the earlier mixed cost/phase inventories. No earlier
timing values enter this study.

The runner builds eight ReleaseFast `direct-mixed-general` source packages,
one per program, at a frozen compiler, engine gitlink, Zig executable, host,
and tool hash. Every proof must pass its source-embedded external native
verifier. A different, ABI-valid public result must fail specifically with
`InvalidMixedInteractionNonce`. The auditor replays both checks against the
retained native proof, statement, package binaries, and stderr. The package's
six stage timers must sum to its package total and fit inside prover process
wall; the native phase timers must fit inside their native stage. Stage and
phase values are diagnostic evidence only, never model features.

## Model fixed before observation

For each training program, compute the median of its 20 trials. Predict
first-verified wall for **every** held-out program using the median of those
four training-program wall medians. Predict proof bytes by ordinary least
squares linear regression of four training-program proof-size medians on
chip call count, with a required positive slope and intercept. Save the median
training proof-size median as a constant-size baseline. There is no refit
after held-out observation.

For each target, take the 5th and 95th percentile of the 80 training trial
actual/predicted ratios, using linear interpolation. Clamp the lower ratio to
at most one and upper ratio to at least one. Multiply these two ratios by the
held-out center prediction to obtain a descriptive band. It is not a
confidence interval and has no distribution-free coverage guarantee.

## Predeclared decision rule

Report each held-out program's predicted center, observed median, median
relative error, band limits, covered trial count, and package build wall.
Report the median absolute percentage error and p90 median relative error
over the four held-out programs, both targets, plus the proof-constant
baseline error. The four gates are:

| Metric | Pass threshold |
| --- | ---: |
| First-verified wall p90 program-median relative error | ≤ 30% |
| Proof-byte p90 program-median relative error | ≤ 10% |
| Wall trial band coverage | ≥ 70% of 80 |
| Proof-byte trial band coverage | ≥ 80% of 80 |

Only if all four gates pass, all 160 proofs and changed-claim controls pass,
the model was committed before held-out builds, and the native replay audit
passes, may the report call the baseline **locally accurate for this pinned
host and profile**. Otherwise the result is a failed or inconclusive local
baseline. Trial ranges and any host contention must be reported alongside
the gates. A pass does not justify automatic lowering, a speedup claim,
cross-machine reliability, or tail-latency prediction.
