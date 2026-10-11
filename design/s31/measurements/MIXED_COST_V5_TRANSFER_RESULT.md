# Mixed-cost v4 predictor transfer to N=1 and N=8

**The prospective transfer fails one of eight preregistered per-source
gates.** The N=1 warm-wall median error is **38.39%**, above the frozen 35%
limit. N=8 passes all four gates. Both sources pass the proof-size center and
interval checks. This is a useful boundary for the current call-count-only
model, not a reason to refit or discard the run.

The [protocol](language/mixed-cost-v5-transfer-protocol.json), including exact
source and claim hashes, predictions, and limits, was committed as `e4ed1f4`
**before the first native build**. Its SHA-256 is
`3fccc8776a6408d45e84169707a91344ab175452757e28c4f349d7a77d2944d6`.
The frozen [v4 model](language/mixed-cost-v4-model.json) receives only call
count. This was one native timing run, with no score-selected rerun and no
model update.
The N=1/N=8 counts were chosen after a separate record-ABI proof smoke had
already run at those counts; the two source hashes, feeder DAGs, and all
claims here were new and their predictions were frozen before their builds.

| Source | Predicted warm p50 | Observed warm median | Relative error | Wall 90% interval coverage | Predicted proof center | Observed proof median | Proof error | Proof 90% interval coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `scaled_seed_n1` | 84.21 ms | 60.85 ms | **38.39% (fail)** | 18/20 = 90% | 70,007 B | 70,360 B | 0.50% | 17/20 = 85% |
| `weighted_scan_n8` | 88.34 ms | 105.72 ms | 16.44% | 20/20 = 100% | 171,831 B | 173,034 B | 0.70% | 20/20 = 100% |

The preregistered limits were wall median error ≤35%, wall interval coverage
≥70%, proof median error ≤10%, and proof interval coverage ≥70%, separately
for each source. The N=1 median miss is 3.39 percentage points past its
limit; its absolute prediction gap is 23.36 ms. The realized N=1 median FRI
PoW interval was 31.64 ms, and the N=8 interval was 71.10 ms. These are
post-proof descriptions, never predictor inputs. With 20 scored claims each,
stochastic PoW can materially move a program median; this small study cannot
separate that effect from other runtime variation with confidence.

**Post-hoc sampling diagnostic (not a score):** the frozen model's one-call
non-PoW center, using its median calibration residual, is about 28.98 ms;
the observed N=1 non-PoW median was 28.15 ms. Its fitted FRI exponential
median is 53.13 ms, versus the observed 31.64 ms. In 100,000 deterministic
Monte Carlo samples of 20 draws from that *unchanged* frozen wall model
(random seed `202610116`), 4.19% of sample medians were at or below the
observed N=1 median; 7.09% missed the same 35% median gate in either
direction. This makes the miss plausible under the model's PoW randomness,
but it is a lower-tail observation and does not rule out systematic bias.
The simulation was run after seeing the result and cannot change the
preregistered failure.

## Native geometry and cold/warm observations

Every package reported the configured 20-bit interaction and 26-bit FRI PoW.
Each native manifest matched the committed source hash, component roster,
tree-column totals, total constraint count, and its registry manifest digest.

| Source | Calls / component slots | Constraints | Commitment tree columns | Max / composition log size | First post-build verified wall | Immediate same-claim repeat | Package build wall |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| `scaled_seed_n1` | 1 / 3 | 30 | `[8, 29, 36, 8]` | 9 / 9 | 1,129 ms | 41.21 ms | 54.43 s |
| `weighted_scan_n8` | 8 / 17 | 163 | `[8, 148, 232, 8]` | 9 / 9 | 1,087 ms | 76.78 ms | 54.34 s |

Build wall is affected by Zig cache state; the two first-post-build values
are single startup observations. None were scored or predicted. N=1 and N=8
are outside the v4 fit counts of 3 and 7; N=8 also has 163 constraints and
232 interaction columns, more than any v4 observed seven-call geometry in
that study. These data test source/count transfer on one pinned host and
software stack, not arbitrary circuits or an alternative prover.

## Verification and reproducibility

The [compact result](language/mixed-cost-v5-transfer-result.json) records all
44 fresh process pairs, exact assignment and statement hashes, proof hashes,
monotonic endpoints, stage and native PoW reports, complete manifests, and
build walls. Its SHA-256 is
`e43e740b9328eab016992c3817e1a1a16afe59e2135dc9c7d33c0695a28dd3fb`.
All **44 proofs** verified against their typed public statements, and all
**44 ABI-valid changed public claims** were rejected specifically at
`InvalidMixedInteractionNonce`. The separate
[artifact audit](language/mixed-cost-v5-transfer-audit.json) checked exact
local source, statement, binary and proof hashes, recomputed the frozen score,
and independently replayed all 44 honest proofs and 44 changed-claim
rejections. Its score artifact is
[here](language/mixed-cost-v5-transfer-score.json).

Raw proofs, stderr, manifests and package binaries remain in the local
`zig-out/s31-mixed-cost-v5-transfer/` bundle. A reviewer without that bundle
can inspect the committed hashes and score but cannot replay these exact
stochastic proofs. The runner deliberately refuses another run in the same
output location. A future calibrated model should be a new preregistered
version with a fresh cohort rather than a changed score for this one.
