# Prospective mixed whole-prover cost v2: local held-out result

**Result:** the frozen, simple model passed all four preregistered local gates
on four held-out source programs. This is a median prediction baseline for the
pinned Apple M5 Max host and `direct-mixed-general` package profile. It makes
no speedup, tail-latency, cross-host, or automatic-lowering claim.

The protocol was committed in `844b2be` before the first v2 native build
(SHA-256 `5c293565a87e2347f1362a4276364b2404e55bb3668367aed65f6e69a327228e`).
The 80-trial training corpus, exact model bytes, and model anchor were
committed together in `ae61bec5725681e702f5fa22d934373073358fea`
before the first held-out build. Model SHA-256 is
`8f0adeb33ff531167e98b758f65e3e3fa7b18a4f11d3d4d690630300a5854e31`.
The runner verified that committed model bytes and its committed training
corpus at the named ancestor before collecting held-out data. The train and
held-out source hashes and all 160 assignment and statement hashes are
disjoint; every claim was generated before observation and checked against
earlier mixed-study claim inventories.

## Predictions fixed before held-out work

The model predicts **77.749 ms** first-verified process wall for every held-out
program: the median of four training-program medians. It predicts proof bytes
as `55,883.875 + 14,745.0625 × chip_calls`. These are predictions for one
fresh prover process plus one fresh external native verifier process, not
package build. Package build wall is measured separately. Native stage and
phase timers were retained for accounting and were never predictor features.

| Held-out source | Wall predicted / observed median | Wall error | Proof predicted / observed median | Proof error | Build wall |
| --- | ---: | ---: | ---: | ---: | ---: |
| `feeder_n4` | 77.75 / 75.07 ms | 3.57% | 114,864 / 114,061 B | 0.70% | 52.66 s |
| `feeder_n6` | 77.75 / 106.62 ms | 27.08% | 144,354 / 142,914 B | 1.01% | 53.47 s |
| `fork_n4` | 77.75 / 80.70 ms | 3.65% | 114,864 / 113,688 B | 1.03% | 53.76 s |
| `fork_n6` | 77.75 / 101.73 ms | 23.57% | 144,354 / 144,400 B | 0.03% | 53.63 s |

| Frozen gate | Held-out result | Threshold | Outcome |
| --- | ---: | ---: | --- |
| Wall p90 program-median relative error | 26.03% | ≤30% | Pass |
| Proof p90 program-median relative error | 1.03% | ≤10% | Pass |
| Wall trial band coverage | 72/80 = 90.00% | ≥70% | Pass |
| Proof trial band coverage | 65/80 = 81.25% | ≥80% | Pass |

Wall program median absolute percentage error was 13.61%; proof was 0.856%.
The saved constant proof-size baseline had 20.20% p90 relative error, versus
1.03% for the preregistered call-count fit on these four programs. This is
evidence that call count predicted proof *size* better than a constant in
this small held-out corpus; it does not establish a general cost model.

The package logged six stage durations for every trial. Their separate
held-out medians, in milliseconds, show where prover process time went;
medians of individual stages need not add to the median of their sum.

| Source | Profile rebuild | Semantic eval | Topology compile | Witness compile | Native prove and setup | Envelope/serialize | Package total |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `feeder_n4` | 2.035 | 0.017 | 0.169 | 0.193 | 52.080 | 0.128 | 54.631 |
| `feeder_n6` | 2.274 | 0.021 | 0.191 | 0.214 | 70.129 | 0.164 | 72.987 |
| `fork_n4` | 2.073 | 0.015 | 0.169 | 0.182 | 53.085 | 0.128 | 55.564 |
| `fork_n6` | 2.251 | 0.017 | 0.181 | 0.197 | 67.682 | 0.166 | 70.516 |

## Native and timing checks

All 160 original proofs (80 training, 80 held out) were accepted by their
source-embedded external native verifiers. All 160 ABI-valid claims with one
changed public result were rejected specifically at
`InvalidMixedInteractionNonce`. The raw replay auditor repeated both native
outcomes for every retained proof, checked exact source, assignment,
statement, proof, package binary, and stderr bytes against the compact
corpora, and verified six package stage sums and native phase identities.
The audit results are in `language/mixed-cost-v2-train-audit.json` and
`language/mixed-cost-v2-heldout-audit.json`. The raw 72 MiB evidence directory
is `zig-out/s31-mixed-cost-v2` in the measurement workspace and is not in
Git; the compact corpora store proof and binary hashes, but native replay
from a fresh clone requires transferring the raw directory or rerunning the
study.

The training first-verified wall ranged from 29.90 to 1,458.49 ms; held out
ranged from 27.23 to 1,599.96 ms. The first trial in **each** source included
a large cold-process/startup penalty: roughly 1.04–1.60 seconds combined
prover and verifier wall. Later long trials also reflected variable FRI proof
of work. The wall empirical band was broad, **0.443× to 6.906×** the center
prediction, giving 34.4–536.9 ms around the 77.75 ms center; it missed the
cold-start extremes. The proof-size band was 0.958× to 1.024×. These bands
are descriptive training quantiles, not confidence intervals or reliable
single-trial latency bounds. Training and held-out packages were measured in
separate, quiet-host windows coordinated with the other workers, but host
contention was not instrumented beyond the process and native stage clocks.

The compact held-out corpus SHA-256 is
`bf740b0c3179ed9b5dd59543b4ca65dbed5bd6e62f988e83ac4292fe78cc0fe4`;
the evaluation SHA-256 is
`4cb37c3e36f303a9c2162beb6c115611dade2da9493328aa0df0f1be042c05d9`.
The exact reproduction commands and preregistered formulas are in the
[runner README](../../../src/frontends/s31/benchmarks/mixed_cost_v2/README.md)
and [protocol](MIXED_COST_V2_PROTOCOL.md).
