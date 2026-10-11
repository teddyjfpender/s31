# Paired public-record v2 cost study: result

Status: **completed, anchored, native-audited, and report-replayed** on one
Apple M5 Max host (macOS 26.7.1, Zig 0.15.2). This is a measured result for
the pinned source family and shipped workflows. It does not authorize automatic
lowering selection or establish equal proof-system soundness.

## What was compared

Each pair used identical normalized S31 source bytes, a canonical typed public
record statement, and the same assignment. The relation contains N independent
16-round `square; add constant` calls, with N=1–8. The generic `direct-gate`
arm and authenticated `direct-mixed-general` arm each ran a fresh prover process
and a separate source-embedded native verifier. The generic arm used the v2
`prove-for-external-verification` command so its ordinary internal verification
was not charged a second time. Both arms had the same visible FRI settings:
70 queries, fold step 1, log blowup 1, last-layer bound 0, FRI PoW 26 bits,
and interaction PoW 20 bits. Generic PCS lifting rose from log 10 to 11 for
N=7–8; mixed remained at log 10. Matching these visible parameters does not
establish equal soundness for the different AIR/component geometries.

The protocol fixed 100 assignments per call count, disjoint train counts
1/2/4/6 and held-out counts 3/5/7/8, order balancing, and a 10,000-resample
assignment-paired percentile bootstrap before measurement. The held-out phase
contains 400 assignment pairs and 800 native arm proofs; the train phase has
the same number. `first_verified_wall_seconds` sums the separately measured
prover and verifier process durations; it excludes package build, Python
orchestration, and their interprocess gap.

## Held-out measurements

Ratios are **generic divided by mixed**, so a wall ratio above 1 favors mixed.
The ratio is the median of the 100 paired log ratios, exponentiated; it need
not equal the ratio of the separate arm medians. KiB uses 1024 bytes.

| Calls | First verified wall median, generic / mixed (ms) | Paired wall ratio (95% interval) | Proof median, generic / mixed (KiB) | Paired proof-size ratio | Prover peak RSS ratio |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 3 | 82.7 / 103.2 | 0.680 [0.578, 0.894] | 54.0 / 97.1 | 0.556 | 1.047 |
| 5 | 109.1 / 115.4 | 0.952 [0.807, 1.200] | 54.0 / 125.2 | 0.432 | 1.021 |
| 7 | 106.0 / 125.7 | 0.797 [0.679, 1.024] | 70.6 / 153.5 | 0.460 | 1.144 |
| 8 | 121.4 / 111.8 | 0.998 [0.731, 1.187] | 70.5 / 169.1 | 0.417 | 1.105 |

This study finds **no whole-workflow speedup for mixed** on this family. N=3
favors generic within its descriptive interval; the other wall intervals
include 1. Mixed proofs are 1.8–2.4 times the generic size at the held-out
counts. Mixed prover peak RSS is lower by roughly 2–13% according to the
paired ratios. Those intervals are per count and metric; there is no
multiple-comparison correction. The N=8 arm medians and paired ratio show why
the paired statistic must not be replaced with a ratio of medians.

Observed warm-cache package builds took 51.5–52.3 seconds for generic and
53.5–54.3 seconds for mixed across held-out counts. These are separate,
different package workflows: generic runs the full `s31.build` package and
mixed runs a source-embedded Zig install. They are not a symmetric compiler
benchmark. The mixed shipped prover evaluates the relation twice, and its CLI
does not expose comparable native stage timers; the study measures shipped
workflows rather than isolating chip arithmetic.

## Integrity and scope

The frozen protocol SHA-256 is
`c1177e83d3e0fb7f37fc232601cc3d20ea6ebe06eda229bee34950968d4cd302`
and its committed anchor is `6091a0773a02e9445946402df0435ab38e1f06a9`.
The train and held-out phase roots, audits, and analyses were committed and
independently timestamped in that order before their dependent phases. The
held-out phase-root SHA-256 is
`d912c008722a7d2ec574a77461e6a462504f86653ba56b3c66d7a94741147b7f`;
its report audit and analysis SHA-256 values are
`fc92a5209bfac4463da57b7629da702176d33b7f1da81d33d212235abfa7487e`
and `a6cb6ae342c20d4244625ee806993714859d758c6b26b51dbb0d69ee1e3886b4`.
The report anchor is `9187c6eff24004b3c6869f34ad26f105ead29d36`.
Both split `report-check` runs reproduced the anchored report bytes from the
raw ledgers and proofs. A separate, short calculation directly from the
held-out `corpus.json` recomputed all 20 median log-ratio cells and matched
`analysis.json` to less than 1e-12.

Native audits replayed every saved proof and checked changed public claims,
altered assignments and proofs, source-embedded alternate verifiers, and a
changed proof-header manifest digest. The immutable raw evidence is in
`zig-out/s31-paired-record-v2/{train,heldout}` in the measurement worktree;
the JSON protocol and four anchors are committed under
`design/s31/measurements/language/`. Timings still trust the pinned Python
collector, host monotonic clock, `/usr/bin/time` RSS report, and this host's
cache state. This is one host and one relation family, not a cross-host speed
claim or a proof of compiler or circuit soundness. Automatic lowering remains
disabled.
