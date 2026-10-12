# Mixed cost v3 postmortem: PoW variance and proof-size band transfer

This is **post hoc analysis** of the frozen, failed v3 heldout evaluation.
It does not change the [protocol](language/mixed-cost-v3-protocol.json),
[model](language/mixed-cost-v3-model.json), [corpora](MIXED_COST_V3_RESULT.md),
or any gate. The analysis uses the clean training/heldout runs only. The
aborted first train attempt described in the [result](MIXED_COST_V3_RESULT.md)
is excluded.

## How much of the wall miss was FRI PoW?

For every process, the runner's checked wall partition gives the exact
identity `first_verified_wall = FRI_PoW + all_other_wall`. Thus subtracting
the reported FRI PoW interval is valid **per trial**. Medians of separate
terms do not generally add, so the table below computes each median from
paired trials rather than subtracting medians.

| Split | Source | Warm wall median | FRI PoW median | Median of wall minus FRI PoW |
| --- | --- | ---: | ---: | ---: |
| Train | `control_n2` | 128.54 ms | 100.25 ms | 31.75 ms |
| Train | `control_n6` | 88.83 ms | 54.50 ms | 35.10 ms |
| Train | `deep32_n2` | 73.32 ms | 40.74 ms | 32.18 ms |
| Train | `deep32_n6` | 81.59 ms | 46.13 ms | 35.46 ms |
| Heldout | `feeder_n4` | 96.30 ms | 64.77 ms | 34.08 ms |
| Heldout | `feeder_n6` | 108.27 ms | 70.32 ms | 35.13 ms |
| Heldout | `fork_n4` | 96.41 ms | 70.30 ms | 30.57 ms |
| Heldout | `fork_n6` | **201.35 ms** | **165.41 ms** | **36.09 ms** |

The four heldout medians of wall **excluding** FRI PoW span only
30.57–36.09 ms. In `fork_n6`, the FRI PoW median is 82.1% of the
first-verified wall median and 96.5% of the native proving median. The
individual `fork_n6` warm FRI PoW intervals span 28.4–241.6 ms.

As an explanatory calculation, take **50.313 ms**, the median of the four
training-program FRI PoW medians. For each heldout trial independently,
replace its observed FRI interval with 50.313 ms, then take the median of
the adjusted walls. This uses a **post-proof measured interval**, so it
cannot be deployed as a source-only predictor.

| Source | Measured warm median | Adjusted median with training FRI reference | Frozen wall prediction |
| --- | ---: | ---: | ---: |
| `feeder_n4` | 96.30 ms | 84.39 ms | 85.21 ms |
| `feeder_n6` | 108.27 ms | 85.45 ms | 85.21 ms |
| `fork_n4` | 96.41 ms | 80.88 ms | 85.21 ms |
| `fork_n6` | 201.35 ms | 86.40 ms | 85.21 ms |

For `fork_n6`, measured median minus frozen center was **116.136 ms**.
After the per-trial FRI replacement it was **1.188 ms**. The accounting
exercise removes **114.948 ms, or 99.0%**, of that particular median miss.
This supports FRI PoW duration as the dominant observed difference. It
does not prove a counterfactual runtime if PoW difficulty or hardware were
changed, and it does not rescue the failed prospective gate.

## Deterministic geometry check

The installed native manifest binaries were run read-only for all eight
programs. Their selected fields and raw manifest/binary SHA-256 digests are
saved in the [geometry extraction](language/mixed-cost-v3-geometry-postmortem.json).
The two heldout **six-call** sources share:

| Native geometry field | `feeder_n6` | `fork_n6` |
| --- | ---: | ---: |
| Chip calls / component slots | 6 / 13 | 6 / 13 |
| Tree column counts | [8, 114, 176, 8] | [8, 114, 176, 8] |
| Total constraints | 125 | 125 |
| Maximum column log size / composition log size | 9 / 9 | 9 / 9 |
| Slot trace log sizes | 9, then twelve 4s | 9, then twelve 4s |
| Interaction / FRI PoW bits | 20 / 26 | 20 / 26 |
| Source-level nodes / repeated rounds | 19 / 96 | 12 / 96 |

The four-call feeder/fork pair also has matching native dimensions and
PoW bits (9 slots, tree columns [8, 80, 120, 8], 87 constraints). The
source DAGs differ: feeder inserts arithmetic before each chip call; fork
starts chip calls from the same input and sums their results. At six calls,
those source differences did **not** change the listed native proof
geometry. Their median wall-minus-FRI-PoW differed by less than 1 ms
(35.13 versus 36.09 ms), while their FRI PoW medians differed by 95.09 ms.
The observations are consistent with variable PoW search duration; the
timers alone cannot identify every cause of that variation.

## Why the proof-size band failed

The frozen proof-size center was `54,887.25 + 14,742.375 × calls` bytes.
It predicted all four heldout **program medians** within 1.44%, and the
program-median p90 error passed at 1.13%. Its training warm-trial ratio
band was **0.97863–1.02188×** predicted size, the training 5th/95th
percentiles clamped to include one. It covered 55/60 training warm
trials, but only **39/60 heldout** warm trials, below the frozen 80% gate.

| Ratio distribution | Minimum | 5th percentile | Median | 95th percentile | Maximum |
| --- | ---: | ---: | ---: | ---: | ---: |
| Training warm proof bytes / prediction | 0.9702 | 0.9786 | 1.0000 | 1.0219 | 1.0239 |
| Heldout warm proof bytes / prediction | 0.9661 | 0.9710 | 0.9999 | 1.0274 | 1.0397 |

Both heldout tails are wider than the training band. Coverage by heldout
source was 10/15, 12/15, 8/15, and 9/15 in feeder-n4, feeder-n6,
fork-n4, and fork-n6 order. This is a **band-transfer failure** even
though the size center transferred well. Widening the v3 band now would
be an invalid retrofit. The proof-size variation's exact serialization
cause is not isolated by the current stage reports.

## Consequence

The next prospective experiment must model a latency **distribution**,
not a single expected PoW search realization; use genuinely new sources
and claims; and set its quantile/coverage gates before collecting them.
The geometry fields above are known before proof time and can be model
features. Realized FRI PoW duration is known only after proving and must
remain an evaluation diagnostic.
