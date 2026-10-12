# Mixed whole-prover cost v4: prospective heldout result

**Result: all six preregistered gates pass on one pinned Apple M5 Max host.**
This is evidence for the v4 distribution model on four genuinely unseen S31
source families/shapes and 316 scored heldout claims. It is not a general
runtime guarantee or a speedup claim against Cairo. The exact
[pre-native protocol](language/mixed-cost-v4-protocol.json) was committed as
`0807b26` before the first v4 package build; its SHA-256 is
`c1fc0ed5a3372af20251b54686971fedf7847edbd1a266e28dd1b9d1bc037569`.
The training corpus, model, and anchor were committed as `90ae1fe` before
the first heldout build. The heldout
[evaluation](language/mixed-cost-v4-evaluation.json) SHA-256 is
`da9d21e4d65a7f1030db9d9d4571942f4a927c4de543ee02c82432ab2400c9cf`.

## Preregistered gates

The model used 160 fit trials and 156 distinct calibration trials from four
training programs. Heldout programs contributed 79 scored fresh process
pairs each. The two claim-0 processes per source were descriptive cold and
same-claim-repeat observations, never fit or scored.

| Heldout metric | Frozen limit | Observed | Result |
| --- | ---: | ---: | --- |
| p90 of four program-median warm-wall relative errors | ≤30% | 18.56% | Pass |
| Predicted wall [p05, p95] coverage, all 316 trials | ≥85% | 90.51% | Pass |
| Worst source wall interval coverage | ≥75% | 87.34% | Pass |
| p90 of four program-median proof-size relative errors | ≤10% | 0.525% | Pass |
| Predicted proof-size interval coverage, all 316 trials | ≥85% | 90.19% | Pass |
| Worst source proof interval coverage | ≥75% | 88.61% | Pass |

The wall predictor combines a count-dependent non-PoW baseline, separate
exponential clocks fitted to **training** interaction and FRI PoW intervals,
and 156 held-aside training residuals. Its inputs for each heldout source
were its call count and the frozen model. No realized heldout PoW time entered
the prediction. The proof interval half-width was fixed at **3.397%** by the
142nd of 156 calibration residuals before heldout. The exact formulas and
assumptions are in the [prospective design](MIXED_COST_V4_PROTOCOL_PROPOSAL.md).

| Heldout source | Observed warm median | Predicted wall p50 | Median error | Wall interval covered | Observed proof median | Predicted proof center | Proof covered |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `braid_n5` | 101.50 ms | 86.57 ms | 14.71% | 71/79 | 128,335 B | 128,192 B | 73/79 |
| `braid_n7` | 80.17 ms | 87.75 ms | 9.46% | 75/79 | 158,266 B | 157,284 B | 70/79 |
| `spoke_n5` | 90.36 ms | 86.57 ms | 4.19% | 69/79 | 128,580 B | 128,192 B | 71/79 |
| `spoke_n7` | 109.98 ms | 87.75 ms | 20.21% | 71/79 | 157,219 B | 157,284 B | 71/79 |

The last source misses the wall median by about 22.2 ms despite passing
the fixed 30% program-error limit. Its observed FRI PoW median was 73.15 ms,
versus 52.14 ms for `braid_n7` with the same deterministic 7-call geometry.
Those realized PoW values are **post-proof attribution only**. They are not
predictor features and do not prove that PoW alone caused the median gap.

## Native evidence and stage accounting

The run produced 648 native proofs: 324 training and 324 heldout. Each proof
was accepted against its typed public statement, and an ABI-valid one-word
changed public result was rejected specifically at
`InvalidMixedInteractionNonce`. A separate raw replay accepted and rejected
all 648 proofs again. The tracked [training corpus](language/mixed-cost-v4-train.json),
[heldout corpus](language/mixed-cost-v4-heldout.json),
[train audit](language/mixed-cost-v4-train-audit.json), and
[heldout audit](language/mixed-cost-v4-heldout-audit.json) preserve hashes,
per-process monotonic endpoints, package stages, native phases, a disjoint
wall partition, binary hashes, source/claim hashes, build wall, and complete
component manifests. Training corpus SHA-256 is
`6343ffd14870b7ce43a7e3f88751fa91ba4af7952c340ca13bcb4c540d438410`;
heldout corpus SHA-256 is
`cf5fc3ffbb6e8afec9df5c49842438985b090740743410d9cf4f32d9be00cf78`.

The heldout native manifests have the expected fixed PoW difficulties:
20 interaction bits and 26 FRI bits. Their deterministic geometry changes
with call count and agrees across the different DAG families at the same
count:

| Calls | Component slots | Constraints | Commitment tree columns | Max/composition log size |
| ---: | ---: | ---: | --- | ---: |
| 3 (train) | 7 | 68 | `[8, 63, 92, 8]` | 9 / 9 |
| 5 (heldout) | 11 | 106 | `[8, 97, 148, 8]` | 9 / 9 |
| 7 (train and heldout) | 15 | 144 | `[8, 131, 204, 8]` | 9 / 9 |

The median measured components below are **diagnostic descriptions of scored
heldout trials**, not inputs to the predictions. Medians of separate
components need not add to the median whole-process wall.

| Heldout source | Warm wall median | FRI PoW median | Interaction PoW median | Non-PoW wall median | First post-build process | Package build wall |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `braid_n5` | 101.50 ms | 66.62 ms | 1.35 ms | 31.99 ms | 844 ms | 53.02 s |
| `braid_n7` | 80.17 ms | 52.14 ms | 1.47 ms | 33.35 ms | 1,135 ms | 54.15 s |
| `spoke_n5` | 90.36 ms | 57.04 ms | 1.44 ms | 32.64 ms | 1,069 ms | 53.99 s |
| `spoke_n7` | 109.98 ms | 73.15 ms | 1.16 ms | 34.30 ms | 1,219 ms | 54.11 s |

These observed build walls depend on Zig cache state; they are not a cold
compiler benchmark. Each first process is just one observation, and neither
build nor first-process accuracy was a gate. Raw proof files, verifier stderr,
manifests, and package binaries are retained locally under
`zig-out/s31-mixed-cost-v4/`; they are not committed to Git because of size.
The tracked corpora identify their SHA-256s, but an external reviewer needs
the raw bundle to repeat the exact native replay rather than regenerating
new stochastic proofs.

## Scope and limitations

The protocol pins macOS 26.7.1 arm64, Apple M5 Max, Zig 0.15.2 and its
executable hash, S31 compiler fingerprint
`26a76d20e8d9485f0424c32ba8b3a0b79600bf8d5bc27019a5d45a5fc9ffcfbf`,
and stwo-zig engine gitlink
`f34f6a64185e98567392a3d27492d7ccb267f6f7`. There was one prospective
timing run, not a score-selected rerun. The eight source hashes and 640
assignment/statement claim pairs were fixed before measurement and disjoint
from the earlier mixed-cost protocols. The four heldout DAGs were unseen by
the model fit and calibration, but all programs use the same direct mixed
chip family and at most seven repeated calls. Transfer to larger programs,
other chips, hosts, compiler revisions, PoW settings, or automatic lowering
has not been established. Nominal 90% coverage on this cohort is an
empirical result, not a probabilistic guarantee for arbitrary programs.

This result materially improves on the failed
[v3 heldout](MIXED_COST_V3_RESULT.md) under its own new preregistration, but
v3 and v4 used different source cohorts, claim counts, models and gates.
Their scores are not a controlled speed or model-quality comparison.
