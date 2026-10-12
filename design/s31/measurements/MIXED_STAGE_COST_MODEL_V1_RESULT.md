# Mixed-general whole-prover cost model v1: frozen result

The **predeclared local accuracy gate passed** for the record ABI v2,
16-round repeat-chain family on one Apple M5 Max host. This is a model of the
source-embedded `direct-mixed-general` package's first verified process wall
and proof bytes for N=1–8 live calls. It is not a cross-host or cross-program
cost model, a speedup claim, or a soundness result. Automatic lowering remains
disabled. [The prospective protocol](MIXED_STAGE_COST_MODEL_V1.md) specifies
the split, estimator, controls, and pass conditions before these measurements.

## Freeze and evidence

The [protocol](language/mixed-stage-cost-v1-protocol.json) has SHA-256
`6eeade0dca2f1052c7865fc76849241058b2b3212daf4bcb93b9fbb57aa75d9a`
and was anchored at `6e3bbb5ea3948958494310a0ef98c9e87cbc3124` before
the first timed build. It pins the S31 source and tools, resolved Zig
executable, stwo-zig gitlink, host identity, 800 distinct assignments and
typed public claims, estimator, and gates. Training used N=1,3,5,7; the
held-out phase used N=2,4,6,8, each with 100 assignments.

| Evidence | SHA-256 | Anchor commit |
| --- | --- | --- |
| Training `phase-root.json` | `860840f3088c459a8b036633e34d0434dfd5be3ef4e895aeaf51b34e3facf9e5` | `c23794617d1b5b14910d2d3f52c9cc15270e78d4` |
| Frozen training `model.json` | `92d4bc1847f7ad69b08c3405e84f7df7e69e9492f403fd7a6286d59c75e9e9f3` | `52cdce6942579e9b10f0b953df125bd078b6ede8` |
| Held-out `phase-root.json` | `fc1bb629e7b85aff131b67f40852305ee97694275fccd2ab725cf6dbf3d104f6` | `84d067c575c092e7d927e149d316335dcea68bed` |
| Held-out `evaluation.json` | `c9ba5676450d85b8d5cbc5cf597c86a521ec4ffdab85296cb74310246e03c536` | `baf45e812051648f53b581eb5f771dff2c765068` |

The [report anchor](language/mixed-stage-cost-v1-heldout-report-anchor.json)
also seals the held-out audit and corpus hashes. `study.py report-check`
recomputed the evaluation from the frozen model and retained audited corpus,
rechecked the raw phase root, and returned
`local_accuracy_gate_pass: true`. The raw binaries, proofs, logs, and reports
are retained under `zig-out/s31-mixed-stage-cost-v1-{train,heldout}-20261011`
in the measurement worktree (about 170 MiB combined); they are not part of
the Git tree. The committed roots make changed local evidence detectable but
do not make that local corpus independently available from Git alone.
Reproduction of `report-check` against those raw directories requires the
frozen source checkout at `baf45e812051648f53b581eb5f771dff2c765068`;
later source edits intentionally fail its source-pin check.
A separate read-only audit recomputed both raw phase roots (4,437 training
files and 4,438 held-out files), all 800 trial records and their source,
assignment, statement and proof hashes, the anchor chronology, and all eight
held-out gates. It found no discrepancy in this result.

Both phases produced 400 proofs accepted by external source-embedded native
verifiers. Their anchored audits replayed every proof, rejected changed public
input and result claims for every proof, and checked source, assignment,
statement, manifest and binary hashes plus raw build and process endpoints.
Engine STARK, LogUp, Fiat–Shamir and PCS soundness remain separate assumptions.

## Held-out predictions

Wall is the median of one fresh prover process plus one fresh external
verifier process per assignment. It includes process startup and the complete
native prover/verifier, but excludes package compilation and Python
orchestration. KiB uses 1024 bytes. Build wall is an observed separate cost;
four training sources are insufficient to claim a general build-time model.

| Calls | Observed / predicted first-verified wall (ms) | Wall median error | Observed / predicted proof (KiB) | Proof median error | Observed package build (s) |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 89.51 / 98.25 | 9.76% | 83.08 / 82.46 | 0.75% | 51.89 |
| 4 | 111.38 / 98.63 | 11.44% | 111.61 / 111.21 | 0.36% | 52.55 |
| 6 | 109.14 / 99.02 | 9.28% | 140.04 / 139.97 | 0.05% | 52.73 |
| 8 | 121.26 / 99.40 | 18.02% | 168.20 / 168.72 | 0.31% | 53.09 |

| Frozen gate | Observed | Required |
| --- | ---: | ---: |
| Wall program-median p90 relative error | 16.05% | ≤25% |
| Wall program-median maximum relative error | 18.02% | ≤35% |
| Wall trial interval coverage | 90.25% | ≥80% |
| Wall median interval upper / observed median | 2.84× | ≤8× |
| Proof program-median p90 relative error | 0.63% | ≤10% |
| Proof trial interval coverage | 91.75% | ≥80% |
| Proof median interval upper / observed median | 1.03× | ≤1.5× |
| Opaque native-prove program-median p90 relative error | 20.70% | ≤30% |

The stage fit sums six disjoint package intervals, a prover process residual,
and external verifier process wall. Its native prove interval includes setup;
separate engine setup and PoW timers are unavailable. The training fit selected
a zero slope for that native interval, so the roughly 98–99 ms wall prediction
barely changes with N; the N=8 wall median error is 18.02%. The empirical
leave-one-source-out trial interval covers 90.25% of held-out wall trials but
is not a confidence interval or a tail guarantee. Cold-start outliers and
host scheduling remain in the raw process observations.

The previous [paired record study](PAIRED_RECORD_V2_RESULT.md) found no
whole-workflow mixed speedup for this family. Its samples were excluded from
this model's fitting, interval calibration, and evaluation. A reliable general
whole-prover predictor still needs new source shapes, hosts, and build-cost
validation under new prospective protocols.
