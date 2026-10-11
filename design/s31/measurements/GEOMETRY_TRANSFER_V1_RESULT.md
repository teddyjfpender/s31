# S31 direct-gate geometry transfer v1: local result

The predeclared **local diagnostic gates passed** for three held-out
add/multiply recurrences spanning 512 and 1024 padded QM31 rows. This is a
useful new geometry observation, but the 448-gate first-verified wall median
was **40.71% above its frozen prediction**. The check does not establish a
reliable general whole-prover predictor or a soundness result. The
[prospective protocol](GEOMETRY_TRANSFER_V1.md) and
[runner](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/README.md)
specify the split and limits.

## Freeze and native evidence

The runner wrote the [plan](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/plan.json)
before the first native build. Its SHA-256 is
`363e07741fb98be940c4ba30e805fc4846ebd3fccff48bce9417e9ace629f351`.
The compiler fingerprint was
`893ce1f78d19783eaafac3094dbbe847bdbb61de9a4b2055d3c8ff50b2e4dd1b`,
engine gitlink `7d544c6839497ca19b6c7ef9b982e464f10cfeed`, and host an
Apple M5 Max on macOS 26.7.1 with Zig 0.15.2. The prior verified core
batch was pushed at S31 `29a9ebc` before this study. Runner and independent
scorer source hashes were pinned in the plan.

Training built 32/192/384-gate packages and produced 36 accepted native
proofs. The [calibration](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/calibration.json)
was written before any held-out package build; its SHA-256 is
`825f3d351a6a437a199db234a1ba86b0c2c36a8d34350991cc6238a8fdee8045`.
It fixed one median estimate per 512/1024-row stratum. Held-out programs
96/256/448 then produced another 36 accepted proofs. Every trial rejected a
changed public claim and passed the independent value oracle. The separate
[native audit](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/audit.json)
replayed all 72 original proofs and 72 changed-claim controls successfully.
The independently written scorer recomputed all training centers, held-out
errors, and four gate outcomes from the 72 raw trial reports without using
the runner's scoring function. The exact
[held-out score](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/heldout-score.json)
has SHA-256
`011c2dc636ff90fb796ec56a6ab3ed250eaf0855c93aa0dd9c3e488380011aeb`.

| Gates | Phase | Raw / padded QM31 rows | First verified wall median | After reported PoW median | Proof median | Prover RSS median | Package build |
| ---: | --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 32 | Train | 352 / 512 | 159.42 ms | 37.56 ms | 54,616.5 B | 9.45 MB | 54.56 s |
| 192 | Train | 512 / 512 | 91.69 ms | 39.49 ms | 54,730.5 B | 10.13 MB | 54.63 s |
| 384 | Train | 704 / 1024 | 93.74 ms | 42.87 ms | 72,903.5 B | 10.85 MB | 52.93 s |
| 96 | Held out | 416 / 512 | 106.62 ms | 38.93 ms | 54,918.5 B | 9.66 MB | 53.06 s |
| 256 | Held out | 576 / 1024 | 117.56 ms | 41.76 ms | 72,146.0 B | 10.76 MB | 53.50 s |
| 448 | Held out | 768 / 1024 | 158.11 ms | 42.66 ms | 73,143.0 B | 10.97 MB | 53.34 s |

MB uses decimal units here; the saved reports retain exact RSS bytes and all
12 observations per program. Builds used an uncontrolled local Zig cache and
are observed separately from the proof-process target. The 1024-row proofs
were roughly 17–18 kB larger than 512-row proofs in this corpus. This is a
fixed-geometry observation, not a universal proof-size law.

## Frozen predictions and held-out errors

| Held-out gates | Padded rows | Wall predicted / observed | Wall error | After-PoW error | Proof-byte error | RSS error |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 96 | 512 | 125.56 / 106.62 ms | 17.76% | 1.04% | 0.45% | 1.36% |
| 256 | 1024 | 93.74 / 117.56 ms | 20.26% | 2.68% | 1.05% | 0.76% |
| 448 | 1024 | 93.74 / 158.11 ms | 40.71% | 0.49% | 0.33% | 1.12% |

All four predeclared maximum per-program median-error limits passed:
50% wall, 30% wall after reported PoW subtraction, 10% proof bytes, and
15% prover RSS. The limits were broad feasibility checks. The 448-gate
wall p90 was 302.21 ms despite a 158.11 ms median. Median PoW timer totals
were 68.30, 85.98, and 84.05 ms across held-out programs; the corresponding
after-PoW wall medians stayed between 38.93 and 42.66 ms. These data show
that PoW variation makes this one-shot wall prediction imprecise even when
the residual process cost tracks row geometry. Subtracting PoW is only timer
accounting and cannot be promised as an actual faster proof mode.

The [compact trial ledger](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/compact-trials.json)
has SHA-256
`62e38888b7cdb214ee770c7fe2ba90c18c9bb4b1d56c40fa6de24aee232aa1cc`.
It carries all 72 measured values, source geometry, trial/proof hashes, and
controls. The full packages, original proofs, statements, and raw reports
remain in the ignored local directory `zig-out/s31-geometry-transfer-v1`
(about 53 MB), so Git alone cannot replay the native audit. `publish.py`
created the compact ledger and copied the **byte-identical** plan,
calibration, reports, score, and audit after measurement; publication code
is post hoc and did not affect the sealed runner or scorer.

A reviewer noticed after the plan was sealed that it did not explicitly pin
`python/oracle.py`. The 72 trial reports contain their independent-oracle
provenance, and a **post hoc consistency check** found all 72 records equal,
including `oracle.py` SHA-256
`e66dde1d05d16db3e5acf026d53ddf94c1c4fdf93be4cbf24ef7ded6b08d0176`.
This is a provenance check, not a retroactive prospective pin. The study
was locally sealed in one worktree and was not independently committed and
timestamped before each phase; it is a controlled local holdout, not an
externally frozen benchmark.

The next cost-model gate is a genuinely different relation family or host,
with package build-time calibration and a stronger PoW-aware wall interval.
Automatic lowering remains disabled. The >16-gate sources in this study are
outside the bounded direct-gate release correspondence certificate; native
verification and value-oracle controls do not close that formal gap.
