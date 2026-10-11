# Independent review: direct-gate geometry transfer v1

Reviewed 2026-10-11 from the saved local evidence at
`zig-out/s31-geometry-transfer-v1/`. This review is separate from the
experimenter's [protocol and result](GEOMETRY_TRANSFER_V1.md).

## Evidence and checks

The plan SHA-256 is
`363e07741fb98be940c4ba30e805fc4846ebd3fccff48bce9417e9ace629f351`;
the pre-heldout calibration SHA-256 is
`825f3d351a6a437a199db234a1ba86b0c2c36a8d34350991cc6238a8fdee8045`.
Both match the saved files, and the plan-pinned runner and independent scorer
hashes still match their source files. The plan pins compiler fingerprint
`893ce1f78d19783eaafac3094dbbe847bdbb61de9a4b2055d3c8ff50b2e4dd1b`
and stwo-zig commit `7d544c6839497ca19b6c7ef9b982e464f10cfeed`.

I checked all 72 trial reports against the six planned source hashes, all 72
planned assignment hashes, each phase report's trial-report hashes, and the
saved proof SHA-256 values. All 72 proofs have distinct hashes. Each saved
statement exactly matches its assignment's public inputs and claimed outputs,
and the independent oracle's computed outputs equal those claims. All 72
reports carry the same oracle source provenance; `python/oracle.py` is pinned
there to SHA-256
`e66dde1d05d16db3e5acf026d53ddf94c1c4fdf93be4cbf24ef7ded6b08d0176`,
which still matches the checkout. The runner's native replay audit reports 72
accepted original proofs and 72 rejected changed public claims. I did not
rerun those native verifications separately. The independently implemented
`independent_score.py` recomputed all training centers, heldout errors, and
diagnostic gates from the saved raw reports and passed.

## All six program medians

Each program has 12 distinct assignments. Wall includes one fresh prover and
one fresh verifier process; after-PoW wall subtracts the two native reported
PoW timers from the same measured process wall. Build time is excluded.

| Phase | Gates | Raw / padded QM31 rows | Paired wall (ms) | After-PoW wall (ms) | Proof bytes | Prover peak RSS (bytes) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Train | 32 | 352 / 512 | 159.419 | 37.560 | 54,616.5 | 9,453,568 |
| Train | 192 | 512 / 512 | 91.692 | 39.491 | 54,730.5 | 10,125,312 |
| Train | 384 | 704 / 1024 | 93.739 | 42.873 | 72,903.5 | 10,846,208 |
| Held out | 96 | 416 / 512 | 106.618 | 38.929 | 54,918.5 | 9,658,368 |
| Held out | 256 | 576 / 1024 | 117.558 | 41.756 | 72,146 | 10,764,288 |
| Held out | 448 | 768 / 1024 | 158.111 | 42.664 | 73,143 | 10,969,088 |

The predeclared estimator takes the median of training program medians within
each padded-row stratum. Its four acceptance gates require **every** heldout
program's relative median error to stay within the stated limit:

| Metric | Limit | 96 gates | 256 gates | 448 gates | Gate |
| --- | ---: | ---: | ---: | ---: | --- |
| Paired wall | 50% | 17.762% | 20.261% | 40.713% | Pass |
| After-PoW wall | 30% | 1.037% | 2.676% | 0.491% | Pass |
| Proof bytes | 10% | 0.446% | 1.050% | 0.327% | Pass |
| Prover peak RSS | 15% | 1.357% | 0.761% | 1.120% | Pass |

All four diagnostic gates pass. The largest raw process-wall error is 40.713%
at 448 gates; it is appreciably closer to its 50% limit than the other three
metrics are to theirs. The score is a median-error diagnostic, with no
confidence interval or tail guarantee.

## Interpretation and remaining limits

The six programs are prefixes or extensions of one alternating four-lane
M31 recurrence. This is within-family transfer across two measured padded
sizes, not evidence for other operation mixes, chip families, machines, or a
general whole-prover model. The 1024-row stratum has one training program.
The study needs training at both row sizes; it does not extrapolate from 512
rows to an unmeasured 1024-row regime. Programs above 16 gates remain outside
the bounded direct-gate release correspondence certificate, even though their
individual native proofs and value claims passed the experiment's controls.

The plan and calibration were sealed in the local runner before their next
phases, but were not committed or independently timestamped at those points.
Thus the result is a controlled local holdout rather than an externally frozen
prospective benchmark. The plan did not pin the oracle source hash directly;
the identical provenance hashes in all 72 reports close that reproducibility
question for this run. This cost result does not establish STARK/PCS soundness
or change the bounded release gate.
