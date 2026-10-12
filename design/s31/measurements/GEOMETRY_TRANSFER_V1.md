# S31 direct-gate geometry transfer v1

Status: **completed; see the [local result](GEOMETRY_TRANSFER_V1_RESULT.md)**.
This page retains the method prepared before native measurement. This is a genuinely
new, local same-compiler held-out check, separate from the qualified V8r1
study and the 1–16-gate fixed-512-row result. The V8r1 model was repaired
after its evaluator freeze and only covers its pinned roster and host. The
newer bounded direct-gate check passed four local diagnostics for 2/8/12
held-out gates, but all six programs had 512 padded QM31 rows. Neither result
validates a cost prediction across the 512→1024 row transition.

## Predeclared experiment

| Phase | Gate counts | Expected padded QM31 rows | Assignments each |
| --- | --- | --- | ---: |
| Train | 32, 192, 384 | 512, 512, 1024 | 12 |
| Held out | 96, 256, 448 | 512, 1024, 1024 | 12 |

Every source is a distinct four-lane M31 recurrence. It starts with
`p1 = x .* x`; even numbered gates compute `x + previous`, and odd numbered
gates compute `x .* previous`. Assignment 0 includes `p-2, p-1, 0, 1`, where
`p=2^31-1`; the other 11 are deterministic and distinct. The independent
value oracle checks all four output lanes. The native `cost-report.json` must
show the expected padded row stratum before any source's trials proceed. The
exact source and assignment hashes are computed and stored in the plan.

The target is one fresh native prover process plus one fresh native verifier
process per assignment, excluding package compilation, Python orchestration,
and changed-claim audit replay. Proof bytes and prover RSS are separate
targets. A PoW-subtracted paired wall is also scored, using the two native
timer fields; it is **accounting on the same process wall**, not an execution
mode. Native setup and the remaining STARK work are not separately timed on
this path. Package build wall is recorded but not predicted because three
training sources and an uncontrolled Zig cache do not calibrate build cost.

For each padded-row stratum, the center prediction is the median of the
training source medians. The 1024-row stratum has only one training source;
this deliberately weak estimate is a falsifiable first probe, not a fitted
general scaling law. Training trial min/max gives a descriptive range. There
are no confidence intervals or tail guarantees. All held-out program medians
are scored, including failures; no held-out observation changes coefficients,
limits, split, or source choice.

| Predeclared diagnostic | Maximum relative error on every held-out program median |
| --- | ---: |
| Paired first-verified process wall | 50% |
| Paired wall after reported PoW subtraction | 30% |
| Proof bytes | 10% |
| Prover peak RSS | 15% |

The limits are feasibility diagnostics. A pass would show only that this
coarse estimator worked for three related programs, two fixed padded sizes,
one compiler/engine revision, and one host. A failure is useful evidence of
missing features or excessive PoW variance; retain it without tuning the
model on held-out results. No automatic lowering decision is enabled.

## Freeze and audit order

1. Finish compiler and runtime changes; give the study an otherwise quiet
   native build slot. Run the native-free static test. Run `study.py plan` at
   a fresh path. Inspect and preserve `plan.json` **before** the first native
   build. It pins host, compiler fingerprint, engine gitlink, source and
   assignment SHA-256 hashes, runner SHA-256, split, estimator, and gates.
2. Run `study.py train`. It builds three new source-embedded packages and
   verifies 36 distinct proofs and changed public claims. `calibration.json`
   records the plan and train-report hashes and the training-only estimate.
   Inspect and preserve that file **before** the held-out command.
3. Run `study.py heldout` once. It first recomputes the train estimate and
   checks the sealed calibration; only then does it build held-out packages
   and verify their 36 distinct proofs. It saves every raw proof/trial and
   writes the score with the pre-held-out calibration hash.
4. Run `study.py audit` to recompute the score from all 72 saved reports and
   replay original and changed-claim native verification on all 72 proofs.
   Run `independent_score.py` for a second-source recomputation of the
   training centers, held-out errors, and diagnostic gates from the saved
   trial reports; its code SHA-256 was included in the premeasurement plan.
   Publish both pass/fail diagnostics, raw and padded AIR sizes, process-wall
   dispersion, proof bytes, RSS, build time, source/compiler hashes, and
   limitations. Preserve the raw local evidence path.

Local plan and calibration files establish ordering within this runner, but
without an independent timestamped commit before each phase this is a
**controlled local holdout**, not an externally frozen prospective benchmark.
The cost study also does not establish compiler correspondence for >16-gate
sources: the current bounded direct-gate release certificate covers only
1–16 gates. Engine STARK/PCS soundness remains a separate assumption.

Runbook and implementation: [geometry transfer benchmark](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/README.md).
