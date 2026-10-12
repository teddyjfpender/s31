# S31 operation-mix cost transfer v1

Status: **completed; see the [local result](OPERATION_MIX_TRANSFER_V1_RESULT.md)**.
This page retains the method prepared before native work. The previous
[geometry-transfer result](GEOMETRY_TRANSFER_V1_RESULT.md) measured alternating
add/multiply recurrences at 512 and 1024 padded QM31 rows. Its 448-gate
first-verified wall center missed by 40.71%, although proof bytes, RSS, and
reported-PoW-subtracted wall were close in that local corpus. This new study
tests an independent source dimension without changing its frozen training
model: all-add and all-multiply recurrences. It cannot validate cross-host,
cross-lowering, chip, hash, private-boundary, or recursive costs.

## Predeclared cases and estimator

| Operation family | Held-out gates | Expected padded QM31 rows | Assignments per source |
| --- | --- | --- | ---: |
| Add only | 96, 256, 448 | 512, 1024, 1024 | 12 |
| Multiply only | 96, 256, 448 | 512, 1024, 1024 | 12 |

Each source starts with `p1 = x + x` or `p1 = x .* x`; every later gate
computes `x + previous` or `x .* previous`. The same four-lane M31 inputs
include one boundary assignment `[p-2, p-1, 0, 1]`, with `p=2^31-1`, and
11 other deterministic assignments. The source names and all input/output
assignment hashes are fixed in the plan. The independent value oracle checks
all four output lanes. Actual native `cost-report.json` padded row counts
must equal the declared strata before trial collection.

The predictor is exactly the prior
[`geometry_transfer_v1` sealed calibration](../../../src/frontends/s31/benchmarks/geometry_transfer_v1/results-2026-10-11/calibration.json):
for each metric, choose the 512-row or 1024-row frozen center and apply it
to every new program in that row class. There are no new coefficients,
train cases, interval adjustments, or held-out refits. The prior calibration
was itself only a three-program local estimate, with one 1024-row training
source. Same-host matching is necessary to interpret transfer, not evidence
that the model has generalized.

The target is a fresh prover process plus a fresh native verifier process on
the same public statement. It includes setup and PoW but excludes package
compilation, Python orchestration, and changed-claim audit replays. Package
build wall is observed separately. The PoW-subtracted target uses the two
reported native timers on that same run. It is diagnostic accounting, not a
faster proof mode or a measured setup/FRI decomposition.

| Metric | Fixed maximum relative error on **every** held-out program median |
| --- | ---: |
| Paired prover + verifier process wall | 50% |
| Paired wall after reported PoW subtraction | 30% |
| Proof bytes | 10% |
| Prover peak RSS | 15% |

Report overall and per-operation-family outcomes, including failures.
These are feasibility diagnostics, not automatic lowering gates or tail
guarantees. Raw dispersion, actual geometry, and build times must accompany
any pass/fail conclusion. No old V8r1 corpus is fitted or retuned.

## Required chronology

1. Finish compiler and runtime changes. Run the native-free source/score
   checks. `study.py plan` must run at a fresh path before any of this study's
   native packages are built. It binds the exact prior plan and calibration
   hashes, current compiler/engine/host and both study/scorer source hashes,
   independent oracle-source provenance, full new source/assignment roster,
   prediction rule, and gates. It refuses
   a different compiler/engine/host from the prior calibration. Preserve the
   plan's SHA-256 before native work.
2. With an otherwise quiet host, run `study.py heldout` once. It rechecks
   the plan and old calibration **before** the first native build. Six new
   ReleaseFast source-embedded packages produce 72 fresh proof/verifier
   trials. The runner requires independent value checks and changed-claim
   rejection, saves proof bytes and raw reports, and scores without fitting.
3. Run `study.py audit` to recompute saved scoring from the frozen calibration
   and replay native original and changed-claim verification for all 72
   proofs. Run the separately written `independent_score.py` to rederive
   all medians/errors and overall/per-operation gates from raw reports. Keep
   raw evidence and any failed gate.

The local plan is a content pin and phase-order check, not an independent
externally timestamped freeze. A study completed only with local files must
be called a controlled local prospective transfer. The 96–448-gate sources
are outside the bounded 1–16-gate direct-gate release correspondence
certificate. Native verifier acceptance and a separate value oracle do not
close that compiler formalization gap; STARK/PCS soundness remains separate.

Implementation and runbook: [operation mix benchmark](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/README.md).
