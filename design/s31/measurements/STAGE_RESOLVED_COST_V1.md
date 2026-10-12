# S31 stage-resolved whole-prover cost v1

Status: **historical model frozen; new-family native phase complete**. See the
[measured result](STAGE_RESOLVED_COST_V1_RESULT.md) and the exact
[sealed plan](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/plan.json).
Prior [geometry transfer](GEOMETRY_TRANSFER_V1_RESULT.md) and
[operation-mix transfer](OPERATION_MIX_TRANSFER_V1_RESULT.md) passed broad
local diagnostic gates, but raw first-verified wall had errors up to 49.05%.
The completed native diagnostics expose two material causes. Reported PoW
timer totals vary widely among otherwise similar programs. Separately, the
first proof process for each newly built package has approximately 400 ms
more unclassified process residual than later processes. A single 12-trial
program median hides this first-use cost. This model represents both effects
without calling the process residual native setup or promising that PoW can
be removed.

## Measured stage equation

For each native trial, the score reconstructs the paired prover-plus-verifier
process wall as:

```text
whole wall = witness + setup + native prove excluding reported PoW
           + reported interaction/FRI PoW + remaining native runtime
           + (prover process wall - native package timer)
           + external verifier process wall
```

The native package timer's four non-PoW/PoW terms and the prover process
residual are checked against raw monotonic process measurements. The residual
includes startup, parsing, I/O, scheduling, and anything the native package
timer does not cover. Engine setup/PCS/FRI work inside the native prove call
is still only as fine-grained as the available native timer. This is an
accounting model, not an independent proof-system profiler.

The [historical stage ledger](../../../src/frontends/s31/benchmarks/stage_resolved_v1/historical-stage-ledger.json)
contains 108 raw-trial-derived stage records from nine whole programs. The
extractor checked each saved source, assignment, trial report and proof hash
against prior study plans/reports, required native proof acceptance,
changed-claim rejection and value-oracle passage, and checked the seven
stage terms sum to measured paired wall. Extraction occurred before the new
prospective native phase. Six complete sources (original alternating and
all-add, 72 trials) fit point centers. Three complete all-multiply sources
(36 trials) calibrate intervals and are excluded from the fit. The
[sealed calibration](../../../src/frontends/s31/benchmarks/stage_resolved_v1/calibration.json)
records both the ledger hash and exact model-source hash.

| Gates | Fit first-use process residual | Fit later process residual | Fit later non-PoW wall center | Fit later whole-wall center |
| ---: | ---: | ---: | ---: | ---: |
| 96 | 420.43 ms | 16.22 ms | 38.78 ms | 101.78 ms |
| 256 | 427.14 ms | 17.69 ms | 42.52 ms | 102.84 ms |
| 448 | 404.50 ms | 17.56 ms | 42.79 ms | 133.08 ms |

The row sizes are 512 padded QM31 rows at 96 gates and 1024 at 256/448.
The whole-wall center is a sum of stage centers; it need not equal a median
of whole-wall observations. The 96/256/448 first-use whole-wall centers are
506.00/512.29/520.02 ms. Proof bytes and RSS use the median of the two fit
source medians at each gate count.

## Uncertainty and prospective gates

For each complete all-multiply calibration source, divide each measured
whole-target value by its frozen fit-only center at the same count and
first-use/later phase. Later-trial intervals use pooled 2.5th/97.5th
percentile ratios from 33 trials. The first-use envelope comes from just
three first processes and deliberately spans half the smallest through
twice the largest observed ratio. These are **empirical intervals** on one
host, not confidence intervals or finite-sample tail guarantees; the
first-use sample is especially small. Intervals are calibrated on complete
targets, not by summing separately fitted stage intervals.

| Target | Later lower / upper ratio | First-use lower / upper ratio |
| --- | ---: | ---: |
| First-verified wall | 0.349 / 3.201 | 0.509 / 2.494 |
| Wall after reported PoW | 0.774 / 1.083 | 0.522 / 2.266 |
| Proof bytes | 0.957 / 1.065 | 0.491 / 2.000 |
| Prover peak RSS | 0.978 / 1.027 | 0.493 / 1.989 |

Those ratios already show a limitation: later first-verified wall's upper
bound is **3.201× its center**. That width may cover variable PoW but is too
broad for precise one-shot scheduling. The later after-PoW upper ratio is
1.083×, but PoW subtraction is only an accounting view of the same proof.

The new, unseen source topology is `p1=x*x`, `p2=x+p1`, then alternating
`p[i-2]+p[i-1]` and `p[i-2]*p[i-1]`. Each 96/256/448-gate source uses 12
new assignments. Sample 0 is the first native proof process after the
package build. Exact source/assignment hashes and expected row sizes must be
sealed in `plan.json` before native work; all 36 native proofs must verify,
reject changed public claims, and pass the independent value oracle. The
frozen model is not refitted on the new family.

| Prospective diagnostic | Required |
| --- | ---: |
| Later first-verified wall trial interval coverage (33 trials) | ≥75% |
| Later after-PoW, proof-byte, and RSS trial coverage | ≥80% each |
| First-use wall interval coverage (three trials) | ≥2/3 |
| Later wall interval upper / center | ≤8× |
| Later after-PoW interval upper / center | ≤1.5× |
| Maximum later program-median error: after-PoW | ≤15% |
| Maximum later program-median error: proof bytes / RSS | ≤10% each |

Coverage and width are reported whether the gates pass or fail, per program
and pooled. The gates are local diagnostics, not admission to automatic
lowering or a general reliability certificate. Any new trial that exceeds
the empirical interval is retained. A broad interval passing coverage must
not be paraphrased as accurate point prediction.

## Freeze order and limits

1. Run the native-free tests and inspect the historical ledger/calibration.
   Finish compiler/runtime edits. On the same compiler, engine and host,
   `study.py plan` must create a fresh path and bind exact hashes of the
   historical ledger, calibration, runner/model/extractor/independent scorer,
   oracle provenance, host, compiler, engine, new source/assignment roster,
   prediction rule, and gates. Preserve its full SHA before any new build.
2. With an otherwise quiet machine, run `study.py heldout` once. It checks
   every frozen identity **before** building the first package. It builds
   three new ReleaseFast packages, enforces actual native padded row sizes,
   runs 36 fresh proof/verifier processes, and writes raw trial evidence and
   score without fitting.
3. Run `study.py audit` to recompute the frozen score and replay all saved
   original and changed-claim proofs. Run the separate second-source scorer
   to check stage decomposition, point errors, interval coverage and gates.
   Preserve any failure and the raw evidence. The separate historical
   calibration replay was added **after** the held-out measurement, so it is
   an additional audit and must not be described as prospectively pinned.

The plan is locally sealed; without an external timestamped pre-phase commit,
the result is a controlled local prospective check. It tests one host,
compiler, engine, `direct-gate` lowering, and a new dependency graph at
three sizes. It does not validate cross-host/chip/hash/recursion costs, nor
package build-time prediction. All three sources exceed the bounded 1–16
direct-gate release correspondence certificate. Native verifier acceptance
and value-oracle checks do not supply that missing formal correspondence.
STARK/PCS soundness remains a separate assumption.

Implementation and runbook: [stage-resolved benchmark](../../../src/frontends/s31/benchmarks/stage_resolved_v1/README.md).
