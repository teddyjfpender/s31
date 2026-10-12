# Stage-resolved whole-prover cost diagnostic

This version separates measured process wall into seven disjoint terms:
native witness generation, native setup, native proving excluding reported
PoW, reported native PoW, remaining timed native runtime, prover process
residual, and external verifier process wall. The process residual is the
measured prover process wall minus the native package timer; it includes
startup, parsing, file I/O, scheduling, and other unclassified work. It is
**not** labelled native setup. Summing the seven terms reconstructs the
actual first-verified process wall for each saved trial.

The [historical stage ledger](historical-stage-ledger.json) was extracted
before new native work from two previously sealed local studies. It has nine
12-trial sources at 96, 256, and 448 gates. The original alternating and
all-add source families (six sources, 72 trials) fit stage centers. The
all-multiply family (three complete sources, 36 trials) calibrates whole-wall,
after-reported-PoW wall, proof-byte, and RSS **ratio intervals**. No trial
from the new lagged-alternating family is used in either step. The
[calibration](calibration.json) records exact historical ledger and model
source hashes. Earlier V8r1 and mixed-stage models are untouched.

The old records show a real first-use effect: the first proof process of a
fresh package has roughly 390–435 ms of process residual in the fit sources,
whereas later processes have roughly 15–19 ms. The model predicts first-use
and later runs separately. It takes each stage center as the median of the
two fit-program medians at that gate count, except process residual, which
has a distinct first-use value and later-trial median. Summed stage centers
form the whole-wall point estimate. It calibrates *whole-target* intervals
directly from all-multiply ratios, preserving dependence among stages:

- Later trials: pooled 2.5th and 97.5th percentiles across 33 ratios per
  target, widened to include the point center.
- First-use trials: only three source-level observations exist. The interval
  is deliberately broad, from half the smallest ratio to twice the largest,
  widened to include the center. This is an uncertainty disclosure, not a
  statistically calibrated tail guarantee.

The next prospective source family is a lagged alternating recurrence:
`p1 = x .* x`, `p2 = x + p1`, then each gate combines the previous two
wires with alternating add and multiply. It is a different dependency graph
from the original `x`-plus-previous chain. The new 96/256/448-gate programs
each have 12 deterministic, distinct assignments; sample 0 is deliberately
the first proof process for its newly built package. The plan pins exact
source and assignment hashes, old ledger/calibration hashes, compiler,
engine, host, oracle provenance, and runner/model/scorer sources before any
new build. The score is never refitted.

Run from the repository root:

```sh
# Historical extraction and fit were completed before the new plan.
python3 -B src/frontends/s31/benchmarks/stage_resolved_v1/test_static.py -q
python3 src/frontends/s31/benchmarks/stage_resolved_v1/study.py plan \
  --out zig-out/s31-stage-resolved-v1
# Preserve and inspect plan.json before native work; use a quiet machine.
python3 src/frontends/s31/benchmarks/stage_resolved_v1/study.py heldout \
  --out zig-out/s31-stage-resolved-v1
python3 src/frontends/s31/benchmarks/stage_resolved_v1/study.py audit \
  --out zig-out/s31-stage-resolved-v1
python3 src/frontends/s31/benchmarks/stage_resolved_v1/independent_score.py \
  --out zig-out/s31-stage-resolved-v1
# Added after the native phase: independently replay the frozen historical fit.
python3 -B src/frontends/s31/benchmarks/stage_resolved_v1/posthoc_calibration_audit.py
python3 -B src/frontends/s31/benchmarks/stage_resolved_v1/publish.py \
  --out zig-out/s31-stage-resolved-v1 \
  --publish src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11
```

Every new trial requires native verification, changed-claim rejection, and
an independent value-oracle check. The audit repeats original/changed native
verification for all saved proofs. This is a one-host, one-compiler,
direct-gate experiment. The intervals are empirical historical bands, not
confidence intervals or scheduling promises. Package builds, Python work,
and audit replays are excluded from the paired process target and reported
separately. All new sources exceed the 1–16-gate bounded release
correspondence certificate. Automatic lowering remains disabled.

Protocol and result interpretation: [stage-resolved cost v1](../../../../../design/s31/measurements/STAGE_RESOLVED_COST_V1.md).
The completed result is in [the local result report](../../../../../design/s31/measurements/STAGE_RESOLVED_COST_V1_RESULT.md).
