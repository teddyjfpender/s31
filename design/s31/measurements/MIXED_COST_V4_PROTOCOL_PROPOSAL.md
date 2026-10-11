# Mixed cost v4: prospective distributional protocol proposal

**Status: executable runner implemented; final native protocol and v4 timing
data are pending.** The
[native-free inventory](language/mixed-cost-v4-prospective-inventory.json)
fixes eight new source programs, 640 unique public claims, the model
implementation hash, fit/calibration split, and acceptance gates. This is
an advance design precommitment. Before **any** v4 native measurement, the
[executable runner](../../../src/frontends/s31/benchmarks/mixed_cost_v4/study.py)
must be reviewed, committed, and included in a separate
final protocol that pins the compiler, engine gitlink, Zig executable,
host, source template, model code, native manifest geometry, and all
runner bytes. Its first build must refuse an uncommitted or changed final
protocol. No v4 latency or reliability claim exists now.

The design responds to the [v3 postmortem](MIXED_COST_V3_POSTMORTEM.md):
actual FRI PoW time was a large, variable component of wall time, and a
narrow proof-size training band failed transfer. The **model structure**
reflects that diagnosis. Thresholds below are the v2/v3 program-median
limits and a nominal 90% interval objective with a 5 percentage-point
aggregate allowance; they were not fit to v3 heldout scores. V3 heldout
trials must never become v4 fitting, calibration, or acceptance data.

## New programs and exact claim split

All eight source DAGs are different from the v2/v3 sources and from one
another; all 640 assignment and typed-statement hashes are new relative
to the earlier cost protocols. The deterministic generator checks each
public output against the independent relation oracle before recording
its hash.

| Role | Programs | New DAG shape |
| --- | --- | --- |
| Train | `relay_n3`, `relay_n7` | Each repeated chip output feeds an addition with the original input before the next chip |
| Train | `twist_n3`, `twist_n7` | Alternating multiply/add constant before each repeated chip |
| Heldout | `braid_n5`, `braid_n7` | Alternate chip inputs between the evolving aggregate and the original input |
| Heldout | `spoke_n5`, `spoke_n7` | Independent chip calls from the original input, with scaled accumulation |

Every chip call has 16 rounds; counts 3, 5, and 7 are within the
eight-call `direct-mixed-general` limit. The 80 unique claims per source
use seed `202610119907`. Claim index 0 runs twice in adjacent, fresh
prover/verifier process pairs after that source's package build: first
post-build and same-claim repeat. Both index-0 processes are **diagnostic
only**. Indices 1–79 each run once:

| Split | Claim indices per source | Rows |
| --- | --- | ---: |
| Train fit | 1–40 | 4 × 40 = 160 |
| Train calibration | 41–79 | 4 × 39 = 156 |
| Heldout scoring | 1–79 | 4 × 79 = 316 |

Thus each of eight packages produces 81 proofs, **648 native proofs**
total, each with an ABI-valid changed-result negative control. Package
build wall and first-process wall are reported separately. The predicted
target is warm **first-verified process wall**: one fresh prover process
plus one fresh external native verifier process. The final runner must
retain proof bytes, emitted statement bytes, all phase reports, source
and binary hashes, monotonic process endpoints, and raw proofs for
native replay. It must reject a changed public result specifically at
`InvalidMixedInteractionNonce`.

The final protocol must require manifest PoW difficulty 20 interaction
bits and 26 FRI bits on every source, with complete native geometry
recorded before fitting. If those assumptions fail, the protocol fails
before heldout rather than silently adapting the fit.

## Frozen model arithmetic

The [model implementation](../../../src/frontends/s31/benchmarks/mixed_cost_v4/model.py)
contains the exact fit and quantile arithmetic. For each warm process
row, let:

\[
W = \text{prover process wall} + \text{external verifier process wall},
\quad
F = \text{FRI PoW interval},
\quad
I = \text{interaction PoW interval},
\quad
N = W-F-I.
\]

All three components are measured for training, but **heldout realized
\(F\) and \(I\) are never predictor inputs**. The model sees source call
count and fixed native geometry only before proving.

1. On the 160 fit rows, take each training program's median \(N\).
   Ordinary least squares against chip call count gives
   \(B(n)=\beta_0+\beta_1 n\). If the intercept is nonpositive or slope
   negative, the predeclared fallback is the median of those four
   program medians, with zero slope.
2. Fit two exponential PoW clocks from **fit rows only**:
   \(\theta_F=\operatorname{median}(F)/\ln 2\) and
   \(\theta_I=\operatorname{median}(I)/\ln 2\).
   At small success probability, a geometric hash search suggests this
   distributional approximation. It is an empirical model assumption,
   not a security statement or a proven runtime law.
3. On the separate 156 calibration rows, save the sorted non-PoW
   residuals \(E_j=N_j-B(n_j)\). The predicted wall CDF for a new source
   with call count \(n\) is the equally weighted mixture of
   \(B(n)+E_j+X_F+X_I\), with independent exponentials
   \(X_F\sim\mathrm{Exp}(\theta_F)\) and
   \(X_I\sim\mathrm{Exp}(\theta_I)\). The code evaluates the exact
   two-exponential convolution, including its equal-scale limit, and
   finds the 5th, 50th, and 95th percentiles by fixed 80-step bisection.
4. Proof-size center is ordinary least squares against call count on the
   four fit-program proof-byte medians. On the 156 calibration rows,
   sort \(d_j=|\mathrm{bytes}_j/\widehat{\mathrm{bytes}}(n_j)-1|\)
   and choose the \(\lceil 0.9(156+1)\rceil=142\)nd value. The
   predicted size interval is center × \([1-d_{(142)},1+d_{(142)}]\).

The exponential assumption and any exchangeability condition behind
the proof-size calibration may fail across source families. The
heldout gates test that transfer; neither distribution is asserted
correct merely because it was fitted.

## Fixed heldout acceptance gates

These gates are already present as constants in the design inventory.
The final runner must compute them **without refitting or widening any
band after seeing heldout data**:

| Metric on four heldout sources / 316 scored trials | Gate |
| --- | ---: |
| p90 across programs of relative error between predicted wall p50 and observed warm median | ≤30% |
| Coverage of predicted wall [p05, p95] across all scored trials | ≥85% |
| Predicted wall [p05, p95] coverage within each source | ≥75% |
| p90 across programs of proof-size median relative error | ≤10% |
| Predicted proof-size interval coverage across all scored trials | ≥85% |
| Predicted proof-size interval coverage within each source | ≥75% |

All 648 proofs and all 648 changed claims must pass native audit, and
train/heldout source, assignment, and statement hashes must be disjoint.
The exact model, calibration residuals, training corpus, and model
anchor must be committed **before** the first heldout package build;
heldout must require their exact bytes at a named ancestor commit.
Cold first-process, build, cross-host, and automatic-lowering claims
remain outside the passing scope even if every warm gate passes.

## Reproduction boundary

The native-free generator, arithmetic and runner chronology can be checked now:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_model.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_study.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/prospective.py preview
```

`preview` starts no native build and reads no v3 timing corpus. The
inventory is a **design artifact**. The runner implements frozen-source
and model-anchor chronology; its exact bytes and the engine/compiler stack
must be committed before `prepare` writes the final protocol. That protocol
must then be committed before the first native build. The full command
sequence and raw-artifact layout are in the
[runner README](../../../src/frontends/s31/benchmarks/mixed_cost_v4/README.md).
Measurements made before final protocol freeze would be exploratory and
cannot validate this preregistration.
