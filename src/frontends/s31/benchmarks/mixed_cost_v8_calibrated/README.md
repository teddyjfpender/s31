# Prospective V8 whole-prover transfer

This experiment fits a **new** cost model using only the committed, clean V4,
V5, and V7 artifacts. V6 was invalidated by a compiler fingerprint change
while timing and is excluded entirely. V7 stays a failed transfer; its errors
are training evidence for V8, never re-scored as V8 validation.

## What the model predicts

The V4 non-PoW whole-process baseline and 156 calibration residuals stay
fixed. The V4 proof-size center also stays fixed. In the eight clean training
source blocks, manifest geometry is collinear with call count:

| Feature | Observed formula for call count `c` |
| --- | --- |
| Main columns | `17c + 12` |
| Interaction columns | `28c + 8` |
| Constraints | `19c + 11` |
| Slots | `2c + 1` |

A separate geometry regression cannot identify a new effect from these data.
V8 tests two new source structures at one and eight calls, with the same
admitted mixed profile and fixed 20/26-bit interaction/FRI PoW settings.

FRI PoW uses a four-component exponential mixture. Each component's scale is
the observed median FRI phase time divided by `ln(2)` for one clean V5 or V7
source. Each source receives equal weight, regardless of its claim count.
The interaction PoW scale and non-PoW residual distribution remain V4's.
Convolving these gives frozen 5th, 50th, and 95th percentiles for total warm
proof-plus-verifier wall time. The model also reports an **empirical source-rate
envelope**: the median wall forecast under the smallest and largest of those
four FRI rates. That envelope is descriptive, not a confidence interval.

Proof-size intervals have the unchanged V4 center and a separate relative
half-width for small (one/three-call) and large (seven/eight-call) profiles.
For each source, take the finite-sample 95th percentile of absolute relative
errors in V4 calibration claims 41–79 or all scored V5/V7 claims; within each
profile, use the maximum source percentile. The resulting small and large
widths are approximately **5.87%** and **4.24%**. This is deliberately
conservative relative to a nominal 90% interval, but four source blocks per
profile do not establish coverage for arbitrary new source families.

The fit records exact input artifact SHA-256 values, source names and hashes,
calibration counts, FRI medians, and proof ranks in a committed model JSON.
The V8 protocol records exact source/claim hashes and numeric predictions,
pins the model and compiler/runtime tools, and checks that its two source IDs
and all claims are fresh relative to V4–V7. The model, protocol, source JSON,
and scripts must be committed before the first native package build.

## Prospective evaluation

`folded_seed_n1` transforms a public four-word input, runs one 16-round chip
call, then scales and adds the input. `braided_scan_n8` alternates scaled and
additive feeders across eight 16-round calls, with two intermediate offsets,
then scales and adds the input. Both produce versioned eight-word public
proof claims. Claim zero is measured twice for descriptive startup effects;
claims 1–80 per source are scored exactly once, in ascending order. Every
proof must verify and every ABI-valid changed public result must be rejected
at the interaction nonce.

The **same four V7 limits** apply separately to each source: warm-wall median
relative error at most 30%; coverage of the predicted nominal 90% wall
interval at least 80%; proof-size median relative error at most 10%; and
coverage of the nominal 90% proof interval at least 80%. All eight checks
must pass. There is no score-selected rerun or coefficient update. Build
wall, the first two claims, PoW phases, native geometry, and the source-rate
envelope are reported separately. The benchmark makes no Cairo speedup
claim.

From the repository root, after compiler/runtime source stability is agreed:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/model.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/model.py freeze
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/protocol.py freeze
# Commit the model, protocol, source JSON, and scripts before Zig.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/model.py check
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/protocol.py check
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/study.py run \
  --out zig-out/s31-mixed-cost-v8-calibrated
python3 -B src/frontends/s31/benchmarks/mixed_cost_v8_calibrated/audit.py \
  --out zig-out/s31-mixed-cost-v8-calibrated --native --write
```

This remains a one-host, one-stack transfer test. The four recent PoW source
blocks are too few to claim a generally reliable clock distribution. New
geometry, changed PoW difficulty, process contention, or host thermal/rate
drift can break the prediction. Such a failure will be retained in the
committed score.

The single prospective run passed all eight frozen gates; the exact
[result and limits](../../../../../design/s31/measurements/MIXED_COST_V8_CALIBRATED_RESULT.md)
are committed with the native replay audit. The V5 and V7 failures remain
separate historical scores.
