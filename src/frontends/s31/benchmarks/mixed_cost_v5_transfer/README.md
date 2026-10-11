# Prospective v4 cost-model transfer at N=1 and N=8

This is one out-of-distribution check of the **already frozen** v4 predictor.
The model was fit at 3 and 7 repeated chip calls and held out at 5 and 7.
The new `scaled_seed_n1` and `weighted_scan_n8` sources have one and eight
calls. They use new source hashes, new 16-round constants, a pre-scaling
feeder and a weighted scan feeder. The model receives only call count. Its
predicted warm wall quantiles and proof-size interval are written into the
protocol before any native package build.

Run from the repository root:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v5_transfer/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v5_transfer/protocol.py freeze
# Commit the protocol, scripts, and this README before running Zig.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v5_transfer/protocol.py check
python3 -B src/frontends/s31/benchmarks/mixed_cost_v5_transfer/study.py run \
  --out zig-out/s31-mixed-cost-v5-transfer
```

The protocol fixes 21 assignments per source. Claim 0 is run twice in adjacent
fresh prover/verifier processes for first-post-build and same-claim-repeat
diagnostics. Claims 1–20 are each run once and scored. All 44 proofs must
verify with their typed public statements; each ABI-valid changed public
result must be rejected at `InvalidMixedInteractionNonce`. The runner records
the full native manifest, interaction and FRI PoW difficulty, package build
wall, prover and verifier monotonic endpoints, native phase reports, proof
size, and proof hashes. Raw proofs and stderr stay under `zig-out/`; the
compact result and score go to `design/s31/measurements/language/`.

The four preregistered per-source limits are median wall error ≤35%, 90%
wall interval coverage ≥70%, median proof-size error ≤10%, and 90% proof
interval coverage ≥70%. Cold and build timings have no accuracy gate. A
build or proof failure is a failed transfer observation; the output directory
is retained and the runner refuses a score-selected second run. Twenty scored
claims per source give only a rough empirical coverage check. This is a
host-, compiler-, and engine-specific cost-model check, not a Cairo speedup
claim or a general statistical guarantee.
