# Eighty-claim transfer of the unchanged v4 whole-prover predictor

V5's 20-claim N=1 median missed its preregistered wall gate while its proof
size and interval coverage passed. This separate v6 cohort uses **new source
families and 80 new scored claims per source** to make a median check less
sensitive to a handful of PoW draws. It does not rerun, relabel, refit, or
replace v5. The source programs and all claim hashes are disjoint from v4 and
v5. Their exact source JSON bytes are committed next to the protocol.

The frozen v4 model receives only call count. `offset_seed_n1` adds a
constant, runs one 16-round chip call and scales its result before the public
sum. `crosswind_n8` alternates scaling and offsetting the previous value,
runs eight 16-round calls, and adds the original input between calls. Both
use the already admitted `direct-mixed-general` operation vocabulary; their
actual native admission remains part of this prospective experiment.

From the repository root, in this order:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/protocol.py freeze
# Commit both sources, the protocol, and every transfer script before Zig.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/protocol.py check
# Run only after other heavy host work completes.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/study.py run \
  --out zig-out/s31-mixed-cost-v6-transfer
python3 -B src/frontends/s31/benchmarks/mixed_cost_v6_transfer/audit.py \
  --out zig-out/s31-mixed-cost-v6-transfer --native --write
```

Claim 0 is run twice for descriptive first-post-build and same-claim-repeat
observations. Claims 1–80 are scored. Each of the 164 fresh process pairs
must produce a proof accepted with its typed statement, while an ABI-valid
changed public result must be rejected at the interaction nonce. The native
manifest, component geometry, PoW settings, build wall, proof size, phase
timings, and monotonic prover/verifier endpoints are saved. The post-run
auditor checks all artifact hashes and independently replays the saved proofs
and changed claims. Raw binaries and proofs remain local under `zig-out/`;
compact canonical results live in `design/s31/measurements/language/`.

Each source must meet all four frozen limits: warm-wall median relative error
≤30%, predicted 90% wall interval coverage ≥80%, proof-size median error
≤10%, and predicted 90% proof interval coverage ≥80%. The first process and
build walls are descriptive only. A native build or proof failure is a failed
admission observation; the runner will not select a rerun by score. Even 80
trials on one host cannot establish general coverage, and no Cairo speedup is
measured.
