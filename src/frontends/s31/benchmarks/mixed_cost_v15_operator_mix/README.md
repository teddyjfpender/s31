# V15 mixed-operator cost falsification

This is a prospective, one-run challenge of the V11–V14 whole-prover cost rule on an eight-way, 4,096-operation live circuit. It uses a pinned production compiler/engine and the same host and wall/RSS collection method as V12–V14. V11 failed; V12–V14 passed. All four scores are declared training evidence for V15. The V15 sources and claims are disjoint from them, and V15 native results are excluded from its predictor.

Read [`design/s31/measurements/MIXED_COST_V15_OPERATOR_MIX_PROTOCOL.md`](../../../../../design/s31/measurements/MIXED_COST_V15_OPERATOR_MIX_PROTOCOL.md) for the source shape, forecast rule, admission checks, and all gates. The canonical protocol and source JSON files under `language/` are authoritative.

Static preflight, before any native package build:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/model.py check
python3 src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/protocol.py check
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix -p test_static.py -v
```

The single native run requires a quiet host and parent approval of the frozen commit:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/study.py run --out /absolute/isolated/v15-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v15_operator_mix/audit.py --out /absolute/isolated/v15-artifacts --native
```

An admission failure or failed gate is a result to preserve. The audit recomputes scores from saved artifacts and replays honest and changed-result native verifier controls.
