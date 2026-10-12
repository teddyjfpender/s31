# V16 sixteen-way fanout and log-14 cost challenge

This is a prospective, one-run test of whole-prover cost transfer after V15's proof-size interval failure. V11 and V15 are declared failed training evidence; V12–V14 are declared passing training evidence. Three new V16 sources use 16 live branches, 4,096 or 8,192 add/multiply operations, and one or two long chip calls. The exact source and claim digests, numeric predictions, schedule, and gates are frozen before any V16 native build.

Read [the design protocol](../../../../../design/s31/measurements/MIXED_COST_V16_FANOUT_PROTOCOL.md) for the arithmetic example, geometry admission, prediction rule, and interpretation limits. The canonical JSON under `design/s31/measurements/language/` is authoritative.

Static preflight:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v16_fanout/model.py check
python3 src/frontends/s31/benchmarks/mixed_cost_v16_fanout/protocol.py check
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v16_fanout -p test_static.py -v
```

The single native run requires independent preflight approval and a quiet host:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v16_fanout/study.py run --out /absolute/isolated/v16-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v16_fanout/audit.py --out /absolute/isolated/v16-artifacts --native --write
```

Admission or gate failure is a result to preserve. The independent audit checks exact files, geometry, scores, process timing endpoints, and honest and changed-result native verifier controls.
