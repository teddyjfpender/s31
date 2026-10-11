# V17 mixed-length N4/N8 chip-call cost challenge

This is a prospective static freeze for one later native cost-model falsification. V11 and V15 are declared failed training ledgers; V12–V14 and V16 are declared local passes. Three new S31 sources use 16 live arithmetic branches, an unseen one-fifth multiplication ratio, four or eight sequential chip calls of mixed round lengths, and circuit log 13 or 14. Their exact source/claim hashes, predictions, admission geometry, schedule, and gates are frozen before any native V17 build.

Read [the design protocol](../../../../../design/s31/measurements/MIXED_COST_V17_MIXED_CALLS_PROTOCOL.md) for the arithmetic example, mixed-call transfer rule, exact admissions, and scope. Canonical model/protocol/source JSON under `design/s31/measurements/language/` is authoritative.

Static preflight:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/model.py check
python3 src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/protocol.py check
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls -p test_static.py -v
```

Only after independent preflight and a quiet host window, run the single frozen native study and audit:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/study.py run --out /absolute/isolated/v17-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v17_mixed_calls/audit.py --out /absolute/isolated/v17-artifacts --native --write
```

An admission or scored-gate failure is retained unchanged. The independent audit checks saved sources, claims, binaries, proof hashes, native geometry/reports, physical timing order, score arithmetic, and honest and changed-result verifier controls.
