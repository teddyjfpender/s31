# V18 prospective N6/N7 branch-topology cost challenge

The V18 model openly trains on failed V11/V15/V17 and passed local V12–V14/V16 ledgers. Three new S31 sources vary branch count (8/32), multiply ratio (one-third/one-seventh), six/seven chip calls, and circuit log 13/14. The exact source/claim hashes, predictions, full native manifest admission, interleaved schedule, and conjunctive gates are frozen before any native V18 build.

Read [the design protocol](../../../../../design/s31/measurements/MIXED_COST_V18_TOPOLOGY_TRANSFER_PROTOCOL.md) for the hand-written arithmetic example, prediction rule, admissions, and limits. Canonical model/protocol/source JSON under `design/s31/measurements/language/` is authoritative.

Static preflight:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/model.py check
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/protocol.py check
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer -p test_static.py -v
```

Only after independent preflight and a quiet host window, run the single frozen native study and audit:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/study.py run --out /absolute/isolated/v18-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/audit.py --out /absolute/isolated/v18-artifacts --native --write
```

An admission or scored-gate failure is retained unchanged. The fixed `design/s31/measurements/language/mixed-cost-v18-topology-transfer-attempt.jsonl` marker is atomically created and synced before the first build; any second invocation is rejected. The runner and audit require a strictly positive non-PoW residual before score arithmetic.
