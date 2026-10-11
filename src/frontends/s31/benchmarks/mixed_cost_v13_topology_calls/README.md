# V13 topology and call-count challenge

The study design, all gates, and the no-refit rule are in `design/s31/measurements/MIXED_COST_V13_TOPOLOGY_CALLS_PROTOCOL.md`.

From the isolated repository root, run `python3 src/frontends/s31/benchmarks/mixed_cost_v13_topology_calls/test_static.py` and `model.py check`. Before any native build, run `protocol.py freeze`, commit the canonical protocol and three source files with all scripts, then run `protocol.py check` and send the commit/hash for independent preflight.

During an exclusive CPU window, run `study.py run --out /tmp/unique-v13-run` once. It builds all packages, requires exact native geometry, then runs the frozen interleaved claims and writes immutable result/score artifacts. Run `audit.py --out /tmp/unique-v13-run --native --write` to check saved bytes and replay all honest/changed-result verifiers. Preserve a geometry or score failure unchanged.
