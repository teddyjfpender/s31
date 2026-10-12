# Independent V18 static preflight — 2026-10-12

**Verdict:** approve one prospective native run of frozen candidate `f73bbaa` after a quiet host window. No V18 native build or timing was run during this review. The frozen 35% per-source wall-median gate and 1.5× sample-median band were chosen after the preserved V17 failure and are exploratory; a V18 pass would not establish general cost reliability.

In isolated worktree `/tmp/s31-v18-mixed-topology-e9be79a`, the following exited 0:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/model.py check
python3 src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/protocol.py check
python3 -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer -p test_static.py -v
git diff --check
```

The six static tests include balanced per-slot constraint mutation, changed call identity/feeder/constant, broken four-lane address chain, changed registry role, nonpositive residual, and fixed-marker retry controls after both a recorded failure and a started-only interruption. [Study code](../../../src/frontends/s31/benchmarks/mixed_cost_v18_topology_transfer/study.py) creates the fixed marker with `O_EXCL`, fsyncs file and directory before the first build, and admits all three exact manifests before proving claim zero.

I independently read canonical JSON without calling the model, protocol, study, or audit scoring functions. V17 scored medians, V12 PoW quantiles, and the V16 proof interval reproduce every V18 prediction, including proof centers 227,381.25 / 251,990.25 / 267,093.875 bytes and non-PoW centers 147,271,854 / 246,275,562 / 247,812,614 ns. Parsed source node order reproduces all N6/N7 call IDs, feeder/source IDs, rounds, and constants. All frozen slot roles, offsets, counts, trace logs, tree columns, and total constraints match independently accumulated geometry. Direct M31 evaluation of 63 claims reproduces all 126 assignment/statement SHA-256 digests; the three source hashes and all 126 claim hashes are disjoint from prior protocol digests. The 60 scored schedule entries are unique.

Frozen [model](language/mixed-cost-v18-topology-transfer-model.json) SHA-256 is `97a1a02ebd1a69022fe9e810ec392078d7eb4450aa4573d51582f98953c05058`; frozen [protocol](language/mixed-cost-v18-topology-transfer-protocol.json) SHA-256 is `07dab408bad90494613a8d67d5b5240cb8bb746398a07b59df4ea87503ad4840`. Native manifest equality, 66 honest proofs, 66 changed-result rejections, physical timing, and all scored gates remain untested until the one allowed native run.
