# V9 fixed-call geometry stress transfer

The [unscored feasibility
probe](../../../../../design/s31/measurements/MIXED_COST_V9_GEOMETRY_FEASIBILITY.md)
established that, at one chip call, a long live circuit chain raises circuit
trace log 9→10 without changing chip trace log 4, while a 1,024-round chip
raises chip trace log 4→10 without changing circuit trace log 9. Both leave
column widths `[8,29,36,8]`, constraints 30, and slot count 3. V9 tests
three **fresh** sources outside the V8 model's training geometry:

| Source | Gate chain | Chip rounds | Frozen expected circuit/chip trace logs |
| --- | ---: | ---: | ---: |
| `gate_ladder_n1` | 256 live multiplications | 16 | 10 / 4 |
| `chip_sweep_n1` | 0 | 1,024 | 9 / 10 |
| `joint_ladder_n1` | 256 live multiplications | 1,024 | 10 / 10 |

All three have one call, so the already frozen V8 predictor assigns **the
same numeric forecast**: 90.29 ms warm-wall median, nominal wall interval
34.88–335.55 ms, 70,006.75-byte proof center, and proof interval
65,898–74,115.5 bytes. There is no new fit or geometry coefficient. The
purpose is to find whether a cost model learned on log-9 circuits and
16-round chips transfers to these larger traces. This is an out-of-domain
stress test; failures remain failures.

The protocol pins all three exact source JSON files, 81 assignments and
typed statements per source, the V8 model, compiler/runtime/tool bytes, the
engine gitlink, and fixed manifest geometry for each source. It rejects
source IDs from V4–V8 and the two feasibility probes and requires all 486
new assignment/statement identities to be unique. Each source's claim zero
is proved twice for descriptive startup timing; 80 new claims are scored
once in ascending order. All 246 honest proofs must verify and all 246
ABI-valid changed public results must fail at the interaction nonce.

The same four V8 limits apply per source, for **12 total gates**: wall-median
relative error ≤30%; coverage of the nominal 90% warm-wall interval ≥80%;
proof-median relative error ≤10%; proof interval coverage ≥80%. A geometry
or final pin mismatch invalidates the run rather than producing a model
score. The runner and independent auditor retain and check exact source,
binary, manifest, statement, proof, timing-endpoint, and stage hashes. The
score is prospective and has no selected rerun or refit.

From the repository root:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/protocol.py freeze
# Commit protocol, source JSON, and all V9 scripts before scored native timing.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/protocol.py check
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/study.py run \
  --out zig-out/s31-mixed-cost-v9-geometry-transfer
python3 -B src/frontends/s31/benchmarks/mixed_cost_v9_geometry_transfer/audit.py \
  --out zig-out/s31-mixed-cost-v9-geometry-transfer --native --write
```

The manifest-only feasibility sources are never scored. V9 is one-host,
one-stack evidence at these three fixed-call shapes. PoW remains stochastic;
the V8 mixture came from only four clean source blocks. The experiment does
not establish accuracy for arbitrary circuits, higher column counts, other
PoW settings, or a speedup against Cairo.
