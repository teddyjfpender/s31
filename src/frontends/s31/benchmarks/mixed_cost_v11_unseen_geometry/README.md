# V11 unseen-geometry cost falsification

This is a prospective test of whether V10's one-call cost coefficients survive
one more trace-log step. It is **not** a fitted or validated log-11 predictor.
The V10 same-geometry holdout passed all 12 gates, but its three log pairs were
used to fit V10. The earlier V9 transfer failed six of twelve gates when V8
was applied to previously unseen log-10 geometry. V6 was integrity-invalidated
and supplies no timing evidence. V10 scored results and the paired-lowering
experiment are explicitly excluded from V11 fitting.

| Source | Live mul gates | Chip rounds | Expected circuit/chip log | Calls | Slots |
| --- | ---: | ---: | ---: | ---: | ---: |
| `gate_surge_n1` | 512 | 16 | 11/4 | 1 | 3 |
| `chip_surge_n1` | 0 | 2,048 | 9/11 | 1 | 3 |
| `joint_surge_n1` | 512 | 2,048 | 11/11 | 1 | 3 |
| `serial_surge_n2` | 0 | 2,048 then 16 | 9/11 | 2 | 5 |

The one-call circuit/chip log pairs 11/4, 9/11, and 11/11 and the two-call
9/11 profile are absent from V4–V10 fit geometry. Each source and its 21
claims have new hashes disjoint from prior protocol rosters. Python evaluates
every claim independently from source semantics. Static sizing follows the
published one-call 256-gate/1,024-round manifests and the mixed component
roster: circuit rows are expected to double for 512 live four-lane mul gates;
chip trace rows equal rounds; each call contributes one chip and one bridge.
These are **expected**, not independently measured AIR dimensions. The native
manifest guard requires exact logs, columns, constraints, component count,
source digest, call rounds, registry digest, and PoW settings before a single
proof is timed. A mismatch invalidates the run.

`model.py` freezes a deliberately simple extrapolation. Starting from the
V4 call intercept and slope, each increase of the maximum trace log beyond 9
adds V10's V9-fitted 15,362.75-byte contrast. Each circuit-log increase
beyond 9 also adds V10's 2,060-byte contrast. The first chip shift represents
the entire log 4→10 change; the identical shift is reused once for 10→11.
The V10 PoW-rate mixture, non-PoW residual sample, and 6.462% proof interval
half-width are retained. There is no new fit to V10 scored results. The
resulting proof centers are 104,852.25 B for gate and joint, 100,732.25 B for
chip, and 115,278.5 B for serial. A failed gate is reported as a failed
extrapolation, with no scored rerun or refit.

One frozen run scores claims 1–20 in ascending order for each source. Claim 0
is proved once after the package build and immediately repeated; both are
descriptive. Each of the 88 honest proofs must verify against its typed
statement, and each corresponding ABI-valid changed public result must be
rejected at the proof layer. The independent auditor reconstructs every
source, assignment, honest statement, exact changed statement, proof hash,
native phase report, and score, then replays both native verifier outcomes.
The saved corpus contains source-pinned executables, manifests, proofs, and
timing endpoints. Package build wall time is reported separately.

For each fresh prover and external verifier process, V11 records process
wall, OS peak RSS, proof bytes, and native reported interaction/FRI PoW.
Verified wall minus the native PoW report is a **descriptive residual**; it
includes verifier process time, launch overhead, and measurement differences.
RSS and the phase split have no predictive gate because V10 did not calibrate
their distributions. `/usr/bin/time` wraps the timed processes to obtain RSS,
so V11 wall has wrapper overhead absent from the V10 fit. This is recorded as
a method change. On a host without parseable process RSS, the run fails.

The four prespecified gates are applied **separately to each source**:
observed wall median relative error ≤30%, nominal 90% wall interval coverage
≥80%, observed proof median relative error ≤10%, and nominal 90% proof
interval coverage ≥80%. With only 20 scored claims, 80% means 16/20. The
single host and four related source blocks cannot establish calibration or
reliability across programs, chips, hosts, compiler revisions, or logs >11.
There is no Cairo speedup inference.

## Reproduce

From the repository root, before any native timing:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/model.py check
python3 -B -m unittest discover -s src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry -p test_static.py -v
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/protocol.py preview
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/protocol.py freeze
# Commit the model, protocol, source JSON, and all pinned scripts.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/protocol.py check
```

In an otherwise quiet native window, after the pin check:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/study.py run --out /tmp/s31-v11-unseen-<commit>
python3 -B src/frontends/s31/benchmarks/mixed_cost_v11_unseen_geometry/audit.py --out /tmp/s31-v11-unseen-<commit> --native --write
```

The protocol rejects compiler/runtime/tool changes after freezing. Raw proof
corpus is local; compact result, score, and audit JSON are committed in
`design/s31/measurements/language/` after the run.
