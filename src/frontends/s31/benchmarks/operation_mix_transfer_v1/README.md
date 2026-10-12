# Prospective operation-family transfer of the geometry cost estimate

This study uses the already sealed
[`geometry_transfer_v1` calibration](../geometry_transfer_v1/results-2026-10-11/calibration.json)
as a **read-only** predictor for six new direct-gate text programs: all-add
and all-multiply recurrences at 96, 256, and 448 gates. It asks whether the
old 512/1024-padded-row cost centers transfer when operation mix changes.
There are 12 distinct four-lane assignments per source. All six programs
are held out; there is no fitting or source selection after measurement.
The completed [local result](../../../../../design/s31/measurements/OPERATION_MIX_TRANSFER_V1_RESULT.md)
passed all four diagnostic limits, but all-multiply 256 gates missed its
frozen wall center by 49.05%, nearly the full 50% allowance. Read that
limitation before using the observations for scheduling.

The plan pins the old calibration SHA-256 and plan SHA-256, new source and
assignment hashes, current compiler fingerprint, engine commit, host, runner
and independent scorer source hashes, independent value-oracle provenance,
estimator, and four diagnostic limits.
It rejects a compiler/host/engine mismatch with the old calibration before
any native build. Each package's actual padded QM31 rows must match the
predeclared 512 or 1024 stratum. Every trial requires native proof acceptance,
changed public-claim rejection, and an independent value-oracle check. The
later `audit` command replays each original and changed claim; the separate
`independent_score.py` recomputes all centers/errors from saved trial reports
without importing the runner.

After the machine is otherwise quiet, run from the repository root:

```sh
python3 -B src/frontends/s31/benchmarks/operation_mix_transfer_v1/test_static.py -q
python3 -B src/frontends/s31/benchmarks/operation_mix_transfer_v1/test_saved_result.py -q
python3 src/frontends/s31/benchmarks/operation_mix_transfer_v1/study.py plan \
  --out zig-out/s31-operation-mix-transfer-v1
# Preserve and inspect plan.json before the first native build.
python3 src/frontends/s31/benchmarks/operation_mix_transfer_v1/study.py heldout \
  --out zig-out/s31-operation-mix-transfer-v1
python3 src/frontends/s31/benchmarks/operation_mix_transfer_v1/study.py audit \
  --out zig-out/s31-operation-mix-transfer-v1
python3 src/frontends/s31/benchmarks/operation_mix_transfer_v1/independent_score.py \
  --out zig-out/s31-operation-mix-transfer-v1
```

The paired target is one fresh native prover plus one fresh verifier process.
Compilation, Python orchestration, and audit replays are separate costs.
The after-PoW metric subtracts native timer fields from the same process
observation; it is not a different execution mode. The fixed maximum
per-program median-error diagnostics are 50% paired wall, 30% after-PoW wall,
10% proof bytes, and 15% prover RSS. A pass is local to this one host,
compiler, engine, lowering, and two simple source families. It does not make
the estimate a general scheduling guarantee. All six sources exceed the
1–16-gate bounded release correspondence certificate; native verification
and value checks do not establish that missing formal correspondence.

The exact protocol and interpretation are in
[`OPERATION_MIX_TRANSFER_V1.md`](../../../../../design/s31/measurements/OPERATION_MIX_TRANSFER_V1.md).
