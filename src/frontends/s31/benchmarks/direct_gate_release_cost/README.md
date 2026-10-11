# Bounded direct-gate process cost exploration

Run from the repository root after compiler and package sources have settled:

```sh
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/measure.py \
  --out zig-out/s31-direct-gate-release-cost --gates 1 4 16 --samples 3
```

The script generates three public four-lane recurrences in the independently
checked 1–16 add/multiply fragment. It builds one `direct-gate` package per
source, then runs three distinct assignments per package. Every observation
uses a fresh native prover process and a fresh native verifier process. The
trial routine requires native proof acceptance, changed public statement
rejection, and an independent value-oracle result. Saved trials retain the
proof, statement, source equations, and full process measurements.

`exploratory-report.json` has a compact `comparison` table of raw and padded
AIR rows, preprocessed cells, and median measured cost. Each full case also
lists FRI settings from its package's `cost-report.json` beside measured
prover/verifier wall time, proof bytes, and process peak RSS. The native cost
report does **not** predict wall time, proof bytes, or RSS. The `package_build`
duration is separate from proof process wall time and uses the host's
uncontrolled Zig cache. Reusing an existing package is recorded explicitly.
The diagnostic paired wall after reported PoW subtracts the two native PoW
timers from each paired process observation. It describes variability; it is
not a separate native execution mode.

This is an exploratory local comparison, not a prospective accuracy gate or
a calibrated predictor. The V8r1 historical cost protocol and its frozen
model are separate artifacts and are not refitted by this script.

## Local observation, 2026-10-11

The [saved summary](observations-2026-10-11.json) covers 20 distinct
assignments for each source (60 accepted native proofs, 60 rejected changed
claims, 60 passed independent value checks) on arm64 macOS. All three packages
had the same compiler digest and were reused in this measurement; package
compile time is outside the numbers below. The individual trial reports and
proofs remain in the ignored `zig-out/s31-direct-gate-release-cost` directory.

| Gates | Raw / padded QM31 rows | Paired wall median / p90 | Wall after reported PoW median | Proof bytes median | Prover RSS median |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 321 / 512 | 77.98 / 139.22 ms | 39.53 ms | 54,590.5 | 9,207,808 B |
| 4 | 324 / 512 | 84.84 / 217.30 ms | 29.54 ms | 55,261.5 | 9,199,616 B |
| 16 | 336 / 512 | 124.35 / 276.22 ms | 40.07 ms | 55,570.5 | 9,191,424 B |

Every package had 4,096 preprocessed cells and the same FRI parameters.
Median FRI PoW time was 44.58, 52.04, and 84.65 ms respectively; that
stochastic search drives much of the paired-wall spread. The PoW-subtracted
diagnostic stays around 30–40 ms, while proof size changes by under 2% and
peak RSS stays around 9.2 MB. These three source shapes and one host cannot
establish a throughput slope or a held-out prediction bound.

The quick source check covers every admitted gate count and M31 boundary
values without building Zig packages:

```sh
python3 -m unittest src/frontends/s31/benchmarks/direct_gate_release_cost/test_source.py -q
```

## Native square4 fixed-column fixture

`square4-fixed-columns.u32le` captures **all eight fixed Gate AIR columns at
all 512 physical rows** for the bounded `functional_square4_manual.s31`
direct-gate package. It is 16,384 bytes: column-major canonical M31 words as
little-endian `u32`. `square4-fixed-columns.json` records the source and
normalized-program hashes, native preprocessed root, per-column hashes, gate
counts, and the source operations' physical row positions. The binary keeps
the complete array auditable without a 4,096-number text dump.

After building the native package, reproduce and check the fixture from the
native `inspect-topology` command and the package's independently replayed
source, component manifest, and verification key:

```sh
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/fixed_columns.py check
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/fixed_columns.py row --row 502
python3 -m unittest src/frontends/s31/benchmarks/direct_gate_release_cost/test_fixed_columns.py -q
```

`check` additionally compares **every one of the 4,096 cells** with the
separately generated Lean `paddedArithmeticFixedRows` literal. A mismatch
reports its row and column. To intentionally regenerate the snapshot after
reviewing a compiler change, run `fixed_columns.py write`, inspect the binary
and metadata diffs, and then rerun `check`.

The fixture describes the *fixed/preprocessed* Gate schedule only. It does
not capture witness-dependent main or interaction columns, quotient
evaluations, or proof openings, and does not by itself establish soundness of
the complete proof. The native root binds this schedule within the package;
the separately generated Lean rows check that the formalization uses the same
physical fixed cells.

## Prospective local held-out cost check

The frozen V8r1 whole-prover protocol and model are separate. Its original
held-out evaluator stopped on an inherited program-inventory mismatch before
producing accuracy results, and the raw V8r1 corpus is not in this checkout.
The 60-proof exploratory result above also used an earlier compiler digest.
Neither artifact is used to fit this new local check.

`prospective.py` fixes three training programs (1, 4, 16 gates), three distinct
held-out programs (2, 8, 12 gates), and 12 assignments per program in code.
It records all planned source and assignment hashes, host, current compiler,
measurement script, and its own script hash **before** native work. Training
then seals a very simple prediction: the median of the three program medians
for each metric. The held-out command checks the sealed calibration before
building the remaining programs. It reports point errors separately for
paired process wall, paired wall after native PoW timer subtraction, proof
bytes, and prover RSS. It also reports PoW timing and how often held-out
trials fall within the raw training min/max. Those ranges are descriptive,
not statistical prediction intervals.

Run each phase in order, leaving its output intact:

```sh
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/prospective.py plan \
  --out zig-out/s31-direct-gate-prospective-v1
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/prospective.py train \
  --out zig-out/s31-direct-gate-prospective-v1
python3 src/frontends/s31/benchmarks/direct_gate_release_cost/prospective.py heldout \
  --out zig-out/s31-direct-gate-prospective-v1
python3 -m unittest src/frontends/s31/benchmarks/direct_gate_release_cost/test_prospective.py -q
```

This is a local diagnostic for a tiny, related, same-host direct-gate family.
All six programs use the same 512-row padded geometry, so the check cannot
validate extrapolation across AIR sizes, hashes, chips, private boundaries,
recursion, or hosts. Its four predeclared error limits are diagnostics, not
admission criteria for automatic lowering. PoW makes one-process wall time
especially variable; subtracting reported PoW timers is only an accounting
view of the same process observation.

### Local result, 2026-10-11

The [plan](prospective-plan-2026-10-11.json) was written before any of this
study's native work, and the [calibration](prospective-calibration-2026-10-11.json)
before the held-out packages were built. The
[training report](prospective-train-report-2026-10-11.json),
[held-out report](prospective-heldout-report-2026-10-11.json), and
[score](prospective-heldout-2026-10-11.json) retain source, assignment,
package, proof, and trial-report hashes. All 72 native proofs verified; every
changed public statement was rejected and every independent value oracle
passed. All six packages were newly built with compiler fingerprint
`98de7c870009451ba75afd00775cd7000f7a839e1c4b6adb8a316bf7f67e377d`.
Each package has 512 padded QM31 rows and 4,096 fixed cells; raw QM31 rows
range from 321 to 336.

The [compact trial ledger](prospective-trials-2026-10-11.json) keeps the 72
measured wall, PoW, proof-byte, and RSS values with their original report and
proof hashes. `test_saved_prospective.py` independently recomputes training
medians, held-out errors, and the predefined gates from this ledger without
native builds. Full native proofs and trial reports remain under the ignored
`zig-out/s31-direct-gate-prospective-v1` directory on the measuring host.

| Held-out gates | Paired wall median | Wall median error | After-PoW wall error | Proof-byte error | Prover-RSS error |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 2 | 87.97 ms | 16.33% | 4.07% | 0.62% | 0.18% |
| 8 | 103.38 ms | 28.80% | 8.68% | 1.75% | 0.36% |
| 12 | 126.29 ms | 41.72% | 8.54% | 0.17% | 0.00% |

The sealed constant predictions were 73.60 ms paired wall, 35.79 ms after
reported PoW, 55,261.5 proof bytes, and 9,191,424 prover RSS bytes. All four
predeclared diagnostic median-error limits passed. Yet the 12-gate wall
median was 41.72% above the predicted center. Held-out 8-gate wall p90 was
384.12 ms, while its median was 103.38 ms. Native PoW median varied from
48.99 to 88.17 ms across held-out programs; the 8-gate PoW p90 was
343.90 ms. Proof size and RSS were stable at this fixed padded geometry, but
the raw process-wall center is not precise enough for scheduling guarantees.
The plan was sealed locally in one workspace, not externally committed before
measurement; treat this as a controlled local holdout, not a frozen prospective
benchmark or evidence of transfer accuracy. The compiler fingerprint above is
the measured source revision. Later boundary/runtime changes alter the
compiler tree; these measurements must not be attributed to a later HEAD
without rerunning both train and held-out phases on that tree.
