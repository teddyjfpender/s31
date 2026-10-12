# S31 operation-mix transfer v1: local held-out result

The frozen 512/1024-row cost centers from the earlier alternating-gate study
passed all four predeclared diagnostic limits on six **new all-add and
all-multiply programs**, with no refitting. This is useful evidence that
proof bytes, prover RSS, and reported-PoW-subtracted process wall were stable
under this operation change on the pinned host. It is **weak evidence for
first-verified wall time**: the all-multiply 256-gate median error was
**49.05%**, only 0.95 percentage points below the 50% limit. The
[predeclared protocol](OPERATION_MIX_TRANSFER_V1.md) specifies the split,
predictor, and gates.

## Freeze, packages, and controls

The [plan](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/plan.json)
was written before any of this study's native builds. Its SHA-256 is
`2fb561a3c2c1cdfd8fe79461e257daa3e0446cf3084f40a7b49be611ef701e1a`.
It pins the prior geometry calibration SHA-256
`825f3d351a6a437a199db234a1ba86b0c2c36a8d34350991cc6238a8fdee8045`,
all six new source hashes and 72 assignment hashes, runner and independent
scorer hashes, and independent value-oracle provenance. The compiler
fingerprint stayed
`893ce1f78d19783eaafac3094dbbe847bdbb61de9a4b2055d3c8ff50b2e4dd1b`,
with stwo-zig gitlink `7d544c6839497ca19b6c7ef9b982e464f10cfeed`.
The host was one Apple M5 Max running macOS 26.7.1, Zig 0.15.2, and Python
3.14.6. The runner rejected changed compiler/engine/host identity before
measurement and checked the native padded geometry for every package.

Six new source-embedded packages each made 12 fresh prover and verifier
process trials. All **72/72 proofs** were accepted by the native verifier;
all 72 changed public statements were rejected, and all 72 independent
value-oracle checks passed. The separate
[native replay audit](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/audit.json)
accepted all 72 originals and rejected all 72 changed claims again. A
separate scorer, whose exact source hash was in the plan, independently
recomputed the six held-out medians, errors, and family/overall gates from
the raw trial reports. The
[held-out score](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/heldout-score.json)
has SHA-256
`a62d0359b82e023da7a89a33687fd4e04b52a5ea750bb1e39eeb7de92cf89316`.

| Operation / gates | Raw / padded QM31 rows | Wall observed / frozen prediction | Wall median error | After-PoW error | Proof-byte error | RSS error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Add / 96 | 416 / 512 | 97.74 / 125.56 ms | 28.46% | 1.85% | 0.64% | 1.88% |
| Add / 256 | 576 / 1024 | 81.55 / 93.74 ms | 14.95% | 1.98% | 0.57% | 0.97% |
| Add / 448 | 768 / 1024 | 148.63 / 93.74 ms | 36.93% | 0.73% | 0.48% | 1.41% |
| Multiply / 96 | 416 / 512 | 121.84 / 125.56 ms | 3.05% | 1.42% | 0.63% | 1.53% |
| Multiply / 256 | 576 / 1024 | 183.98 / 93.74 ms | **49.05%** | 0.23% | 0.26% | 0.53% |
| Multiply / 448 | 768 / 1024 | 146.31 / 93.74 ms | 35.93% | 0.26% | 0.09% | 2.14% |

The fixed maximum per-program median-error limits were 50% paired wall,
30% wall after reported PoW subtraction, 10% proof bytes, and 15% prover
RSS. Both operation families and all four overall gates passed. The
all-multiply 256-gate wall p90 was 318.98 ms, against a 183.98 ms median;
the all-add 448-gate wall p90 was 321.60 ms, against a 148.63 ms median.
Observed package builds took 52.89–53.27 seconds each under an uncontrolled
local Zig cache, excluded from the proof-process predictions. The exact
[held-out report](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/heldout-report.json)
records each build and actual geometry.

The after-PoW median errors were at most 1.98%, proof-byte errors at most
0.64%, and RSS errors at most 2.14%. PoW timer totals had very different
medians across programs: 34.65 ms for add/256, 88.63 ms for multiply/256,
and 101.59 ms for multiply/448. The timer subtraction is only an accounting
view of the same observed wall; it is not a mode that removes PoW work or a
tail-latency guarantee. In particular, this estimator should **not** be used
as a one-shot wall-time scheduler on the strength of a 49.05%-error pass.

The [compact ledger](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/compact-trials.json)
has SHA-256
`0d1f1dcac84ec21d1f6667d3e7229973b444bf3a8d71ebc869c854f9b27d8acd`.
It retains all 72 measured values, AIR row sizes, proof/trial hashes, and
control outcomes. Full packages, proofs, statements, and raw trial reports
remain under the ignored local `zig-out/s31-operation-mix-transfer-v1`
directory (about 55 MB), so Git alone cannot replay native verification.
`publish.py` copied the plan, report, score, and audit byte-identically and
made this ledger **after** measurement; that publication tool was not part of
the frozen prospective runner.

The plan was sealed locally, without an independently timestamped external
commit before native work. This is a controlled local prospective transfer,
not an externally frozen benchmark. It covers one host, one compiler and
engine revision, one `direct-gate` lowering, two simple operation families,
and two padded AIR sizes. All six programs exceed the 1–16-gate bounded
direct-gate release correspondence certificate; native proof acceptance and
value checks do not supply that missing formal compiler guarantee. No
cross-host, chip, hash, private-boundary, recursive, or build-cost transfer
claim follows. Automatic lowering remains disabled.
