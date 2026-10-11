# Independent review: S31 operation-mix cost transfer v1

All **six predeclared programs passed each of four local median-error gates**,
but the raw wall-time gate for multiply at 256 gates passed by only 0.95
percentage points. This is
evidence that the frozen row-stratum estimates transferred to these two new
operation families on this host. It is not a reliable general whole-prover
cost model or a source-to-proof soundness result. The [protocol](OPERATION_MIX_TRANSFER_V1.md),
[saved plan](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/plan.json),
[score](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/heldout-score.json),
and [native audit](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/audit.json)
contain the exact evidence.

## Freeze and controls checked

The local plan's SHA-256 is
`2fb561a3c2c1cdfd8fe79461e257daa3e0446cf3084f40a7b49be611ef701e1a`.
Its file timestamp preceded the first held-out source file, and its pinned
runner and independent scorer hashes still matched at review. It pins the
prior geometry plan (`363e0774…629f351`) and calibration
(`825f3d35…fdee8045`), six source hashes, 72 assignment hashes, the compiler
fingerprint (`893ce1f7…0b2e4dd1b`), stwo-zig commit
(`7d544c68…0cfeed`), host, and Python oracle provenance. The old calibration
was unchanged and was used without fitting or adjustment. This is a local
content and phase-order seal, not an external timestamp or independent
pre-registration.

The [second-source scorer](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/independent_score.py)
recomputed all six program medians and all four gate outcomes from 72 raw
trial reports without importing the runner. The separate native audit replayed
**72 accepted proofs and 72 rejected changed public-output claims**. Every
trial report also records a passed independent relation-value check. I checked
the six saved package relations have exactly their declared add or multiply
node counts, their raw/padded row counts match the plan, and all 72 public
outputs and statements match the closed forms
`(n + 1)·x mod (2^31 − 1)` for add and `x^(n + 1) mod (2^31 − 1)` for multiply.
The [compact ledger](../../../src/frontends/s31/benchmarks/operation_mix_transfer_v1/results-2026-10-11/compact-trials.json)
publishes all measured trial values and hashes; its SHA-256 is
`0d1f1dcac84ec21d1f6667d3e7229973b444bf3a8d71ebc869c854f9b27d8acd`.
Full packages and proofs remain in the ignored local `zig-out` evidence root,
so a checkout of Git alone cannot replay the native proof audit.

## All six held-out outcomes

Each program had 12 fresh prover plus verifier process observations. The
frozen predictor uses only its prior 512-row or 1024-row training center.
All errors below are absolute relative errors of the **program median**;
the fixed limits are 50% paired wall, 30% reported-PoW-subtracted wall,
10% proof bytes, and 15% prover RSS.

| Program | Raw / padded QM31 rows | Paired wall median | Wall error | After-PoW error | Proof-byte error | RSS error |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Add 96 | 416 / 512 | 97.74 ms | 28.46% | 1.85% | 0.64% | 1.88% |
| Add 256 | 576 / 1024 | 81.55 ms | 14.95% | 1.98% | 0.57% | 0.97% |
| Add 448 | 768 / 1024 | 148.63 ms | 36.93% | 0.73% | 0.48% | 1.41% |
| Multiply 96 | 416 / 512 | 121.84 ms | 3.05% | 1.42% | 0.63% | 1.53% |
| Multiply 256 | 576 / 1024 | 183.98 ms | **49.05%** | 0.23% | 0.26% | 0.53% |
| Multiply 448 | 768 / 1024 | 146.31 ms | 35.93% | 0.26% | 0.09% | 2.14% |

The independent scorer reported **pass** for each of the four overall gates
and each of the four gates within both operation families. Paired wall p90
reached 323.25 ms for multiply 96 and 321.60 ms for add 448; individual
PoW-subtracted observations reached 512.08 ms. These are broad-tail process
observations despite close median residuals. Subtracting reported native PoW
timers is diagnostic accounting, not a faster execution mode. The six package
builds took 52.89–53.27 seconds each and are excluded from the paired-process
target.

The 1024-row calibration rests on **one** prior mixed-operation training
program. The model has now been checked on one host, one compiler and engine,
one direct-gate lowering, and simple four-lane recurrences. It does not cover
other hosts, optimization or cache states, private-boundary calls, chips,
hashes, recursion, or reliable tail latency. All six programs have more than
16 gates and lie outside the bounded release compiler-correspondence proof.
The independent value checks and native verifier replays do not establish
that missing formal correspondence, PCS/FRI soundness, or a general native
verifier refinement theorem.
