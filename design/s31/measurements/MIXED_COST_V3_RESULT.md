# Prospective mixed whole-prover cost v3: local held-out result

**Result: the v3 warm-wall/proof-size model failed two of its four frozen
held-out gates.** The failure is retained as measured. The constant warm-wall
prediction missed one held-out program badly, and the proof-size interval
covered too few individual trials, although proof-size program medians were
close. V3 provides a clearer first-process and nested-stage diagnostic; it
does not yet establish a reliable whole-workflow cost model.

The [protocol JSON](language/mixed-cost-v3-protocol.json) was committed as
`0f23dd5` before the first native build, with SHA-256
`6460e13cc5a93623a0ee55e347ea006c416164ab2d425d251efe7d4003a012e6`.
The **clean** training corpus, exact model bytes, and anchor were committed
together as `de6d2e8af4eb44156f2908348024165b5367e510` before the first
held-out build. The [model JSON](language/mixed-cost-v3-model.json) has SHA-256
`12dd2f357e7e37ca5563968526d3af33b83d18c22deb38d8a9886cb9dd35116b`.
The held-out command checked the model, anchor, and train bytes against that
ancestor commit before creating its held-out directory.

## Aborted attempt and clean rerun

One earlier training run used the same frozen protocol but was excluded
because an independent formal unit suite used about one CPU core for about
15 seconds around **2026-10-11 18:02:30 UTC**, overlapping the `deep32_n6`
package build. This was reported during collection, before using a score to
choose a run. Its raw evidence and generated fit remain in the local
`zig-out/s31-mixed-cost-v3` directory as an aborted record. The single
replacement training run was collected in
`zig-out/s31-mixed-cost-v3-clean`; **only its** corpus, model, and bands were
used for heldout. The replacement train corpus SHA-256 is
`40e30571e0f24c6ff1eb443e9728dc3449e77cb0e8f20dbccc8dfe5a5889ae74`.

## Fixed predictions and held-out observations

The frozen fit predicts **85.211 ms** warm first-verified process wall for
every source: the median of four training-program warm medians. It predicts
proof size as **54,887.25 + 14,742.375 × chip calls** bytes. “Warm” here
means trials 1–15 for each source; every trial starts a new prover and native
verifier process. Trial 0 is the first invocation after package build.
Training ratios gave a 0.485–3.274× warm-wall band and a 0.979–1.022×
proof-size band. These are empirical bands, not confidence intervals.

| Held-out source | Warm wall predicted / observed median | Wall error | Proof predicted / observed median | Proof error | Build wall |
| --- | ---: | ---: | ---: | ---: | ---: |
| `feeder_n4` | 85.21 / 96.30 ms | 11.52% | 113,857 / 114,331 B | 0.41% | 52.70 s |
| `feeder_n6` | 85.21 / 108.27 ms | 21.30% | 143,342 / 143,484 B | 0.10% | 53.40 s |
| `fork_n4` | 85.21 / 96.41 ms | 11.62% | 113,857 / 112,246 B | 1.44% | 54.02 s |
| `fork_n6` | 85.21 / 201.35 ms | 57.68% | 143,342 / 142,806 B | 0.37% | 54.02 s |

| Frozen gate | Held-out result | Threshold | Outcome |
| --- | ---: | ---: | --- |
| Warm-wall p90 program-median relative error | **46.76%** | ≤30% | **Fail** |
| Proof-size p90 program-median relative error | 1.13% | ≤10% | Pass |
| Warm-wall trial band coverage | 56/60 = 93.33% | ≥70% | Pass |
| Proof-size trial band coverage | **39/60 = 65.00%** | ≥80% | **Fail** |

The proof-size center was useful for these four program medians, but the
training band was too narrow for individual held-out proofs. The wall band
was wide enough to cover most warm trials, yet the fixed center missed
`fork_n6`. This is a failed local reliability gate, not evidence of a
speedup or a cost regression against v2: v2 and v3 sampled different claims
and timing windows.

## What cold and native stages showed

The first process after each package build was much slower than its
same-claim repeat. Each pair used identical assignment and public statement
bytes and two separate proof processes.

| Source | First process | Same-claim repeat | Warm median | First minus repeat |
| --- | ---: | ---: | ---: | ---: |
| `feeder_n4` | 1,766.96 ms | 154.75 ms | 96.30 ms | 1,612.21 ms |
| `feeder_n6` | 1,015.39 ms | 45.95 ms | 108.27 ms | 969.44 ms |
| `fork_n4` | 1,049.71 ms | 57.55 ms | 96.41 ms | 992.16 ms |
| `fork_n6` | 1,261.73 ms | 147.18 ms | 201.35 ms | 1,114.55 ms |

“First” is an observational label, not an isolated process-startup or
cold-cache timer. Build and source writes can already warm caches. There
are only four first-process samples per split, so v3 makes no cold-tail
accuracy claim. Package build wall is also measured but remains outside
the predicted target.

The native timing report exposes nested intervals. The runner converts
them to **disjoint slices** that sum exactly to prover-plus-verifier process
wall for each trial. The table gives warm-trial medians of selected slices
in milliseconds; separate medians need not sum to the median total.

| Source | Native prove incl. setup | FRI PoW | Interaction PoW | PCS excluding FRI PoW | Package outside native | Prover wall outside package | Verifier process |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `feeder_n4` | 70.27 | 64.77 | 2.06 | 0.97 | 2.53 | 10.91 | 15.20 |
| `feeder_n6` | 76.98 | 70.32 | 0.46 | 1.09 | 2.86 | 11.34 | 16.15 |
| `fork_n4` | 77.95 | 70.30 | 1.57 | 1.03 | 2.48 | 8.55 | 14.23 |
| `fork_n6` | 171.32 | 165.41 | 1.92 | 1.09 | 2.79 | 12.04 | 14.74 |

FRI PoW dominated the warm native interval on these four held-out sources.
The `fork_n6` median FRI PoW was **165.41 ms**, versus 70.30–70.32 ms on
three others. Individual FRI PoW times were also highly variable (for
example 28.4–241.6 ms on `fork_n6`), so the constant wall fit cannot
predict a particular proof's PoW search duration from source shape alone.
The available inner/outer timers do not isolate a pure setup interval;
`native prove incl. setup` and the explicit package compile/witness
stages are the supported setup-related measurements.

## Native audit and limits

All **128** original proofs (64 training, 64 heldout) were accepted by
their source-embedded native verifiers. All **128** ABI-valid claims with
one changed public result were rejected specifically at
`InvalidMixedInteractionNonce`. The read-only raw auditor replayed both
outcomes for every retained proof and checked source, assignment, typed
statement, proof, package binary, stderr, stage identities, and the
non-overlapping wall partition. The canonical audit records are
[train audit](language/mixed-cost-v3-train-audit.json) and
[heldout audit](language/mixed-cost-v3-heldout-audit.json).

The [train corpus](language/mixed-cost-v3-train.json),
[heldout corpus](language/mixed-cost-v3-heldout.json), and
[evaluation](language/mixed-cost-v3-evaluation.json) retain hashes and
measurements. Heldout corpus SHA-256 is
`9056e4a7e2f29d17bd1cce42c5d960efc763ef1d18c37707bc90ec735e7c4bd0`;
evaluation SHA-256 is
`71b735970c5f28587c49f45bc75c05896aa6c5ef5c5724e4c4bbace22825a68e`.
The raw package binaries, proofs, and logs are local in
`zig-out/s31-mixed-cost-v3-clean`, not tracked in Git. A fresh clone
cannot replay native verification from compact JSON alone. The exact
sequence and formulas are in the [runner README](../../../src/frontends/s31/benchmarks/mixed_cost_v3/README.md).

The next cost study should predeclare a model of a latency **distribution**
or PoW quantiles, include repeated independent first-process sessions, and
measure build plus verification separately. Any new fit or threshold must
use a new protocol and untouched heldout claims.
