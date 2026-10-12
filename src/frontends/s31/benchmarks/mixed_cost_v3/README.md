# Mixed whole-prover cost v3: first process versus warm processes

This is a **prospective protocol and executable runner**, not a measured
result. It extends the v2 local baseline with a separate first-process
observation and a checked, disjoint breakdown of the existing native phase
timers. V2's frozen protocol, raw proofs, model, and evaluation are untouched.
No v3 accuracy or speed result exists until the native train/model/heldout
sequence below is run and audited.

## Workload and clocks

The source split stays the same as v2: training uses `control_n2`,
`control_n6`, `deep32_n2`, and `deep32_n6`; heldout uses `feeder_n4`,
`feeder_n6`, `fork_n4`, and `fork_n6`. Source bytes deliberately overlap
v2 to isolate the timing protocol change. V3 uses a new deterministic seed
and **eight new, distinct public claims per source**. The oracle checks each
claim against the source before any native run. Its assignment and typed
statement hashes are disjoint from the earlier cost protocols.

For each source, the runner builds one ReleaseFast package, then runs each
claim in **two adjacent fresh prover processes**, each followed by a fresh
native verifier process. The first and second processes use identical
assignment and statement bytes. Each proof has its own negative control:
the verifier must reject an ABI-valid changed public result with
`InvalidMixedInteractionNonce`. There are 16 proof processes per source,
64 per split, 128 overall. Trial 0 is the first invocation after that
package build; trials 1–15 form the warm cohort. Package build wall is
reported separately.

Here, “cold” means **first observed process after this package build**.
The build, source file writes, filesystem cache, CPU state, and operating
system may already be warm. A difference between trial 0 and the identical
claim repeated at trial 1 is an observation, not a causal estimate of
process startup or cold-cache cost. Both trials are fresh processes; no
in-process JIT warmup exists. The native verifier has no internal stage
timer, so its entire process wall remains one measured slice.

## What a timing row means

The native reports are nested. The runner checks their identities and
arithmetic, then partitions the measured prover-plus-verifier process wall:

```text
prover + verifier process wall
  = prover wall outside reported package stages
  + package stages outside native proving
  + native outer interval outside proof body
  + proof body outside interaction PoW and PCS
  + interaction PoW
  + PCS outside FRI PoW
  + FRI PoW
  + external verifier process wall
```

`native outer interval outside proof body` includes setup, caller work,
proof assembly, and cleanup that the inner timer does not cover. It is
**not** labeled “pure setup.” The prover-wall residual includes process
startup, I/O, instrument gaps, exit, and scheduler effects; it is **not**
an isolated startup timer. `pcs_prove_ns` already contains FRI PoW, so
adding the two would double-count. The code rejects negative durations,
inconsistent identities, impossible nesting, and a partition whose sum
differs from the measured wall.

The per-program `cold_warm` record saves, for each selected wall or
native stage, the first value, the same-claim repeat, the median over all
later processes, and the signed first-minus-repeat difference. Negative
differences are retained.

## Predeclared fit and claims

The model predicts **warm** first-verified process wall as the median of
the four training-program warm medians. It predicts proof bytes by ordinary
least squares against live chip call count on the four training-program
warm proof medians. Training warm-trial 5th/95th actual-to-predicted ratios,
clamped to include one, form empirical bands. The heldout gate requires:

| Diagnostic | Threshold |
| --- | ---: |
| Warm program-median wall p90 relative error | ≤ 30% |
| Program-median proof-size p90 relative error | ≤ 10% |
| Warm wall trial band coverage | ≥ 70% |
| Proof-size warm trial band coverage | ≥ 80% |

Cold first-process values and phase costs are **descriptive only**. Four
first-process samples per split cannot support a stable cold-tail model.
Passing the warm gates would support only local accuracy on the pinned
host, compiler, source families, and timing protocol. It would not show
cross-host reliability, cold-tail accuracy, automatic lowering quality, or
speedup against Cairo or another system.

## Exact experiment sequence

Run from the S31 repository root on a quiet host. First commit the code
for this runner and the current compiler/runtime. The `prepare` action
creates the deterministic claim roster and pins tool, compiler, engine,
host, Zig executable, and prior protocol bytes. Review and **commit the
protocol before the first native build**. Any post-freeze source change
requires a new protocol/version, not an edited v3 result.

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py prepare
# Review and commit design/s31/measurements/language/mixed-cost-v3-protocol.json.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py train \
  --out zig-out/s31-mixed-cost-v3
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py audit-train \
  --out zig-out/s31-mixed-cost-v3
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py fit \
  --out zig-out/s31-mixed-cost-v3
# Review and commit v3 train corpus, model, and model-anchor JSON.
# Copy exact model SHA-256 and full anchor commit from that commit.
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py heldout \
  --out zig-out/s31-mixed-cost-v3 \
  --model-sha256 <exact-model-sha256> --model-anchor-commit <full-commit>
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py audit-heldout \
  --out zig-out/s31-mixed-cost-v3
python3 -B src/frontends/s31/benchmarks/mixed_cost_v3/study.py evaluate \
  --out zig-out/s31-mixed-cost-v3 \
  --model-sha256 <exact-model-sha256> --model-anchor-commit <full-commit>
```

`train` and `heldout` require a new raw directory for their respective
split. The heldout command checks the exact model, anchor, and training
corpus bytes against the named ancestor commit **before it creates a
heldout directory or builds a package**. `fit` replays the accepted and
changed-claim native verifier checks for training; `evaluate` does so
for heldout. Compact JSON alone cannot replay native verification: retain
the raw package binaries, proofs, statements, stderr, and build logs in
`zig-out/s31-mixed-cost-v3` with their recorded hashes.

The first native run is intentionally deferred while concurrent compiler
and formal work changes the source tree and competes for CPU. This README
specifies the experiment; it does not report fabricated timings.
