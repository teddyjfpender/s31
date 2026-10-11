# Mixed-general whole-prover cost: prospective source-shape transfer v1

**Status: design and tooling only. No transfer native corpus, accuracy result,
or speedup claim exists.** The [local v1 result](MIXED_STAGE_COST_MODEL_V1_RESULT.md)
passed its predeclared gates for one 16-round repeat-chain family on one host.
This protocol asks whether its **already frozen training-only model** predicts
new source shapes. The old held-out timings, proof lengths, and stage reports
are never fitted or used to choose these gates. The [machine-readable design](language/mixed-stage-cost-transfer-v1-prospective.json)
fixes the new roster and thresholds before a transfer build.

## Twelve programs, 360 new claims

Each program has one public record input containing four M31 words and one
public record result of the same shape. `N` is the number of live chip calls,
not the number of rows or the number of field operations. Calls use the
square-then-add chip; the current mixed profile admits at most eight calls.

| Shape, N=2/4/6 | Program sketch | What changes |
| --- | --- | --- |
| `control` | `r[i] = repeat16(r[i-1]^2 + (13+i)); result = r[N-1] + x` | Fresh witness/claim and package on the new stack; same relation shape as v1 |
| `feeder` | Before each repeat, `v = (v + 5+i) * (3+i)` | Constrained circuit arithmetic feeds every chip input |
| `fork` | Each distinct `r[i] = repeat16(x^2 + 13+i)`, then add all outputs | Independent chip calls and a larger combining circuit |
| `deep32` | Dependent `repeat32` calls | Twice the chip rounds at the same call count |

The hand evaluator computes the four output words independently of S31's
relation oracle for every generated claim. The oracle must agree. Sources,
assignments, and typed statements are all distinct within this cohort and
from **both** committed v1 train and held-out inventories. Only the old
protocol's hashes are read for that disjointness check; old held-out
observations are not read. The new assignment seed is `2026101127`; there are
30 unique assignments per program. A predeclared SHA-256 order interleaves all
12 programs at each assignment index; the native audit checks that the saved
process endpoints follow this order without overlap. The source generator and
full deterministic inventory are in [cohort.py](../../../src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py).

The new compiler revision may differ from the v1 model's compiler revision.
The fresh `control` programs measure that stack shift, so shape error can be
read alongside the same-count control error. This design **does not isolate a
causal shape-only effect** if the compiler differs. A same-revision experiment
would require running both shapes on the exact older compiler, separately
frozen and audited. The engine gitlink, host, Zig executable, and tool bytes
are pinned in the transfer protocol. Host transfer is another study.

## Target, model, and gates

The target is one fresh source-embedded prover process plus one fresh external
native verifier process on the same typed public statement. Process startup,
engine setup and proof work are included. Package build and Python scheduling
are reported separately. The profiler's six package intervals, process
residual, and verifier wall retain the v1 definitions. Native setup and PoW
are still inside an opaque engine interval because no separate timers exist.

The only permitted predictor is the v1 **training** `model.json` with SHA-256
`92d4bc1847f7ad69b08c3405e84f7df7e69e9492f403fd7a6286d59c75e9e9f3`.
The [model freeze](language/mixed-stage-cost-v1-model-freeze.json) predates the
v1 held-out phase. Its fit and empirical bands are applied unchanged to each
new N. The `deep32` shape deliberately tests a missing feature: v1 sees call
count but not rounds. Failure is informative and must be published without
retuning on this transfer cohort. Any later round-aware estimator needs a
new prospective split and model version.

The [design JSON](language/mixed-stage-cost-transfer-v1-prospective.json) fixes
all gates. All 12 sources and 360 native-verified trials are required. The
control three-program p90 median relative error must be ≤25% for first
verified wall and ≤10% for proof bytes. The nine transfer programs' p90 must
be ≤30% and ≤15%, respectively. Every shape must have ≥75% trial coverage for
wall and ≥80% for proof bytes under the *unchanged v1* intervals. Across all
programs, the median interval upper bound divided by observed median must be
≤8× for wall and ≤1.5× for proof bytes. A failing gate remains a result.
These are diagnostic gates, not permission for automatic lowering or a
general cost guarantee.

## Freeze and native run order

Commands below are from the S31 repository root. The protocol is generated
**only after** the design and tooling are committed on the exact revision
that will build packages. The Git source commit, complete Python tool set,
compiler fingerprint, record template, reference model/protocol hashes,
resolved Zig executable bytes, host identity, engine gitlink, cohort bytes,
build mode, and gates are then written to a candidate JSON. The transfer
collector refuses native work until that candidate and a separate UTC freeze
anchor are committed, with the full hash and anchor commit externally recorded.

```sh
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/test_static.py
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py preview
# Commit reviewed design and tools on a clean stack, then:
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/protocol.py draft
```

Commit the generated `language/mixed-stage-cost-transfer-v1-protocol.json`.
Create and commit `language/mixed-stage-cost-transfer-v1-freeze.json` with
`schema: s31-mixed-stage-cost-transfer-v1-freeze`, the exact
`protocol_sha256`, and `recorded_at_utc` in UTC. Record its full commit ID and
protocol hash externally before the first timed build. The anchor must descend
from the source commit. Do not edit this protocol in place. Use a new version
if a source, tool, host, or gate must change. Keep the timed run in a dedicated
worktree at this frozen revision; ongoing S31 development in another worktree
must not alter its compiler or collector bytes.

Use a fresh ignored path such as `zig-out/s31-mixed-stage-transfer-v1-YYYYMMDD`
for raw evidence. The `build` and `prove` commands need `--out`, `--expected-protocol-sha256`,
and `--protocol-anchor-commit` (the full recorded values). `build` starts at a
fresh path, materializes exact source/assignment/statement bytes, builds each
ReleaseFast source-embedded package once, and records monotonic build
endpoints, logs, inspector identity, and binary hashes. `prove` checks all
builds, runs every prover and external verifier, saves proofs and stage logs,
then writes a `phase-root.json` over every raw evidence file. A failed or
partial phase must be restarted at a new path. Neither command resumes.

After the phase finishes, commit and externally record
`language/mixed-stage-cost-transfer-v1-phase-anchor.json` with schema
`s31-mixed-stage-cost-transfer-v1-phase-anchor`, the protocol hash, full
`phase-root.json` SHA-256, and UTC `recorded_at_utc`. It must descend from the
freeze anchor. Only then run `study.py audit` with the three build/prove
arguments plus `--expected-phase-root-sha256` and `--phase-anchor-commit`.
The audit regenerates all 360 claims, checks raw file roots, package binaries,
manifest digests, build/process intervals, and stage lines, then replays every
proof with the source-embedded native verifier. It requires rejection of a
changed public input and a changed public result for **each** proof. Only a
complete audit writes `corpus.json` and `audit.json`.

`score.py score` additionally needs `--model` pointing to the frozen
training-only `model.json` and the same protocol/phase arguments. It checks
the exact model hash against the old committed model freeze, scores the
audited 12-program corpus without refitting, and writes one `evaluation.json`.
The raw corpus and audit must be retained. Commit
`language/mixed-stage-cost-transfer-v1-report-anchor.json` with schema
`s31-mixed-stage-cost-transfer-v1-report-anchor`, the protocol hash, phase
root hash, phase anchor commit, reference training model hash, exact SHA-256
of `audit.json`, `corpus.json`, and `evaluation.json`, and UTC time. Externally
record its full commit ID, then run `score.py report-check` with all scoring
arguments plus `--report-anchor-commit`. It replays every native proof and
both changed claims again, checks the raw phase and committed report hashes,
and recomputes the evaluation from the frozen model. Publish pass **or** fail
only after this seal passes. The old v1 raw corpus must not be copied into the
new phase or used for interval calibration.

The protocol keeps the v1 guard of **12 GiB free at phase start and 8 GiB
before every build, proof, and audit replay** across the evidence, Zig cache,
and temporary filesystems. This may require clearing reproducible compiler
caches while retaining all old raw evidence. Use an otherwise quiet host.
The pinned collector and host monotonic clock remain timing assumptions;
the source-embedded native verifier and STARK/PCS review remain proof
assumptions. No transfer accuracy or whole-workflow speedup is established by
this design alone.
