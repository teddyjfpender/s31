# Mixed-general whole-prover cost model v1: prospective protocol

Status: **design and tooling only; no new timed training or held-out corpus**.
The completed [paired record v2 study](PAIRED_RECORD_V2_RESULT.md) and the
single-witness [N3/N8 stage smoke](MIXED_STAGE_DIAGNOSTIC_V1.md) motivated
the stage boundary. Their source hashes, assignments, wall times, ratios, and
proof lengths are excluded from fitting, interval calibration, and evaluation.
The proposed protocol must be committed, reviewed, and externally timestamped
before a new native phase. A local gate pass would apply only to the pinned
record ABI v2, 16-round repeat-chain source family, host, compiler, engine,
security profile, and build mode. It would not establish transfer to another
source shape or host, equal soundness against `direct-gate`, or a speedup.

## What is predicted

The target is **first verified process wall** for the source-embedded
`direct-mixed-general` package: one fresh prover process followed by one fresh
source-embedded native verifier process on the same canonical typed public
record statement. Process startup, native setup, FRI, interaction PoW and
verification are inside that target. Python orchestration, the gap between
processes, package compilation, independent oracle work, and untimed native
audit replays are outside it. The report discloses the observed package build
time and observed `build + first verified proof` and `build/100 + first verified
proof` costs separately. Build wall is not predicted from four training
sources, and these accounting sums are not a source-to-proof timing experiment.

The complete target partitions into six disjoint internal package intervals,
the measured prover process residual (`prover wall − package total`), and the
external verifier process wall. The residual includes source/assignment CLI
work, process startup and teardown, file I/O, scheduling and timer overhead;
it is not labelled native setup. `native_prove_including_setup_ns` remains an
opaque engine interval. Engine setup/preprocessing and PoW are explicitly
`null` because no separate mixed native timer measures them.

| Predeclared component | Feature used for the point fit |
| --- | --- |
| Profile rebuild, semantic evaluation, topology compile, witness compile | Number of live 16-round calls, N |
| Opaque native prove including setup, envelope and serialization | N |
| Prover process residual, external verifier process wall | Constant |
| Proof bytes | N |

Each N-dependent component uses nonnegative affine least squares on **four
per-source medians**; a constant component uses the pooled median of those
medians. The four training call counts are N=1,3,5,7. The distinct held-out
counts are N=2,4,6,8. There are 100 fresh, deterministic assignments per
count and distinct source names `mixed_stage_cost_v1_nN`, generated from the
record v2 template. The deterministic inventory has eight source hashes and
800 unique assignment and typed-statement hashes; its preview SHA-256 is
`08725ff480e6bfbd272fb8afe3d415b15d21abe9a62939716ed7e85644a56250`.
Source geometry is the same general family as the older paired study, so the
held-out count set is **prospective for the new runtime**, not an unseen
relation-family validation. The prior held-out N values were already public.

For an empirical trial interval, omit each whole training source in turn,
refit on the other three, and collect the 100 observed/predicted target ratios
for that omitted source. The 5th and 95th percentiles across the 400
leave-one-source-out ratios, expanded to include 1, multiply the final
training fit's target prediction. This interval is a diagnostic for this host,
not a confidence interval or a tail guarantee. Summing independent stage
interval bounds is avoided; the whole-wall interval is calibrated on the
complete observed wall target, preserving correlated process variation.

## Predeclared local gates

The [prospective JSON](language/mixed-stage-cost-v1-prospective.json) is the
source of these exact values; changing a gate requires a new version and a new
corpus. All four held-out programs and 400 verified trials are required.

| Metric | Pass condition |
| --- | ---: |
| First-verified wall, p90 relative error across four program medians | ≤ 25% |
| First-verified wall, maximum program-median relative error | ≤ 35% |
| First-verified wall, trial interval coverage | ≥ 80% |
| First-verified wall, median interval upper / observed median | ≤ 8× |
| Proof bytes, p90 relative error across four program medians | ≤ 10% |
| Proof bytes, trial interval coverage | ≥ 80% |
| Proof bytes, median interval upper / observed median | ≤ 1.5× |
| Opaque native prove, p90 program-median relative error | ≤ 30% |

The gate can fail. If it does, publish the failure against the frozen protocol;
do not retune on the held-out corpus. The `local_accuracy_gate_pass` flag is
never an automatic lowering choice. Package build cost and peak RSS have no
predictive pass gate in this version; they must be reported as measured
quantities or marked unavailable. The model is not yet a reliable general
whole-prover predictor until source-shape and host transfer pass separately.

## Freeze, collection, and audit order

1. Commit the design, model, collector, stage diagnostic, and tests. On that
   clean S31 revision with the exact pinned `deps/stwo-zig` gitlink, run
   `python3 src/frontends/s31/benchmarks/mixed_stage_cost_v1/protocol.py draft`.
   The generated protocol binds the design/template bytes, generated inventory,
   compiler fingerprint, resolved Zig executable hash, engine commit, tool hashes, host, split, features,
   estimator, gates, and 12 GiB/8 GiB disk guards. It is a **candidate**, not
   permission to measure. Commit it, then commit
   `language/mixed-stage-cost-v1-freeze.json` with schema
   `s31-mixed-stage-cost-v1-freeze`, the full protocol SHA-256 and UTC
   `recorded_at_utc`. Externally record the full protocol hash and anchor
   commit before any timed build. The native commands require both values and
   recheck exact source/tool/compiler/engine/host identity.
2. Run the `study.py build --split train` phase at a fresh evidence path, then
   `study.py prove --split train` there. The builder uses the same ReleaseFast
   mixed source-embedded install for each of four source hashes and records
   monotonic build endpoints, command, raw logs, inspector identity and binary
   hashes. The prover collector saves every proof, canonical statement, raw
   logs, manifest and stage report. It records monotonic prover/verifier
   endpoints and first-verified wall from their two differences. It writes an
   immutable `phase-root.json` over every raw evidence file when all 400
   proofs pass their external native verifiers. A failed or partial phase
   must be restarted at a new path.
3. Commit and externally timestamp
   `language/mixed-stage-cost-v1-train-phase-anchor.json` with schema
   `s31-mixed-stage-cost-v1-phase-anchor`, split `train`, full protocol hash,
   full `phase-root.json` SHA-256 and UTC time. `study.py audit --split train`
   checks the anchored raw root, regenerates every source, assignment and
   typed statement, reconstructs all wall times and package partitions from
   saved raw endpoints/stage logs, checks the inspector and binary hashes,
   and reruns the native verifier on every proof plus changed public input
   and changed public result. It writes an audited corpus only after all
   controls pass.
4. `study.py fit` consumes only that anchored audited train corpus. It writes
   `model.json` once. Commit and externally timestamp
   `language/mixed-stage-cost-v1-model-freeze.json` with schema
   `s31-mixed-stage-cost-v1-model-freeze`, the full protocol/train phase and
   phase-anchor identities, exact train audit/corpus/model hashes, and UTC
   time. The held-out commands recompute the training fit and require this
   model anchor to descend from the train phase anchor. The full model hash
   and anchor commit must be independently recorded **before** the first
   held-out build.
5. Build, prove and audit the four held-out counts at a **new** path, with
   the frozen train admission bound into the held-out phase root. Commit and
   externally timestamp its phase-root anchor before audit. Run
   `study.py evaluate` once with the full held-out phase-root hash and its
   committed anchor; it checks every frozen identity and reports all
   eight gates and per-program observed build accounting. Anchor the held-out
   audit/corpus/evaluation hashes before publishing a result. The committed
   `language/mixed-stage-cost-v1-heldout-report-anchor.json` uses schema
   `s31-mixed-stage-cost-v1-heldout-report-anchor`, split `heldout`, full
   protocol and phase-root hashes, phase-anchor commit, full model hash and
   model-anchor commit, SHA-256 of each of `audit.json`, `corpus.json`, and
   `evaluation.json`, and UTC `recorded_at_utc`. Commit it after evaluation,
   externally record its full commit ID, and run `study.py report-check` with
   all freeze, train-model, held-out-phase and report-anchor arguments. This
   command checks the committed chronology and exact report bytes and
   independently recomputes the evaluation from the frozen model and audited
   corpus. Never pool the prior paired study's N3/N5/N7/N8 results into this
   fit or interval.

Both phase starts require at least **12 GiB** free on the evidence, Zig local
and global cache, and temporary filesystems. Every build, proof, and native
audit replay checks at least **8 GiB** free on each distinct filesystem. The
retained paired study suggests about 100–200 MiB of mixed-only raw evidence
and roughly 48 MiB of eight installed bundles. Zig cache growth may take
several GiB; the disk guard aborts rather than claiming a partial phase.
Runs need an otherwise quiet host. A committed timestamp proves what bytes
were declared and when, while process durations still trust the pinned
collector and host monotonic clock. The source-embedded native verifier and
its proof-system review remain the proof authority.

Native-free checks:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_v1/cohort.py
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_v1/test_static.py
python3 -B src/frontends/s31/benchmarks/paired_record_v2/test_diagnose_stages_v1.py
```
