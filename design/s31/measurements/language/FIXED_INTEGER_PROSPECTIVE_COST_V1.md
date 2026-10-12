# Prospective fixed-integer whole-prover cost v1

Status: **protocol and native-free checks implemented; no native measurements
collected under this protocol yet**. The historical V8r1 result used another
compiler fingerprint and does not calibrate this model. Current paired runs
are observations, not prospective predictions.

The protocol measures unsigned checked `std::int::add_checked` and
`std::int::mul_checked` under `direct-gate` and `sparse-wide-gate`, on the
same source and witness for each pair. Sources at u16 and u32 fit a small
stage model; u64 sources calibrate residual envelopes; u128 is the unseen
width within the same checked arithmetic source templates. Each source has
eight distinct witnesses. This costs 16
package builds and 128 measured prover/verifier pairs, plus 16 separate
warmup proofs. The multiplication runner also proves overflowing controls
must fail under both lowerings. The pair schedule alternates first position
by witness. The benchmark is deliberately narrow enough for one quiet-host
run; it does not extrapolate to chips, hash circuits, recursion, or another
machine.

## Freeze and run order

1. Finish compiler and benchmark edits. `plan` writes exact source and
   assignment hashes, the compiler fingerprint, engine gitlink, host and
   toolchain identity, oracle provenance, and benchmark script hashes. Commit
   or externally timestamp the plan SHA before collecting native data.
2. `collect-training` builds and measures the u16/u32 fit and u64 calibration
   programs only. It uses the existing paired runners, native proof controls,
   and saved artifacts. `fit` revalidates the raw paired evidence and writes
   `model.json` plus `model.sha256`; it refuses to run if either u128 result
   directory exists. Commit or externally timestamp the model SHA.
3. `collect-holdout` checks that sealed model against a fresh training-only
   refit. For each u128 source it writes `prebuild-prediction.json` using only
   the source width **before either package build starts**. After both builds,
   it reads the exact AIR geometry, writes `preproof-prediction.json`, and only
   then starts native warmup and measured proof processes. The latter is a
   prospective **post-layout proof** prediction, and its build estimate must
   match the earlier prebuild record. The callbacks enforce this order during
   an honest run and refuse to overwrite either prediction. An offline
   validator can check their values and hashes but cannot cryptographically
   establish local file chronology; commit or externally timestamp the
   prebuild and preproof hashes for stronger independent evidence.
4. `score` checks the preproof prediction against the model and built package,
   revalidates all native evidence, and scores all four u128 profiles without
   refitting. `validate` replays the artifact checks and recomputes any saved
   score. Missing or unusable native stage/RSS data fail closed.

Commands are in the [benchmark runbook](../../../../src/frontends/s31/benchmarks/fixed_integer_cost/README.md).

## Prediction and accounting

The paired native trial's measured whole wall is the **sum of one fresh
prover process and one fresh native verifier process**. A saved trial must
satisfy, within native timer rounding:

```text
whole wall = witness + cold native setup + prove excluding PoW
           + interaction PoW + FRI PoW + native other
           + (prover process wall - native runtime total)
           + external verifier process wall
```

Package build is a separate measured term. It is not added to first-proof
latency unless the caller explicitly needs build plus first proof. The
process residual includes startup, parsing, I/O, resource wrapper, and OS
scheduling; it is not silently labeled engine setup. RSS is a process peak,
not an additive stage.

Each operation/lowering combination fits separate nonnegative affine stage
centers from the u16 and u32 program medians. Inputs are chosen before
measurement: source width for build; raw QM31 rows for witness; preprocessed
cells for setup/RSS; padded rows times their base-2 logarithm for proving
and verification; padded rows for proof bytes; and the visible PoW search
space for interaction/FRI PoW. Constant fallback applies where a feature
does not vary. These are small descriptive regressions, not derived
complexity bounds. In particular, two training widths cannot reliably
identify a nonlinear compiler threshold at u128.

The PoW terms have their **own** point estimates and interval residuals.
The after-PoW diagnostic subtracts the *reported* PoW from the same measured
wall; it is not a proposed mode of running a proof. Transcript-dependent
PoW and host load still affect actual whole wall. Visible FRI equality does
not establish equal soundness of direct and sparse AIRs.

The u64 calibration sources determine empirical p05/p95 target ratios for
whole wall, after-PoW wall, proof bytes and prover RSS. Four independent
build observations use a doubled min/max envelope. Predeclared minimum
extrapolation bands are applied before u128: whole wall 0.5–2.0× center;
after-PoW 0.7–1.5×; proof bytes and RSS 0.8–1.25×. These are intentionally
wide local diagnostics, **not confidence intervals or tail guarantees**.
They cannot be narrowed after the holdout is observed.

## Predeclared score

All four u128 programs and all eight witnesses per program are mandatory.
The score reports each target's predicted center, band, observed median,
relative error, and trial coverage; it retains every miss. Local diagnostic
gates are: p90 program-median relative error at most 30% whole wall, 25%
after-PoW, 15% proof bytes, 20% RSS and 50% build; at least 75% trial
coverage for whole and after-PoW wall; whole upper/center at most 8× and
after-PoW upper/center at most 2×. A broad interval may pass coverage while
point estimates fail. A failed gate is a result, not an invitation to fit on
u128. No automatic lowering selection is enabled.

The native controls prove that these sampled statements were accepted and
their changed public claims rejected by the generated verifier. This study
does not establish general source-to-AIR correspondence or PCS/FRI
soundness. A successful local cost gate would justify only this pinned host,
compiler, engine, sources, and width extrapolation.
