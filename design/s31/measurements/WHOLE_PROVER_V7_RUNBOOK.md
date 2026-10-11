# V7r1 prospective whole-prover cost study

Status: **V7r1 completed; the predeclared local accuracy gate failed**. The
saved artifacts and native verifier controls passed independent replay.
Automatic lowering remains disabled. The first V7 protocol was anchored at
`5bb640ac69c74e5adae02e55735232ea8b7a0689`, then stopped after four
training package builds and an interrupted fifth build. It produced no
proofs, model, or validation artifacts. Its protocol and anchor remain in
the repository as the superseded attempt. V7r1 uses distinct protocol,
model, anchor, and evidence paths. It records that earlier exposure, retains
the predeclared workloads and gates, and restarts measurements from zero.

The V6 model failed the changed-stack [transfer diagnostic](WHOLE_PROVER_TRANSFER_V1.md).
Do not use V6 wall predictions to choose current S31 lowerings. This runbook
implements the [V7 design](WHOLE_PROVER_V7_PLAN.md) without changing V6 files.

## Recorded run and outcome

The V7r1 protocol was anchored at commit
`16da6a3981ac8d9ff237c4555114d1cbb3f25f77` with SHA-256
`94b1bd57a49c3fdbd7ef8931ba21b3452efdfd5573693796a57035aeb3f7a891`.
Its full hash and anchor commit were externally recorded at
2026-10-11 03:31:52 UTC before the first native build. The training-only model
was anchored at commit `a807e5210f21611a31ed03f4a9b3e0ad04a77be2` with
SHA-256 `461994df2b47d8c7d2a5358c7918f25cb6973f4110f433328a5d789e2bc65593`.
Both identifiers were externally recorded at 2026-10-11 04:03:57 UTC before
the first held-out build.

The training and held-out corpora each contain 20 fresh packages and 2,000
distinct trials, five programs per family. Their SHA-256 digests are
`9a600ff137d844350ef8121fb6812dfbcc14555a9da5983755cd8b600f067856`
and `7617f4dcbcc901620de286e0751e5f6d4702707ba802e3eb64c353ed6a5ac3a1`.
The saved held-out evaluation has SHA-256
`459e9c86fe67052d8713001ff2558f5e6986451cecd6d0c0c626c7e47d343660`.
The committed [pinned audit](language/whole-prover-cost-v7r1-audit.json) has
SHA-256 `9b871ec1618128c8d10f74d60fad46150d62ade58164aab7a2b88eb388e175a6`.

The predeclared gate **failed**: chip-family prover RSS interval coverage was
75.2% against the 80% minimum. Individual RSS interval coverage was 0% for
`chip_8192` and 3% for `hash_13`, both below the 70% per-program minimum.
All wall-time, proof-byte, and process-stage gates passed. The native publisher
confirmed all 4,000 saved proofs and changed claims, and its independent
second implementation reproduced the failed gate. A content-addressed copy
was replayed at a different path with native verification: 28,466 files,
4,000 proofs, and 8,000 original/changed verifier controls passed. The
portable manifest SHA-256 is
`f087ea2dba1175bfe973fd0d7f0f74169d69f1554b29a80c85014424c375dbed`;
it was externally recorded before relocation. The raw evidence remains under
`zig-out/s31-v7r1-evidence/` and is not part of this Git commit.
Because the accuracy gate had already failed, the native publisher and
relocated replay were run with `--native` and without `--require-pass`; both
exited successfully after auditing artifacts and independently confirming
`local_accuracy_gate_pass=false`. The release-gate commands below retain
`--require-pass` and therefore exit nonzero on this frozen result.

This result is specific to source base commit
`264e0f77a6806f9276327caea5108a1b95a07ad0`, compiler fingerprint
`d43ede036820a67281925d89d64b1bf8200da636f83d9a2a4b0a6390fc505edf`,
measurement-tool digest
`8691897011496b0228e300ef396fb98db75700372f75f8bd4c6b81049624df1d`,
engine commit `2a0960dd8b57c6bff5c10ea241bd559e15cd95b9`, and the recorded
Apple M5 Max host (macOS 26.7.1, Python 3.14.6, Zig 0.15.2). The small RSS
point errors alongside under-covering intervals are a diagnostic for a new,
separately frozen study. They do not license changing this model or rescoring
these held-out trials.

## What V7r1 predicts

For one pinned host, compiler, engine, and proof profile, V7r1 predicts the mean
of a fresh prover process plus a fresh native verifier process. It also
predicts proof bytes and prover peak RSS. Package build time is recorded
separately. Every program uses 100 distinct assignments and the same 26-bit
proof of work. Native interaction and FRI PoW timers are kept separately when
available. Each trial saves the outer process wall, native runtime stages, and
their difference. The validation gate checks both process stages for **each
program**, in addition to family-wide target accuracy.

The frozen workload definition contains five training and five held-out
programs per family: direct-gate arithmetic, direct chip, gate hash, and
fixed-width arithmetic. The resulting 40 programs and 4,000 assignments are
digest-disjoint from each other, V6, and the V6 transfer diagnostic. Direct
chip powers of two and fixed-width division forms can repeat earlier shapes;
the study does not claim shape novelty. Fixed N=3 mixed proof support exists;
it enters this cost study after a packaged CLI lowering and a representative
mixed workload/profile are specified and reviewed.

## Freeze in this order

First commit the V7r1 tooling on the final S31 and engine gitlink revisions and
initialize that exact clean engine checkout. `draft` refuses uncommitted
benchmark/frontend sources and refuses an unclean or wrong engine checkout.
It generates both splits and writes the one-time protocol. The tool inventory
is every `*.py` under `src/frontends/s31/benchmarks/` and
`src/frontends/s31/python/`, including transitive predictors and both
independent value oracles.

```sh
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py draft \
  --out zig-out/s31-v7r1-freeze-inputs
git add design/s31/measurements/language/whole-prover-cost-v7r1.json
git commit -m 'Freeze prospective S31 V7r1 protocol'
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py anchor protocol
git add design/s31/measurements/language/whole-prover-cost-v7r1-protocol-freeze.json
git commit -m 'Anchor prospective S31 V7r1 protocol'
```

**Before the first native build**, record the full protocol SHA-256 printed by
`draft` and the full protocol-anchor commit SHA in an independently timestamped
external record. Pass those exact values on every following command. A Git
commit and its own timestamp alone do not establish independent chronology.
The collector checks committed anchor bytes, ancestor order, current source
and compiler fingerprints, host identity, engine gitlink, workload inventory,
profile, FRI settings, and predeclared gates. A draft JSON or CLI-supplied
hash alone cannot unlock a native phase.

Build and prove the training split in separate steps, using one output
directory for both:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split train --phase build --out zig-out/s31-v7r1-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split train --phase prove --out zig-out/s31-v7r1-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v7.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  fit zig-out/s31-v7r1-evidence/train/whole-prover-corpus.json \
  --out design/s31/measurements/language/whole-prover-cost-v7r1-model.json
git add design/s31/measurements/language/whole-prover-cost-v7r1-model.json
git commit -m 'Freeze training-only S31 V7r1 model'
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py anchor model \
  --model design/s31/measurements/language/whole-prover-cost-v7r1-model.json
git add design/s31/measurements/language/whole-prover-cost-v7r1-model-freeze.json
git commit -m 'Anchor training-only S31 V7r1 model'
```

**Before the first held-out package build**, externally record the full
serialized model SHA-256 and full model-anchor commit SHA. The model anchor
must descend the protocol anchor. The V7r1 predictor fits coefficients and
empirical intervals only from the training corpus; the held-out sources,
assignments, and gates were fixed in the earlier protocol.

Then build, prove, evaluate, and replay the held-out split:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split validation --phase build --out zig-out/s31-v7r1-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v7r1-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split validation --phase prove --out zig-out/s31-v7r1-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v7r1-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v7.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  evaluate design/s31/measurements/language/whole-prover-cost-v7r1-model.json \
  zig-out/s31-v7r1-evidence/validation/whole-prover-corpus.json \
  --out zig-out/s31-v7r1-evidence/validation/evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v7.py \
  zig-out/s31-v7r1-evidence/train/whole-prover-corpus.json \
  design/s31/measurements/language/whole-prover-cost-v7r1-model.json \
  zig-out/s31-v7r1-evidence/validation/whole-prover-corpus.json \
  zig-out/s31-v7r1-evidence/validation/evaluation.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native \
  --require-pass \
  --out zig-out/s31-v7r1-evidence/validation/audit.json
```

The publisher reads package manifests, saved proof hashes, trial reports,
assignments, public statements, component manifests, both independent value
oracles, anchors, and the frozen model. It refits training and reevaluates the
held-out gate without rebuilding packages or altering evidence. `--native`
additionally reruns each saved original and changed public statement against
its native verifier. Raw package, proof, source, and assignment directories
must be retained beside the corpus files for replay. The ordinary publisher
expects the original absolute paths. To move evidence between directories,
create the relative, content-addressed manifest below, record its full SHA
externally, and move the entire `s31-v7r1-evidence/` directory. Portable replay
resolves every artifact relative to the new root, verifies its hash, and
treats absolute path strings in historical reports as provenance hints. It
still requires the pinned source checkout and committed freeze anchors;
native replay also requires compatible saved verifier binaries.

```sh
python3 src/frontends/s31/benchmarks/cost/portable_v7.py create \
  --root zig-out/s31-v7r1-evidence \
  --protocol-sha256 <full-protocol-sha256> \
  --model-sha256 <full-model-sha256>
python3 src/frontends/s31/benchmarks/cost/replay_portable_v7.py \
  --root <moved-evidence-directory> \
  --expected-manifest-sha256 <full-portable-manifest-sha256> \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native \
  --require-pass
```

`--native` on the portable replay reruns original and changed statements.
Both release commands require it when `--require-pass` is set, and the audit
checks that the changed claim is a canonical ABI value produced by the
declared one-word mutation. The
manifest lists all files under `train/` and `validation/`, including packages
and proofs, and rejects missing files, extra files, path traversal, and
symlinks. These portable tools are included in the frozen V7r1 tool digest;
they do not change the frozen V6 inventory. The separate
`independent_v7_gate.py` recomputes held-out predictions and every gate from
the serialized model and raw trials without importing the fitting predictor.
The publisher and portable replay exit successfully by default when the
evidence is internally consistent, even if `local_accuracy_gate_pass` is
`false`. On this run, `--require-pass` exits nonzero because the frozen
accuracy gate failed; use `--native` without it to audit the preserved proof
artifacts. The fitted features (`raw`, `padded`,
`preprocessed_cells`, profile, and visible FRI settings) must also match each
package's sealed cost report.

## Acceptance and limits

The predeclared V6 minimum gates remain: five programs per family, 100 trials
per program, wall p90 program mean error at most 25% and empirical coverage at
least 80%, proof byte and RSS p90 program median error at most 10% and coverage
at least 80%, plus the existing RSS per-program bounds. For each program the
prover's unattributed process time and native verifier process time must each
have either at most 25% relative mean error **or** at most 20 ms absolute mean
error. This tolerance is fixed before native observations; it is not tuned on
held-out results. The 26-bit PoW contributes random variation, so empirical
intervals do not promise tail coverage.

Even a passing V7r1 local gate does not establish cross-host or future-revision
transfer, compiler soundness, or soundness-equivalent lowering selection.
Automatic lowering remains disabled pending paired measurements and verifier
equivalence review.
