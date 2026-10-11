# V8r1 baseline whole-prover runbook

Status: **completed with a post-freeze evaluator roster repair; qualified local
accuracy gate passed**. The frozen protocol was externally recorded before
native work, and the training-only model was externally recorded before any
held-out build. The original frozen held-out evaluator failed before producing
an accuracy result because its inherited V3 roster expected four quotient
names where the pinned V8r1 inventory specified div/rem. The separately
versioned, reviewed roster-only bridge then produced a passing held-out
evaluation, independent gate, native publisher, and relocated native replay.
This is a **post-freeze repaired result**, not an unqualified prospective V8r1
result. The frozen model, gates, protocol, and raw trial evidence were not
changed. See [the result and evidence record](WHOLE_PROVER_V8R1_RESULT.md).

V8r1
repairs the frozen V8 training fit gate. The V8 protocol called the 128-bit
fixed-width choice `signed_128_result`; its inherited V3 roster checker read
`signed_128_output`. V8 built 23 clean training packages and verified 2,300
training proofs, but the fit failed before creating a model. It produced no
held-out native observation. The exact failure and preserved evidence hashes
are in [the V8 fit-failure record](language/whole-prover-cost-v8-fit-failure.json).
V8 timings and proof measurements are excluded from V8r1 fitting and
calibration. V8r1 keeps the previously declared error gates and 2 MiB RSS
uncertainty floor; it changes only the versioned tool contract, source names,
and assignment seeds. The train and held-out rosters remain disjoint by
source and assignment bytes. No mixed-versus-generic speed claim is included.

## Before native work

Use an isolated clean S31 worktree with the exact committed engine gitlink.
The [V8r1 prospective design](language/whole-prover-cost-v8r1-prospective.json)
fixes train and held-out menus, gates, disclosure, and a train-only fitter.
The V8r1 adapter projects `signed_128_result` into the V3 checker's
`signed_128_output` spelling only in a temporary checker view. The corpus
must separately match every name and digest in the frozen inventory. A
synthetic 23-case fit test exercises the complete roster before freeze.

Check at least 8 GiB free before each native phase. Run the static checks and
inventory preview, then freeze only after all compiler, engine, benchmark,
frontend, and design sources are committed. The draft pins the source base,
engine gitlink, compiler fingerprint, complete transitive Python tool digest,
host, FRI/PoW settings, 43 source digests, 4,300 assignment digests, gates,
and algorithm. The old V8 protocol and failure record are pinned disclosures.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest \
  src.frontends.s31.tests.python.test_cost_v8r1_design \
  src.frontends.s31.tests.python.test_cost_v8r1_pipeline
PYTHONDONTWRITEBYTECODE=1 python3 src/frontends/s31/benchmarks/cost/v8r1_design.py \
  --check-inventory zig-out/s31-v8r1-preview
python3 src/frontends/s31/benchmarks/cost/v8r1_protocol.py draft \
  --out zig-out/s31-v8r1-freeze-inputs
git add design/s31/measurements/language/whole-prover-cost-v8r1.json
git commit -m 'Freeze prospective S31 V8r1 baseline protocol'
python3 src/frontends/s31/benchmarks/cost/v8r1_protocol.py anchor protocol
git add design/s31/measurements/language/whole-prover-cost-v8r1-protocol-freeze.json
git commit -m 'Anchor prospective S31 V8r1 baseline protocol'
```

An independent, externally timestamped record of the **full** protocol
SHA-256 and full anchor commit must precede the first V8r1 native package
build. A Git commit alone does not establish this chronology. Keep all raw
packages, assignments, proofs, trial records, and corpus files. Do not reuse
or edit V8 evidence. Native measurements must have an exclusive machine slot.

## Train, fit, and anchor

Use a fresh `zig-out/s31-v8r1-evidence/train` path. The build phase packages
all 23 training programs; the prove phase makes 100 fresh prover and native
verifier process trials per program. The collector refuses missing or changed
protocol and source pins. Replace angle-bracket placeholders with the
externally recorded full values.

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8r1.py \
  --split train --phase build --out zig-out/s31-v8r1-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8r1.py \
  --split train --phase prove --out zig-out/s31-v8r1-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v8r1.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  fit zig-out/s31-v8r1-evidence/train/whole-prover-corpus.json \
  --out design/s31/measurements/language/whole-prover-cost-v8r1-model.json
git add design/s31/measurements/language/whole-prover-cost-v8r1-model.json
git commit -m 'Freeze training-only S31 V8r1 baseline model'
python3 src/frontends/s31/benchmarks/cost/v8r1_protocol.py anchor model \
  --model design/s31/measurements/language/whole-prover-cost-v8r1-model.json
git add design/s31/measurements/language/whole-prover-cost-v8r1-model-freeze.json
git commit -m 'Anchor training-only S31 V8r1 baseline model'
```

Stop before building any held-out package. Externally record the full model
SHA-256 and full model-anchor commit, and separately authorize the held-out
phase. The model uses the V8r1 training corpus only. A fit failure is a failed
study gate; do not change tools under the same protocol or use V8 evidence to
repair a model.

## Held-out, audit, and portable replay

After the model anchor is externally timestamped, build and prove the fresh
held-out split. Then evaluate the committed model and run the independent
publisher with both native verification and the accuracy gate required:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8r1.py \
  --split validation --phase build --out zig-out/s31-v8r1-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v8r1-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8r1.py \
  --split validation --phase prove --out zig-out/s31-v8r1-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v8r1-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v8r1.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  evaluate design/s31/measurements/language/whole-prover-cost-v8r1-model.json \
  zig-out/s31-v8r1-evidence/validation/whole-prover-corpus.json \
  --out zig-out/s31-v8r1-evidence/validation/evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v8r1.py \
  zig-out/s31-v8r1-evidence/train/whole-prover-corpus.json \
  design/s31/measurements/language/whole-prover-cost-v8r1-model.json \
  zig-out/s31-v8r1-evidence/validation/whole-prover-corpus.json \
  zig-out/s31-v8r1-evidence/validation/evaluation.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native --require-pass \
  --out zig-out/s31-v8r1-evidence/validation/audit.json
```

The publisher refits from the saved training corpus, recomputes the held-out
prediction and gate with an independent implementation, checks source and
assignment hashes and value-oracle results, and reruns native verifiers on
the saved original and changed public claims. `--require-pass` requires
`--native`. Preserve failed evaluations too: if the accuracy gate fails,
rerun the publisher with `--native` and without `--require-pass`; report the
failure and retain the audit. Never refit or adjust an interval from held-out
observations.

Create a relative content-addressed manifest over the raw evidence and
externally record its **full** SHA before moving the directory. Replay at a
distinct path with native verification:

```sh
python3 src/frontends/s31/benchmarks/cost/portable_v8r1.py create \
  --root zig-out/s31-v8r1-evidence \
  --protocol-sha256 <full-protocol-sha256> \
  --model-sha256 <full-model-sha256>
python3 src/frontends/s31/benchmarks/cost/replay_portable_v8r1.py \
  --root <moved-evidence-directory> \
  --expected-manifest-sha256 <full-portable-manifest-sha256> \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native --require-pass
```

If the accuracy gate failed, replay with `--native` and without
`--require-pass`; keep the failed gate separate from artifact integrity.
The result is limited to the pinned compiler, engine, host, source corpus,
and toolchain. Automatic lowering stays disabled.
