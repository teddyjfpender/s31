# V8 baseline whole-prover runbook

Status: **executable tooling, unfrozen protocol, no native V8 observations**.
The [prospective design](WHOLE_PROVER_V8_PROTOCOL.md) discloses V7r1's failed
RSS coverage, the training-only V8 interval rule, fresh split menus, and the
conditional authenticated mixed comparison. The commands here run only the
four baseline families. The paired mixed/generic experiment is explicitly
excluded by this protocol implementation until its general profile, packaged
CLI lowering, paired runner, and independent controls are admitted. There is
no mixed speed claim and automatic lowering stays disabled.

## Prepare and freeze

Run after the S31 compiler, engine gitlink, measurement Python and host are
settled. The exact source tree and engine checkout must be clean. `draft`
checks that all compiler-fingerprinted Zig/Zon files and transitive benchmark
and frontend Python files are committed, checks historical protocol/audit
digests, and generates both complete source/assignment inventories. The
preview design is deliberately not an executable protocol. Do not edit the
design, tooling, or source after the freeze; changes require a new study
revision.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 src/frontends/s31/benchmarks/cost/v8_design.py \
  --check-inventory zig-out/s31-v8-preview
python3 src/frontends/s31/benchmarks/cost/v8_protocol.py draft \
  --out zig-out/s31-v8-freeze-inputs
git add design/s31/measurements/language/whole-prover-cost-v8.json
git commit -m 'Freeze prospective S31 V8 baseline protocol'
python3 src/frontends/s31/benchmarks/cost/v8_protocol.py anchor protocol
git add design/s31/measurements/language/whole-prover-cost-v8-protocol-freeze.json
git commit -m 'Anchor prospective S31 V8 baseline protocol'
```

Record the **full** protocol SHA-256 and full anchor commit in an independent
timestamped external record **before** the first native package build. The
program then requires those values on every native phase. Merely committing
the anchor is not independent chronology. Use distinct `zig-out/s31-v8-evidence`
paths; never reuse V7 evidence. Maintain at least 8 GiB free before each
native phase and preserve all raw packages, proofs, assignments, trial reports,
and corpus files.

## Train, fit, and anchor the model

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8.py \
  --split train --phase build --out zig-out/s31-v8-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8.py \
  --split train --phase prove --out zig-out/s31-v8-evidence/train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v8.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  fit zig-out/s31-v8-evidence/train/whole-prover-corpus.json \
  --out design/s31/measurements/language/whole-prover-cost-v8-model.json
git add design/s31/measurements/language/whole-prover-cost-v8-model.json
git commit -m 'Freeze training-only S31 V8 baseline model'
python3 src/frontends/s31/benchmarks/cost/v8_protocol.py anchor model \
  --model design/s31/measurements/language/whole-prover-cost-v8-model.json
git add design/s31/measurements/language/whole-prover-cost-v8-model-freeze.json
git commit -m 'Anchor training-only S31 V8 baseline model'
```

The fitter reads the training corpus only. It checks sealed package cost
geometry before fitting and stores the exact V8 uncertainty method and fixed
2 MiB floor in the model. After the model anchor commit, independently
timestamp the **full** serialized model SHA-256 and full model-anchor commit
**before** the first held-out package build. Validation refuses an unanchored
model or one from another compiler, host, tool digest, or protocol.

## Held-out evaluation and evidence replay

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8.py \
  --split validation --phase build --out zig-out/s31-v8-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v8-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v8.py \
  --split validation --phase prove --out zig-out/s31-v8-evidence/validation \
  --model design/s31/measurements/language/whole-prover-cost-v8-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v8.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  evaluate design/s31/measurements/language/whole-prover-cost-v8-model.json \
  zig-out/s31-v8-evidence/validation/whole-prover-corpus.json \
  --out zig-out/s31-v8-evidence/validation/evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v8.py \
  zig-out/s31-v8-evidence/train/whole-prover-corpus.json \
  design/s31/measurements/language/whole-prover-cost-v8-model.json \
  zig-out/s31-v8-evidence/validation/whole-prover-corpus.json \
  zig-out/s31-v8-evidence/validation/evaluation.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native --require-pass \
  --out zig-out/s31-v8-evidence/validation/audit.json
```

The publisher independently refits training, reevaluates held-out cases,
recomputes every gate with a second implementation, checks package/source and
assignment hashes, value-oracle outputs, and canonical changed public claims.
`--native` reruns every saved original and changed statement with the saved
native verifier. `--require-pass` requires `--native`. A failed accuracy gate
still writes an audit; rerun **without** `--require-pass` and **with**
`--native` to preserve the failed result and artifact-integrity record. Never
refit or adjust an interval from held-out observations.

For relocation, create a relative content-addressed manifest over the raw
evidence, externally record its full SHA before moving the directory, then
verify at a different path with both native controls and the gate:

```sh
python3 src/frontends/s31/benchmarks/cost/portable_v8.py create \
  --root zig-out/s31-v8-evidence \
  --protocol-sha256 <full-protocol-sha256> \
  --model-sha256 <full-model-sha256>
python3 src/frontends/s31/benchmarks/cost/replay_portable_v8.py \
  --root <moved-evidence-directory> \
  --expected-manifest-sha256 <full-portable-manifest-sha256> \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --native --require-pass
```

If the accuracy gate failed, run portable replay with `--native` and without
`--require-pass` and report the failed gate separately. The portable manifest
rejects missing/extra files, changed bytes, symlinks, and traversal paths.
The replay still requires the pinned source checkout and its committed
anchors. A passing local gate alone does not establish cross-host transfer,
compiler correctness, or soundness-equivalent automatic lowering selection.
