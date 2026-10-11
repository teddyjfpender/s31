# V8 baseline whole-prover runbook

Status: **protocol frozen and externally timestamped; training paused before
any completed native V8 observation**.
The [prospective design](WHOLE_PROVER_V8_PROTOCOL.md) discloses V7r1's failed
RSS coverage, the training-only V8 interval rule, fresh split menus, and the
conditional authenticated mixed comparison. The commands here run only the
four baseline families. The paired mixed/generic experiment is explicitly
excluded by this protocol implementation until its general profile, packaged
CLI lowering, paired runner, and independent controls are admitted. There is
no mixed speed claim and automatic lowering stays disabled.

## Frozen protocol and interrupted pre-slot build

The V8 baseline protocol is frozen at source base
`b4d4270f28ab162e3ed0a17c4d6628ec24ee938f`, engine gitlink
`7d544c6839497ca19b6c7ef9b982e464f10cfeed`, compiler fingerprint
`290eaa667e96039b7a872f5b5566bff3d6c4d7a880bdf022bd38f7990ab72c9a`,
and measurement-tool digest
`9dd113abb35bad0ed25b7177c1db5152ece441d6280fb0301f72802361f5084e`.
The protocol SHA-256 is
`dff9ed804a9a5c50189f569adceae0ba68a25cebcfa4d98c899065f2ab769abd`;
the full anchor commit is `cdfe86cf7047a630c945cca7f8b8706295bc3623`.
Both were externally recorded at 2026-10-11 05:22:10 UTC before native work.
The mixed/generic paired study is excluded from this baseline protocol.

After that timestamp, a training **build** was briefly started for the first
case, `arithmetic_16`, while an unrelated record-v2 Zig build was active.
The V8 process group received SIGINT and the collector exited 130. It
produced no completed package, package-build record, build inventory, proof,
trial report, or timed corpus. The 1.7 MiB generated-source and partial
staging directory was preserved under `zig-out/s31-v8-aborted-overlap/train`.
The canonical `zig-out/s31-v8-evidence/train` path was cleared for a complete
restart after an exclusive build-slot handoff. This interrupted attempt is
excluded from every model and timing claim; no V8 protocol or tool source was
changed. It may have warmed the global Zig compiler cache. Subsequent package
build times therefore describe **fresh package paths under the observed
cache state**, not cold-cache builds.

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
