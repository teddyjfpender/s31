# V7 prospective whole-prover cost study

Status: **tooling prepared; protocol and model not frozen; no V7 native
observations**. The V6 model failed the changed-stack [transfer diagnostic](WHOLE_PROVER_TRANSFER_V1.md).
Do not use V6 wall predictions to choose current S31 lowerings. This runbook
implements the [V7 design](WHOLE_PROVER_V7_PLAN.md) without changing V6 files.

## What V7 predicts

For one pinned host, compiler, engine, and proof profile, V7 predicts the mean
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
the study does not claim shape novelty. Mixed-chip programs enter only after a
reviewed proof-backed native profile exists.

## Freeze in this order

First commit the V7 tooling on the final S31 and engine gitlink revisions and
initialize that exact clean engine checkout. `draft` refuses uncommitted
benchmark/frontend sources and refuses an unclean or wrong engine checkout.
It generates both splits and writes the one-time protocol. The tool inventory
is every `*.py` under `src/frontends/s31/benchmarks/` and
`src/frontends/s31/python/`, including transitive predictors and both
independent value oracles.

```sh
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py draft \
  --out zig-out/s31-v7-freeze-inputs
git add design/s31/measurements/language/whole-prover-cost-v7.json
git commit -m 'Freeze prospective S31 V7 protocol'
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py anchor protocol
git add design/s31/measurements/language/whole-prover-cost-v7-protocol-freeze.json
git commit -m 'Anchor prospective S31 V7 protocol'
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
  --split train --phase build --out zig-out/s31-v7-train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split train --phase prove --out zig-out/s31-v7-train \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v7.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  fit zig-out/s31-v7-train/whole-prover-corpus.json \
  --out design/s31/measurements/language/whole-prover-cost-v7-model.json
git add design/s31/measurements/language/whole-prover-cost-v7-model.json
git commit -m 'Freeze training-only S31 V7 model'
python3 src/frontends/s31/benchmarks/cost/v7_protocol.py anchor model \
  --model design/s31/measurements/language/whole-prover-cost-v7-model.json
git add design/s31/measurements/language/whole-prover-cost-v7-model-freeze.json
git commit -m 'Anchor training-only S31 V7 model'
```

**Before the first held-out package build**, externally record the full
serialized model SHA-256 and full model-anchor commit SHA. The model anchor
must descend the protocol anchor. The V7 predictor fits coefficients and
empirical intervals only from the training corpus; the held-out sources,
assignments, and gates were fixed in the earlier protocol.

Then build, prove, evaluate, and replay the held-out split:

```sh
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split validation --phase build --out zig-out/s31-v7-validation \
  --model design/s31/measurements/language/whole-prover-cost-v7-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/benchmark_whole_prover_cost_v7.py \
  --split validation --phase prove --out zig-out/s31-v7-validation \
  --model design/s31/measurements/language/whole-prover-cost-v7-model.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit>
python3 src/frontends/s31/benchmarks/whole_prover_predictor_v7.py \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  evaluate design/s31/measurements/language/whole-prover-cost-v7-model.json \
  zig-out/s31-v7-validation/whole-prover-corpus.json \
  --out zig-out/s31-v7-validation/evaluation.json
python3 src/frontends/s31/benchmarks/publish_whole_prover_cost_v7.py \
  zig-out/s31-v7-train/whole-prover-corpus.json \
  design/s31/measurements/language/whole-prover-cost-v7-model.json \
  zig-out/s31-v7-validation/whole-prover-corpus.json \
  zig-out/s31-v7-validation/evaluation.json \
  --expected-protocol-sha256 <full-protocol-sha256> \
  --protocol-anchor-commit <full-protocol-anchor-commit> \
  --expected-model-sha256 <full-model-sha256> \
  --model-anchor-commit <full-model-anchor-commit> \
  --out zig-out/s31-v7-audit.json
```

The publisher reads package manifests, saved proof hashes, trial reports,
assignments, public statements, component manifests, both independent value
oracles, anchors, and the frozen model. It refits training and reevaluates the
held-out gate without rebuilding packages or altering evidence. `--native`
additionally reruns each saved original and changed public statement against
its native verifier. Raw package, proof, source, and assignment directories
must be retained beside the corpus files for replay. The current artifact
format stores absolute paths, so replay requires the original directory
layout; portable archive support is future work.

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

Even a passing V7 local gate does not establish cross-host or future-revision
transfer, compiler soundness, or soundness-equivalent lowering selection.
Automatic lowering remains disabled pending paired measurements and verifier
equivalence review.
