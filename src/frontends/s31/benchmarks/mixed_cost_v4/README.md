# Mixed whole-prover cost study v4

This is a prospective, host-specific distribution study for eight new S31
`direct-mixed-general` programs. It estimates warm first-verified process wall
and proof size from training sources only. The source and claim inventory is
already frozen in `design/s31/measurements/language/mixed-cost-v4-prospective-inventory.json`.
The final protocol must be prepared and committed before the first native
build. See `design/s31/measurements/MIXED_COST_V4_PROTOCOL_PROPOSAL.md` for
the model derivation and fixed acceptance gates.

Run the native-free checks first:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_static.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_model.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/test_study.py -q
python3 -B src/frontends/s31/benchmarks/mixed_cost_v4/prospective.py preview
```

The exact chronological experiment, from the repository root, is:

```sh
V4=src/frontends/s31/benchmarks/mixed_cost_v4/study.py
OUT=zig-out/s31-mixed-cost-v4

# First commit the runner, all frontend and engine sources, and the prospective inventory.
python3 -B "$V4" prepare
git add design/s31/measurements/language/mixed-cost-v4-protocol.json
git commit -m 'design: freeze mixed cost v4 native protocol'

# Quiet host: no concurrent native build, formal kernel replay, or CPU-heavy task.
python3 -B "$V4" train --out "$OUT"
python3 -B "$V4" audit-train --out "$OUT"
python3 -B "$V4" fit --out "$OUT"
git add design/s31/measurements/language/mixed-cost-v4-train.json \
        design/s31/measurements/language/mixed-cost-v4-model.json \
        design/s31/measurements/language/mixed-cost-v4-model-anchor.json
git commit -m 'bench: anchor mixed cost v4 training model'

MODEL_SHA=$(shasum -a 256 design/s31/measurements/language/mixed-cost-v4-model.json | cut -d ' ' -f 1)
ANCHOR_COMMIT=$(git rev-parse HEAD)
python3 -B "$V4" heldout --out "$OUT" \
  --model-sha256 "$MODEL_SHA" --model-anchor-commit "$ANCHOR_COMMIT"
python3 -B "$V4" audit-heldout --out "$OUT"
python3 -B "$V4" evaluate --out "$OUT" \
  --model-sha256 "$MODEL_SHA" --model-anchor-commit "$ANCHOR_COMMIT"
```

The first build and claim-0 process pair are descriptive cold/startup
diagnostics. Claims 1–40 train the model; 41–79 calibrate its uncertainty.
Only heldout claims 1–79 are scored. All 648 native proofs must verify, and
all 648 changed public results must be rejected at the interaction nonce.
The `cold_warm` summary's descriptive warm median includes the claim-0
same-claim repeat; the fitted model and heldout score exclude both claim-0
processes.
Raw proofs, statements, process stderr, manifests and package binaries live
under `$OUT`; compact canonical corpora and the model live under `design/`.
Run the commands in order with an unchanged working tree for compiler/engine
and v4 tool files. A failed or interrupted timing run must be declared and
restarted in a fresh output directory; do not select a rerun by score.

The timing prediction is empirical and local to the pinned host, Zig binary,
engine gitlink, compiler sources and manifest geometry. The exponential PoW
approximation and proof interval transfer across unseen DAG families are
tested by heldout coverage, not assumed to hold. Neither a speedup over Cairo
nor automatic lowering quality is measured here.
