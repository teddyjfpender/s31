# Cross-source-shape mixed cost transfer

Read the [prospective design and runbook](../../../../../design/s31/measurements/MIXED_STAGE_COST_TRANSFER_V1.md).

`cohort.py` generates 12 deterministic record ABI v2 sources and 360 new
assignments/claims without native work. `protocol.py` drafts and checks the
separately anchored stack freeze. `study.py` builds, proves, seals the raw
phase, and performs native audit replay. The 360-trial native phase and audit
completed, but the exact earlier training model bytes were lost. `score.py`
requires their frozen SHA-256 and the transfer remains **unscored**. See the
[result](../../../../../design/s31/measurements/MIXED_STAGE_COST_TRANSFER_V1_UNSCORED_RESULT.md).

`descriptive.py` independently replays the **committed compact corpus**. It
pins all five source-file SHA-256 digests, checks the protocol inventory and
all 360 assignment/statement identities, source and engine fingerprints,
native audit flags, every process endpoint, stage partition, and proof
uniqueness. It produces the committed
[descriptive replay](../../../../../design/s31/measurements/language/mixed-stage-cost-transfer-v1-descriptive-replay.json).
This is an observed-cost table, not a fitted model or a transfer score. The
full native proofs live in the frozen worktree, so the compact replay cannot
independently rerun STARK verification; the earlier frozen native audit did.

```sh
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py preview
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/test_static.py
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/descriptive.py \
  > /tmp/s31-mixed-descriptive-replay.json
cmp /tmp/s31-mixed-descriptive-replay.json \
  design/s31/measurements/language/mixed-stage-cost-transfer-v1-descriptive-replay.json
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/test_descriptive.py -q
```

A future predictive transfer needs a new prospective protocol with the
exact training model bytes committed **before** held-out native work. The
[retention gate](../model_artifact_retention_v1/README.md) implements that
preflight and must be wired into the new collector. Engine phase timing is
being developed behind an optional diagnostic seam; until it is pinned and
measured, `native_prove_including_setup_ns` remains opaque in this corpus.
