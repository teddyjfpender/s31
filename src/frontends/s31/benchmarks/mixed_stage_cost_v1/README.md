# Prospective mixed stage cost model

Start with the [design and runbook](../../../../../design/s31/measurements/MIXED_STAGE_COST_MODEL_V1.md).
`cohort.py` previews a deterministic 8-source, 800-assignment inventory without
Zig. `model.py` implements the predeclared stage fit and held-out gate.
`protocol.py` drafts or checks the separate committed protocol freeze.
`study.py` builds source-embedded packages, collects proofs through the
source-bound stage diagnostic, audits saved evidence with native verifier and
changed-claim controls, fits the training model, evaluates held-out data, and
checks a separately committed held-out report anchor before publication.

**Current status:** the frozen v1 train and held-out corpus completed; see the
[audited result](../../../../../design/s31/measurements/MIXED_STAGE_COST_MODEL_V1_RESULT.md).
`study.py` still refuses native work without the exact committed protocol and
externally recorded full hash/anchor commit. The model predicts only first
verified wall and proof bytes for one pinned record ABI v2 repeat-chain source
family on one host. It never selects a lowering or claims a speedup.

Native-free checks:

```sh
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_v1/cohort.py
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_v1/test_static.py
python3 -B src/frontends/s31/benchmarks/paired_record_v2/test_diagnose_stages_v1.py
```
