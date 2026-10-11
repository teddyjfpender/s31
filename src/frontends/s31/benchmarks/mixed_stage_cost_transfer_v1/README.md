# Cross-source-shape mixed cost transfer

Read the [prospective design and runbook](../../../../../design/s31/measurements/MIXED_STAGE_COST_TRANSFER_V1.md).

`cohort.py` generates 12 deterministic record ABI v2 sources and 360 new
assignments/claims without native work. `protocol.py` drafts and checks the
separately anchored stack freeze. `study.py` builds, proves, seals the raw
phase, and performs native audit replay. `score.py` applies only the prior
training model, identified by its exact frozen hash; it never fits transfer
observations. No native transfer corpus has been collected or scored yet.

```sh
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/cohort.py preview
python3 -B src/frontends/s31/benchmarks/mixed_stage_cost_transfer_v1/test_static.py
```
