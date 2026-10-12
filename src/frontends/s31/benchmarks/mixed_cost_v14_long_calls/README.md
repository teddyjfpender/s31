# V14 long-call/log13 prospective challenge

Read `design/s31/measurements/MIXED_COST_V14_LONG_CALLS_PROTOCOL.md` for source semantics, the frozen predictor, admission, schedule, gates, and build/cold limitation.

From the isolated repository root: run `python3 src/frontends/s31/benchmarks/mixed_cost_v14_long_calls/test_static.py` and `model.py check`. Before any native build, run `protocol.py freeze`, commit the model/protocol/sources/scripts/design, then run `protocol.py check` and send the commit/hash for independent preflight. During an exclusive CPU window, run `study.py run --out /tmp/unique-v14-run` once. Run `audit.py --out /tmp/unique-v14-run --native --write` to check saved bytes/scores and replay every honest/changed-result verifier invocation. Preserve any admission or scored failure without retuning.
