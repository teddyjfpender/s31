# V12 decomposed unseen-geometry experiment

Read `design/s31/measurements/MIXED_COST_V12_DECOMPOSED_PROTOCOL.md` for the frozen question, model, source geometry, schedule, and score gates. All commands below run from the repository root of the isolated worktree.

1. `python3 src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/test_static.py` checks source claims, geometry expectations, schedule, model classification, and score agreement without native proving.
2. `python3 src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/model.py check` checks the canonical model against its declared V10/V11 inputs.
3. Before the **first** V12 native build only, `python3 src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/protocol.py freeze` writes the canonical protocol and four source files. Commit them with the model, scripts, and design protocol. Then `protocol.py check` must pass without byte changes.
4. During an exclusive CPU window, run `python3 src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/study.py run --out /tmp/unique-v12-run`. This is one scored run; it writes canonical result and score artifacts under `design/s31/measurements/language`.
5. Run `python3 src/frontends/s31/benchmarks/mixed_cost_v12_decomposed/audit.py --out /tmp/unique-v12-run --native --write` for independent file/score checks and saved-binary honest/changed-result verifier replay.

Do not refit after seeing V12 outcomes. An admission failure, native proof failure, or missed score gate remains a reported failed prospective result.
