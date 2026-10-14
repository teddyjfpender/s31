# Independent follow-up: physical modeled trace and V15 score

Reviewed [`CheckedPhysicalModeledComposition.lean`](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/CheckedPhysicalModeledComposition.lean) at `7b31f55` after the reported focused Lake build and `leanchecker` replay, and the frozen V15 artifacts in commits `8516b8c` and `65bc930`. This review inspected theorem premises and proof steps and independently calculated the proof-size coverage gate from the committed JSON. I did not replay native proofs or rerun the benchmark.

## Physical modeled theorem

`checked_u8_physical_modeled_trace` assumes three explicit executable results: byte `checkRelation = some certificate`, constant-island `check = true`, and bounded Gate-address-ledger `check = true`. It obtains the modeled wire/output and local roots from `checked_u8_direct_full_modeled_trace`, constructs `physical := traceWithExternal (joinedCells ...) wire externalUses externalYields`, and applies `checked_joined_trace_gate_balance` to the **same trace's** decoded rows and external fields. The old modeled Gate balance conjunct is discarded, rather than fed back as a premise. The decoded-row bridge derives the row permutation from the checked complete, distinct, bounded, canonical 512-cell roster. I found no circular balance premise or stronger conclusion than these constructions support.

The result is conditional witness existence for the admitted direct functional source fragment. It does not prove that an arbitrary accepted native proof has these fixed/main rows or event fields. In particular, the caller supplies external address lists; this theorem neither derives them from the production public feeder nor binds `joinedCells` to a native preprocessed commitment. Production compiler/source-plan binding, committed main/interaction openings, the probabilistic Gate/Chip lookup argument, and PCS/FRI verification remain independent obligations. The module comment and theorem docstring state this modeled scope accurately.

## Independent V15 proof-gate calculation

I read the frozen [model](../../../measurements/language/mixed-cost-v15-operator-mix-model.json), [protocol](../../../measurements/language/mixed-cost-v15-operator-mix-protocol.json), and raw [result](../../../measurements/language/mixed-cost-v15-operator-mix-result.json) `records[].trials` without importing or calling `study.py`. For each source I selected the 20 trials with a non-null `scored_ordinal`, calculated the frozen center as `127611 + 2 × 18624.5 + (call_count - 1) × 15645.375`, and used the model's relative half-width `0.06462233998864397`. Each score requires coverage at least `0.8`, or 16 of 20 samples.

| Source | Frozen interval, bytes | Raw median, bytes | In / below / above band | Coverage |
| --- | ---: | ---: | ---: | ---: |
| `wide_addheavy_n1` | 154206.361–175513.639 | 152822.5 | 5 / 15 / 0 | 0.25, fail |
| `wide_mix_n1` | 154206.361–175513.639 | 153107.5 | 5 / 15 / 0 | 0.25, fail |
| `wide_mix_n2` | 168840.695–192170.055 | 167669.5 | 7 / 13 / 0 | 0.35, fail |

These independent counts match [`MIXED_COST_V15_OPERATOR_MIX_RESULT.md`](../../../measurements/MIXED_COST_V15_OPERATOR_MIX_RESULT.md) and the canonical score. Direct SHA-256 of the committed protocol/model/result/score/audit files matched the report's five digests; the protocol→model, result→protocol/model, and score→result/protocol digest references also matched. The frozen challenge therefore remains **FAIL**. This calculation only checks score arithmetic and committed-file linkage; it does not independently certify trial acquisition, the temporary proof artifacts, or native verifier replays. The report discloses that the raw native artifacts live at a temporary path and need separate archiving for durable replay.

Reproduction from the repository root, using only Python's JSON and statistics libraries:

```sh
python3 - <<'PY'
import json, statistics
from pathlib import Path
b = Path('design/s31/measurements/language')
prefix = 'mixed-cost-v15-operator-mix-'
model = json.loads((b / (prefix + 'model.json')).read_text())
result = json.loads((b / (prefix + 'result.json')).read_text())
for record in result['records']:
    center = (model['base_metrics']['proof_bytes']
              + model['structural_steps_to_v15'] * model['structural_step_per_1024_ops']['proof_bytes']
              + (record['call_count'] - 1) * model['long_call_step']['proof_bytes'])
    half = model['proof_relative_half_width']
    low, high = center * (1 - half), center * (1 + half)
    sizes = [trial['proof_bytes'] for trial in record['trials']
             if trial['scored_ordinal'] is not None]
    print(record['name'], len(sizes), statistics.median(sizes),
          sum(low <= size <= high for size in sizes),
          sum(size < low for size in sizes), sum(size > high for size in sizes))
PY
```

Output: `wide_addheavy_n1 20 152822.5 5 15 0`; `wide_mix_n1 20 153107.5 5 15 0`; `wide_mix_n2 20 167669.5 7 13 0`.
