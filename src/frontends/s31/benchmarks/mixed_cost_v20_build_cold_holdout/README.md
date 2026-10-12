# V20 prospective build and cold holdout

V20 measures the `calls6_log14_b8` mixed circuit on the pinned S31 compiler
revision `93114df`. This source was already measured in V18, so this is **not
an unseen-topology test**. It has a larger bundled-circuit trace (`log14`)
than the `log13` source used in V19. The claim inputs are new. The study asks
whether one-host build and first-use forecasts based solely on V18/V19 survive
this circuit and the current compiler revision.

The immutable pre-native protocol is
`design/s31/measurements/language/mixed-cost-v20-build-cold-holdout-protocol.json`.
It pins source bytes, 21 assignments and statements, shuffled claim order,
production file hashes, tool hashes, engine gitlink, host identity, the V18
warm prediction and exact native geometry, and the four lifecycle forecasts.
It checks the current checkout and committed protocol before creating the
one-attempt marker and running any native build. The package build is a fresh
`zig build ... install` invocation with an isolated prefix. The study records
one verified first proof, an immediate same-claim repeat, and 20 fresh
verified claims in fresh prover and verifier processes. For every proof it
requires the emitted public statement to match exactly and a changed-result
statement to be rejected by the native verifier at the proof layer. Manifest
admission checks every ordered call, slot, constraint, trace log, and tree
column against the frozen V18 source expectation before any timed proof.

## Forecast and gates, fixed before the native attempt

The build, first-proof, and immediate-repeat centers are the componentwise
medians of four **prior** lifecycle observations: the three V18 sources and
V19's `calls6_log13_b8`. The 20 warm claims use V18's preexisting predicted
one-draw median for this source. No target result is used for fitting.

| Metric | Frozen center | Maximum observed-relative error |
| --- | ---: | ---: |
| One package build | 78.164 s | 25% |
| First post-build verified proof | 1.184 s | 40% |
| Immediate same-claim verified repeat | 0.291 s | 50% |
| Build plus 22 verified proof-process durations | 86.060 s | 25% |

The total is `build + first + repeat + 20 × 0.321025 s`; it is a **sum of
separately measured process durations**, excluding idle gaps, and is not an
end-to-end stopwatch forecast. These are exploratory one-host tolerances,
not calibrated confidence intervals. The old V18 warm accuracy, interval,
proof-size, RSS, and stage gates remain conjunctive. A wrong exact manifest or
one failed honest/changed-result proof pair fails the study irrespective of
timing. A failed or interrupted attempt stays a failed record; no refit or
second run is permitted within this protocol.

Before the native run:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v20_build_cold_holdout/freeze.py check
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v20_build_cold_holdout/*.py
```

On a quiet host, with no other build or proof job competing for CPU and memory:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v20_build_cold_holdout/study.py run \
  --out /absolute/isolated/v20-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v20_build_cold_holdout/audit.py \
  --out /absolute/isolated/v20-artifacts --native --write
```

The audit checks raw source, assignments, statements, binary and proof hashes,
exact manifest admission, phase and timing records, the frozen score, and
native replay of all honest and changed-result verifier calls. The marker,
result, score, and audit are committed under `design/s31/measurements/language/`.
Raw proof and binary artifacts remain in the isolated output directory.

This protocol can establish only a local, one-source prospective result on
one host. It cannot establish cross-host accuracy, general cold-cache
behavior, or a Cairo speedup. V17's prior N8 warm-model failure remains a
failure regardless of the V20 outcome.
