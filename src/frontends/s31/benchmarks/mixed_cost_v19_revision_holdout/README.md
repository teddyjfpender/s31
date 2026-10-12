# V19 current-revision cost replication

This is a **new-claims/current-revision replication** of V18's
`calls6_log13_b8` program. It does not test an unseen topology. The S31 source
and frozen V18 prediction are copied by exact hash from the V18 protocol; the
20 input/output claims are new. The compiler revision and pinned production
files differ from V18. The question is whether V18's one-host warm prediction
and exact native component geometry survive this revision and a new claim
sample. V17's N8 failure remains a failure regardless of this result.

The canonical protocol is
`design/s31/measurements/language/mixed-cost-v19-revision-holdout-protocol.json`.
It was frozen and committed before any V19 native build. It fixes the source,
all 21 assignment and statement hashes, shuffled warm order, V18 prediction,
exact native manifest and call admission, one-attempt marker, and conjunctive
gates. A manifest change is an admission failure. Every honest proof must be
accepted by an external verifier and every changed-result control must be
rejected at the proof layer. The first post-build proof and its immediate
same-claim repeat are descriptive. One package build is also descriptive;
there is no fitted build or cold-start accuracy claim.

The warm score uses 20 fresh prover and verifier processes, measured with
`/usr/bin/time` for peak RSS. It takes the median of verified whole-process
wall times. It subtracts native-reported interaction and FRI proof-of-work
durations only for the separately reported non-PoW diagnostic; residuals must
stay positive. Prediction bands and gates are those frozen before this run.
The protocol's sample-of-20 wall band is additionally required.

Run static preflight before the single native attempt:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v19_revision_holdout/freeze.py check
python3 -m py_compile src/frontends/s31/benchmarks/mixed_cost_v19_revision_holdout/*.py
```

Run the native attempt on a quiet host, from the S31 repository root:

```sh
python3 src/frontends/s31/benchmarks/mixed_cost_v19_revision_holdout/study.py run \
  --out /absolute/isolated/v19-artifacts
python3 src/frontends/s31/benchmarks/mixed_cost_v19_revision_holdout/audit.py \
  --out /absolute/isolated/v19-artifacts --native --write
python3 src/frontends/s31/benchmarks/mixed_cost_v19_revision_holdout/lifecycle.py \
  design/s31/measurements/language/mixed-cost-v19-revision-holdout-result.json
```

The attempt marker is created with `O_EXCL` before the package build. An
interrupted or failed attempt stays a failure; changing the source or gates
after observing it would be a new exploratory study. Raw proofs, native reports,
binary hashes, manifests, and timing ledgers stay in the artifact directory.
The committed result and audit summarize that one attempt.
