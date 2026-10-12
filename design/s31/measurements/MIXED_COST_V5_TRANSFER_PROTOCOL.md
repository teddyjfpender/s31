# Prospective N=1/N=8 transfer of the frozen mixed-cost v4 predictor

The [v4 model](language/mixed-cost-v4-model.json) is fixed. This protocol
tests its **call-count-only** warm-wall distribution and proof-size interval
at one and eight calls, beyond the v4 fit counts of three and seven. The
[executable protocol](../../../src/frontends/s31/benchmarks/mixed_cost_v5_transfer/protocol.py)
pins exact source and claim SHA-256 IDs, two predictions per source, software
and host fingerprints, trial order and score limits. The protocol JSON must
be committed before the first native build. Any source admission or proof
failure is reported; it does not license changing the source or selecting a
better rerun.

| Source | Calls | Source structure | Scored fresh process pairs |
| --- | ---: | --- | ---: |
| `scaled_seed_n1` | 1 | Scale public four-word input, one 16-round chip call, add input | 20 |
| `weighted_scan_n8` | 8 | Repeated weighted input blend and 16-round chip call, then add input | 20 |

The runner builds each `direct-mixed-general` package in `ReleaseFast`, then
checks the source-bound native manifest, its component slots/columns and
20-bit interaction/26-bit FRI PoW. It runs claim 0 twice for descriptive
cold/startup behavior, then claims 1–20 once in order. Every proof must
verify, and a correctly encoded changed public result must be rejected at
the interaction nonce. Build wall and the two claim-0 wall values are
descriptive; only claims 1–20 are scored against the frozen predictions.

Precommitted per-source gates are wall median relative error ≤35%, predicted
90% wall interval coverage ≥70%, proof median relative error ≤10%, and
predicted 90% proof interval coverage ≥70%. Relative error divides by the
observed median, as in v4. Both sources must pass each gate for an overall
pass. These limits test practical transfer on this small corpus. With 20
claims per source, realized PoW and interval coverage remain noisy; this
does not establish general statistical coverage.

No v4 coefficients or residuals may be updated from this run. The source
families and counts differ from the v4 sources, and the committed protocol
records exact claim disjointness checks. The predictor has no DAG, record,
feeder, manifest, or observed PoW feature; failures should be read as model
scope evidence. The measurement is not a speedup comparison or an automatic
lowering evaluation.
