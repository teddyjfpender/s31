# Prospective v7 cost-model transfer after v6 stack invalidation

The [v6 attempt](MIXED_COST_V6_TRANSFER_INVALIDATED.md) is unscored because
the compiler fingerprint changed during measurement. V7 is a fresh cohort,
with new source JSON and 81 new assignment/statement pairs per source. The
[executable protocol](../../../src/frontends/s31/benchmarks/mixed_cost_v7_transfer/protocol.py)
checks that no source or claim hash overlaps v4, v5 or v6. It commits exact
source bytes, host and compiler/engine fingerprints, unchanged v4-model
SHA-256, predictions, gates and trial order **before any native build**.
The v4 model is never updated using v5 or v6 data.

| New family | Calls | Feeder structure | Scored claims |
| --- | ---: | --- | ---: |
| `affine_seed_n1` | 1 | Scale and offset input before chip; offset chip result and add input | 80 |
| `switchback_n8` | 8 | Alternate add/scale feeders; offset after every third chip call | 80 |

The first claim is run twice in adjacent fresh prover/verifier processes as
a descriptive cold/startup pair. Claims 1–80 are scored once each. The
runner checks source-bound manifest identity, component geometry and 20-bit
interaction/26-bit FRI PoW. It requires every honest typed statement and
proof to verify, and every ABI-valid changed public result to reject at
`InvalidMixedInteractionNonce`. It records process endpoints, native phases,
proof sizes and hashes, and complete manifests. A final check requires the
same pinned stack as the pre-native commit. A build, proof, or pin failure
is reported as an invalid or failed attempt without score-selected retries.

The per-source gates are the same as v6: wall median error ≤30%, predicted
90% wall interval coverage ≥80%, proof median error ≤10%, and predicted 90%
proof interval coverage ≥80%. Relative error divides by the observed median.
First-post-build and package-build walls are descriptive only. Even 80 claims
on one host cannot establish general transfer or nominal coverage for
arbitrary programs; no Cairo speedup claim is made.
