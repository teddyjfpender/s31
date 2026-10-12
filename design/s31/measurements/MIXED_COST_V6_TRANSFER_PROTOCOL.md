# Prospective 80-claim transfer after the v5 N=1 median miss

The [v5 result](MIXED_COST_V5_TRANSFER_RESULT.md) contains one missed N=1
warm-wall median gate over 20 scored claims. This is a **new** prospective
cohort with 80 scored claims for each of two new source families. The
[executable protocol](../../../src/frontends/s31/benchmarks/mixed_cost_v6_transfer/protocol.py)
must freeze exact source JSON bytes, source/assignment/statement hashes,
v4-model SHA-256, host and compiler/engine pins, predictions, gates and trial
order in a Git commit before the first native package build. The v4
predictor's coefficients, residuals, PoW distribution and proof interval
remain unchanged; v5 measurements are not fit data.

| New family | Chip calls | Circuit feeder structure | Scored claims |
| --- | ---: | --- | ---: |
| `offset_seed_n1` | 1 | Add constant to public input; after the chip, scale and add input | 80 |
| `crosswind_n8` | 8 | Alternate scale/offset feeders and add original input between calls | 80 |

For each source, the first assignment is run twice in adjacent fresh
prover/verifier processes to describe startup and immediate repetition.
Assignments 1–80 then run once each and are scored. A package build or proof
failure stays in the retained output as a failed transfer observation. The
native manifest must bind the source, component roster, column geometry and
20-bit interaction/26-bit FRI PoW. Every honest proof must verify against its
typed claim. A valid one-word public-result mutation must reject specifically
at the interaction nonce. The runner records all native phases, process
endpoints, proof hashes and complete manifests.

The frozen limits, separately per source, are warm-wall median relative error
≤30%, predicted 90% wall interval coverage ≥80%, proof-size median relative
error ≤10%, and predicted 90% proof interval coverage ≥80%. Error divides by
the observed median. First-post-build wall, immediate repeat and package
build wall are descriptive only. The new source and claim identities are
checked for disjointness from v4 and v5. This study uses one host and one
software stack, and it neither tests a Cairo speedup nor implies general
statistical coverage.
