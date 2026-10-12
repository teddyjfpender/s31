# V17 mixed-call prospective cost challenge: failed whole-wall gate

**Frozen score: FAIL.** The one permitted V17 native run used isolated pre-native commits `ce9ef2b`, `2f6203d`, and `e8b19fb`, with the final amended protocol SHA-256 `c4402bff32a5b24db6e6e32fa26ea5137aff1170bcd1ba9e99dbed747d479329` and unchanged model SHA-256 `5a24f246aac2fb197bd5029d6dbdae4adcd92d3e7dea798a9693e15faacbc51d`. Independent static preflight approved the amended freeze before any V17 native build. V11/V15 failed scores and V12–V14/V16 passes were declared training; these three V17 sources and 60 scored claims were unseen. No source, predictor, interval, gate, or runner was altered after the native attempt began.

All three exact native manifests passed admission **before any proof**: N4 log13 slots `[13,12,4,10,4,8,4,6,4]` with 87 constraints, N4 log14 slots `[14,12,4,10,4,8,4,6,4]` with 87, and N8 log13 slots `[13,12,4,11,4,10,4,9,4,8,4,7,4,6,4,5,4]` with 163. Admission checked source-derived ordered call IDs, feeder/source node IDs, constants and rounds, the complete frozen slot layout including per-slot constraints, and the bounded address-chain properties described in the protocol. The single attempt marker was created before the first build and retained. All 66 honest proofs were accepted by the native verifier; all 66 exact ABI-valid changed-result controls were rejected at `InvalidMixedInteractionNonce`.

## Frozen scored result

| New source | Whole verified wall median observed / predicted | Wall center error (gate ≤30%) | One-draw wall hits | Non-PoW median error | Proof median observed / predicted | Proof hits | Prover / verifier RSS error | Largest native stage error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| N4 log13 | 218.30 / 218.88 ms | 0.27% | 19/20 | 0.04% | 197,174 / 197,471 B | 20/20 | 1.81% / 0.27% | 4.23% |
| N4 log14 | 288.44 / 316.62 ms | 9.77% | 20/20 | 0.55% | 221,783 / 222,905 B | 20/20 | 1.22% / 0.93% | 2.40% |
| **N8 log13** | **171.93 / 224.41 ms** | **30.52% FAIL** | 17/20 | 0.45% | 257,588.5 / 258,336 B | 20/20 | 2.37% / 0.70% | 1.87% |

The N8 log13 observed sample median also fell **below** its frozen 90% sample-median band `[184.65, 316.18]` ms. This band miss alone did not fail the aggregate gate because the other two source medians were inside their bands, meeting the prespecified ≥2/3 rule. Pooled one-draw wall coverage was 56/60 against ≥49/60. All proof, non-PoW, four native phase, and both RSS gates passed. The result is still a conjunctive **FAIL** because N8 wall center error exceeds its 30% gate; there is no post-hoc widening, rerun, or exclusion.

The phase decomposition is informative but does not erase the miss. N8 non-PoW observed/predicted medians were 150.35/149.66 ms, a 0.45% error; its native FRI PoW median was only **17.94 ms**, versus the frozen one-draw PoW p50 of 73.47 ms inherited from V12. The N4 log13 and log14 FRI PoW medians were 71.12 and 43.84 ms. This is consistent with a lower N8 PoW realization driving most of the whole-wall miss. Medians of sums need not equal sums of medians, so this is a diagnostic comparison, not a causal proof or a replacement scoring rule. Interaction PoW medians were 1.17, 1.31, and 1.77 ms respectively.

## Build, cold start, audit, and scope

| Source | Package build wall | First post-build verified wall | Immediate same-claim repeat |
|---|---:|---:|---:|
| N4 log13 | 81.10 s | 1.177 s | 171.75 ms |
| N4 log14 | 74.40 s | 1.214 s | 374.23 ms |
| N8 log13 | 73.93 s | 989.54 ms | 153.23 ms |

The predeclared protocol has no build or cold-start prediction gate: one build/source on one host cannot separate source cost from compiler cache and process state. These measurements are descriptive and were excluded from the scored warm medians.

The independent `audit.py --native --write` exited 0. It recomputed the canonical score and exact geometry from saved files, checked source/claim/proof and binary hashes, native phase reports, physical interleaved timing order, and OS RSS endpoints, then replayed 66 honest and 66 changed-result native verifier calls. It confirmed the failed gate rather than converting the run into a pass. Canonical result, score, and audit SHA-256 digests are `c84ebaeba603a9ca7f9cf6572c3eac09cfc81b7ae092ecf1b371a6c7af5f4a59`, `aba4eb8a6516c9da7a7b674500a90a087cf0bc1f4d07daa07988fa91f1e01bdd`, and `bf258807eb8e4437aa6bab01ef3568339eced86845221913311a2c61cd2af6f4`. Canonical ledgers and the durable one-attempt marker are under `design/s31/measurements/language/`; raw proofs, binaries, manifests, native reports, and controls remain at `/tmp/s31-v17-mixed-calls-23f55ac/.v17-artifacts` (archive separately for long-term native replay).

This failure is evidence about a fragile stochastic whole-wall center on one host, not a failure of native proof verification or a measured prover speedup. It is evidence of accurate local non-PoW, proof-size, and RSS predictions for these three source families, with only 20 scored draws each. Build/cold cost remains unmodeled, and no host-independent or broad whole-prover reliability claim follows.
