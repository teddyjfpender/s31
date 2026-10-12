# V18 N6/N7 branch-topology prospective cost challenge: local pass

**Frozen score: PASS.** The one permitted V18 run used isolated pre-native commit `f73bbae` (`/tmp/s31-v18-mixed-topology-e9be79a`), protocol SHA-256 `07dab408bad90494613a8d67d5b5240cb8bb746398a07b59df4ea87503ad4840`, and model SHA-256 `97a1a02ebd1a69022fe9e810ec392078d7eb4450aa4573d51582f98953c05058`. Independent static preflight approved the exact source/claim roster, prediction rules, geometry, schedule, one-attempt guard, and gates before any native build. V11, V15, and **failed V17** scores were declared training; V12–V14 and V16 were declared local passes. V18 source and claim bytes and native timings were unseen. No predictor, interval, source, gate, or runner changed after the attempt marker was created.

All three native manifests passed exact admission **before any proof**: `calls6_log13_b8` slots `[13,12,4,10,4,8,4,6,4,11,4,9,4]`, 125 constraints; `calls6_log14_b8` slots `[14,12,4,10,4,8,4,6,4,11,4,9,4]`, 125; and `calls7_log14_b32` slots `[14,12,4,10,4,8,4,6,4,11,4,9,4,7,4]`, 144. Ordered source-derived call semantics, full per-slot registry/offset/constraint projections, tree columns and PoW configuration also matched. The run made 66 honest proofs (claim 0 twice plus 20 scored claims/source) and 66 ABI-valid changed-result controls. Every honest external native verifier accepted; every changed result was rejected at `InvalidMixedInteractionNonce`.

## Frozen warm score

| Held-out source | Whole verified wall observed / predicted | Wall median error | One-draw wall hits | Non-PoW median error | Proof median observed / predicted | Proof hits | Prover / verifier RSS error | Largest native stage error |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| N6 log13, 8 branches, one-third mul | 214.94 / 222.02 ms | 3.29% | 19/20 | 0.81% | 228,117.5 / 227,381 B | 20/20 | 3.65% / 1.87% | 3.10% |
| N6 log14, 8 branches, one-third mul | 338.65 / 321.03 ms | 5.20% | 19/20 | 0.68% | 255,110 / 251,990 B | 20/20 | 2.39% / 2.60% | 1.94% |
| N7 log14, 32 branches, one-seventh mul | 314.26 / 322.56 ms | 2.64% | 19/20 | 1.26% | 268,918 / 267,094 B | 20/20 | 1.63% / 0.15% | 1.99% |

All prespecified conjunctive gates passed. The per-source wall-median errors were ≤5.20% versus the frozen ≤35% gate; nominal 90% one-draw wall bands covered 19/20 per source and 57/60 pooled versus ≥14/20 and ≥49/60. All three observed sample-of-20 medians fell in their frozen bands, versus ≥2/3. Non-PoW whole-process median errors were ≤1.26% versus ≤20%; each of four native package-stage errors was ≤3.10% versus ≤30%. Proof median errors were ≤1.22% versus ≤10%, and the V16-derived 9.846% proof interval covered 20/20 per source versus ≥16/20. Both RSS median errors were ≤3.65% versus ≤30%. The exact gates and unrounded values are in the canonical score JSON.

V17's N8 log13 wall-center failure remains a failure. V18 explicitly trained on V17, expanded its sample-median band by 1.5, and relaxed the wall-center gate from 30% to 35% **before** V18 measurement. The small observed V18 center errors are therefore more informative than simply clearing these broad gates; three related source families on one host remain too little evidence for general calibration. The observed FRI PoW medians were 68.78, 89.66, and 61.46 ms, respectively; the corresponding non-PoW observed/predicted medians were 148.48/147.27, 247.97/246.28, and 250.98/247.81 ms. Medians of sums need not equal sums of medians, so the phase split is diagnostic and does not replace the frozen whole-wall score.

## Descriptive build/cold costs and independent audit

| Source | Package build wall | First post-build verified wall | Immediate same-claim repeat |
|---|---:|---:|---:|
| N6 log13 B8 | 79.90 s | 1.288 s | 296.53 ms |
| N6 log14 B8 | 76.43 s | 1.156 s | 377.54 ms |
| N7 log14 B32 | 75.43 s | 1.092 s | 284.86 ms |

The frozen protocol has **no build or cold-start prediction gate**. One build/source and first claim on one host remain confounded by compiler cache and process state, and these costs were excluded from warm medians. Their scale matters when evaluating end-to-end use.

The independent `audit.py --native --write` exited 0. It recomputed the exact canonical score, checked all saved source/claim/proof and binary hashes, native manifests/reports, physical interleaved timing order and OS RSS endpoints, then replayed 66 honest and 66 changed-result verifier calls. Canonical result, score, and audit SHA-256 digests are `3a5d20ef644581bf02dd17cc0b4c3b580cbbd6783ef89f33b70329a96bca9a91`, `e7defea74f7403e772344431a4cfd46d89d41836aba7629a6a19f9d4f154eafc`, and `8691e05f25b1ccaabe8d8d0d7ab5d1865e58ad107db4058ea306aa88d92f05cf`. Canonical ledgers and the fixed one-attempt marker are under `design/s31/measurements/language/`. Raw proofs, binaries, manifests, native reports, and controls remain in `/tmp/s31-v18-mixed-topology-e9be79a/.v18-artifacts`; archive that directory separately for long-term native replay.

This local pass supports the three held-out N6/N7 source families at the pinned pre-main-root compiler/engine revision, Apple M5 Max host, and `/usr/bin/time` collection method. It does not update the failed V17 score, model package-build/cold costs, establish host-independent whole-prover reliability, prove AIR/PCS soundness, or measure a Cairo speedup.
