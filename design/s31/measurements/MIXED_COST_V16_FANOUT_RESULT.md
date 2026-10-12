# V16 sixteen-way fanout/log-14 prospective cost challenge: local pass

**Frozen score: PASS.** The single V16 run used isolated pre-native commit `709de00` (`/tmp/s31-v16-fanout-4478736`), protocol SHA-256 `5cecdd6993c0222acb931eb71830476b7e2bfdff841bf73e8d6da216533b9b55`, and model SHA-256 `2f2944d3de0b7ea22f095fa5ec4eadb2d689118f0b816121186f6437e7895036`. Independent static preflight approved the frozen model/protocol/source/claim/gates before any native V16 build. V11 and V15 failures and V12–V14 passes were declared training; V16 sources, claims, and native timings were unseen. No frozen source, coefficient, interval, or gate was changed after timing.

All three exact native manifests were admitted **before any proof**: `fanout16_log13_n1` slots `[13,12,4]`, 30 constraints; `fanout16_log13_n2` slots `[13,12,4,12,4]`, 49 constraints; and `fanout16_log14_n1` slots `[14,12,4]`, 30 constraints. Source digests, calls/rounds, tree columns, max/composition log, registry digest, and PoW bits also matched the frozen protocol. The run made 66 honest proofs (claim 0 twice plus 20 scored claims/source) and 66 changed-result controls. Each honest native verifier accepted; each ABI-valid changed result was rejected at `InvalidMixedInteractionNonce`.

## Scored warm costs

| Source | Whole verified wall observed / predicted | Wall interval hits | Non-PoW residual median error | Proof median observed / predicted | Proof interval hits | Prover / verifier RSS median error | Largest native package-stage error |
|---|---:|---:|---:|---:|---:|---:|---:|
| Log-13 N1 | 192.73 / 213.50 ms | 19/20 | 1.01% | 151,886 / 152,965 B | 20/20 | 0.69% / 7.98% | 6.39% |
| Log-13 N2 | 207.69 / 214.96 ms | 19/20 | 1.54% | 167,422 / 167,527 B | 20/20 | 0.05% / 1.82% | 2.37% |
| Log-14 N1 | 339.60 / 306.15 ms | 19/20 | 2.73% | 177,319.5 / 178,319 B | 20/20 | 0.40% / **22.40%** | 7.12% |

All prespecified gates passed. Whole-wall median relative errors were 10.78%, 3.50%, and 9.85% versus ≤30%; pooled nominal 90% one-draw wall coverage was 57/60 versus ≥49/60, and all three sample-of-20 medians lay in their frozen median bands versus ≥2/3. Non-PoW errors were ≤2.73% versus ≤20%, and each of four native stage errors was ≤7.12% versus ≤30%. Proof median errors were 0.71%, 0.06%, and 0.56% versus ≤10%. The V15-calibrated 9.846% proof half-width covered **20/20 proofs for every source**, versus ≥16/20. Prover RSS errors were ≤0.69% and verifier RSS errors ≤22.40%, both within ≤30% gates. The log-14 verifier RSS miss is the largest remaining structural error and should not be obscured by the much smaller prover RSS errors.

This is a sharper local proof-size result than V15: the frozen V15 bands covered 5/20, 5/20, and 7/20, while V16's prospective bands covered all 60 new proofs. The V16 bands are also wider because V15's failed score was openly used as training. The very low V16 proof-median errors give separate evidence that the new centers transferred to these exact sources; the 100% interval coverage alone is weak evidence for broader calibration. The observed log-14 wall median exceeded its predicted center by 33.45 ms, while the non-PoW residual exceeded its prediction by 6.50 ms. Native FRI PoW median at log 14 was 101.95 ms, versus 48.13/63.27 ms for log-13 N1/N2, consistent with stochastic PoW contributing much of the wall shift. That decomposition is descriptive, not a causal identification of PoW variance.

## Descriptive build and cold-start costs

| Source | Package build wall | First post-build verified wall | Immediate same-claim repeat |
|---|---:|---:|---:|
| Log-13 N1 | 80.46 s | 1.058 s | 229.26 ms |
| Log-13 N2 | 74.55 s | 996.72 ms | 161.10 ms |
| Log-14 N1 | 73.99 s | 1.279 s | 443.88 ms |

The frozen protocol explicitly had **no build or cold prediction gates**. A single package build/source and first claim on one host remain confounded by cache and process state. These costs are material: warm proof medians near 0.2–0.34 seconds do not describe the first use or package generation. They are reported separately and excluded from warm scored medians.

## Independent audit and scope

The independent native audit exited 0 while recomputing the exact canonical score from saved files and checking all source/claim/proof hashes, native manifests/reports, physical interleaved timing order, and OS RSS timing endpoints. It checked 66 saved honest proof/control sets and replayed 66 honest plus 66 negative native verifier calls. The 60 scored claims in total used frozen schedule seed `202610130163`, with 20 claims/source interleaved; all emitted statements matched the independent four-lane M31 oracle.

Canonical result, score, and audit SHA-256 digests are respectively `01b47ef82ea8387a9698bf01a9f4ab4a79aa95f4a1474c79bb7251c22db43abd`, `4a795ba860250456c22f474baddd2f2c8571b2e0241bf07a0eaf264fd9109d0e`, and `f575a410a9ee7c0a09b7422a1286fd062fd35b2efb867f8aba30b0f27a580f1b`. The canonical JSON files are in `design/s31/measurements/language/`. The 66 raw proofs, saved binaries/manifests, native reports, and control files remain in `/tmp/s31-v16-fanout-4478736/.v16-artifacts`; the result ledger pins binary and proof hashes. Archive that temporary directory separately if long-term independent native replay is needed.

This pass supports only the three frozen 16-way sources, this host, this production/compiler/engine revision, and this collection method. V11 and V15 remain failed prospective scores. The unmodeled build/cold cost, 22.40% log-14 verifier RSS error, and one-host correlated PoW data prevent a claim of broadly reliable whole-prover forecasting, a Cairo speedup, or cryptographic soundness from this experiment.
