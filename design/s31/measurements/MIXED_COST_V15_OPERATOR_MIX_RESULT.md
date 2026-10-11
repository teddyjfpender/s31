# V15 mixed-operator cost challenge: frozen score failed

The prospective V15 run at frozen isolated commit `c3265b8746ff1383d5bc92517179dc872f69f84e` completed on the same pinned production compiler/engine/host and `/usr/bin/time` wall/RSS method as V12–V14. Protocol SHA-256 is `a1ae39d2cfc8aae0bf0022874c8d07639da4cc24502914a492e89c28befa837f`; model SHA-256 is `510aa16f133708fad7a97c96b9744665af002d8f89e06ad2fe92e0deca6bed73`. The protocol, model, source JSON, claims, schedule, gates, runner, and audit were committed before the first V15 native build. Independent static preflight passed. No source or model was selected, refit, or rerun after observing native results.

**Result: FAIL.** All three frozen sources passed exact native log-13/component admission and produced 20 interleaved scored proofs each. Every proof passed its native verifier and its ABI-valid changed-result control failed at the specified interaction nonce. The independent audit recomputed the exact score from saved files, checked all 66 source/claim/proof/report sets and timing endpoints, and replayed 66 honest plus 66 changed-result native verifier calls. It returned exit 0 while preserving `all_gates_pass: false`.

| Source | Wall median observed / predicted | Wall interval hits | Non-PoW median error | Proof median observed / predicted | Proof interval hits | Prover RSS error | Largest native phase error |
|---|---:|---:|---:|---:|---:|---:|---:|
| `wide_addheavy_n1` | 202.60 / 213.40 ms | 19/20 | 0.23% | 152,822.5 / 164,860 B | **5/20** | 10.96% | 10.78% |
| `wide_mix_n1` | 192.59 / 213.40 ms | 19/20 | 0.08% | 153,107.5 / 164,860 B | **5/20** | 9.07% | 8.78% |
| `wide_mix_n2` | 191.58 / 214.19 ms | 19/20 | 0.40% | 167,669.5 / 180,505.4 B | **7/20** | 9.54% | 13.73% |

Each source fails only the **proof interval coverage** gate, which required at least **16/20** hits. The frozen N1 proof band was 154,206–175,514 B; the N2 band was 168,841–192,170 B. Observed proof medians are 7.66–7.88% below centers. The separately frozen proof-median relative-error gate was 10%, so it passed; the V12-inherited interval half-width was narrower, and its coverage failed decisively. This specifically falsifies the proof-size uncertainty transfer for this wide mixed-op circuit topology. It does not justify widening the V15 interval after scoring.

All three source wall-median errors were 5.33%, 10.81%, and 11.80% versus the ≤30% gate; pooled wall one-draw coverage was 57/60 versus ≥49/60, and all three observed sample medians lay in their frozen bands versus ≥2/3. Each non-PoW whole-process residual error was below 0.4% versus ≤20%. Each of the four native package-stage errors was below 13.8% versus ≤30%. Prover and verifier RSS gates, proof-median errors, and honest/negative proof controls also passed. These passing subgates are useful diagnostic evidence, **not a passing whole-prover model**.

## Build and cold cost, descriptive only

| Source | Package build wall | First post-build verified wall | Immediate same-claim repeat |
|---|---:|---:|---:|
| `wide_addheavy_n1` | 78.48 s | 1.020 s | 210.07 ms |
| `wide_mix_n1` | 74.24 s | 1.043 s | 204.26 ms |
| `wide_mix_n2` | 74.48 s | 1.009 s | 183.62 ms |

One-shot builds and the first post-build claim were prespecified descriptive measurements with **no prediction gates** because the earlier data do not identify compiler-cache or cold-start effects. They matter materially to deployment cost: roughly 74–78 seconds per package on this host, and a roughly one-second first verified process invocation. They cannot be merged into the scored warm medians or called forecast successes.

## Interpretation and retained limits

The V15 predictor assigned the same per-operation marginal cost to packed adds and multiplications, and reused an earlier log/proof coefficient across a larger eight-way fanout. Observed N1 proof sizes were close for the 1:3 and 1:7 multiplication/addition mixes, while both were systematically below the common predicted interval. This points to the structural proof baseline or interval calibration as the failed assumption; the experiment does not isolate a causal add-versus-multiply proof cost. The extra long call increased observed median proof size by about 14.6 KB, close to but below the predicted 15.6 KB increment.

V11 remains a failed frozen challenge, V12–V14 remain local passes, and V15 is a failed wider-topology challenge. A revised proof-size rule must use V15 as declared training and face a new, genuinely unseen source/geometry holdout. The very close non-PoW and phase predictions here support further testing, but one host and related source families do not establish portable whole-prover reliability or a speedup claim.

The canonical artifacts are `language/mixed-cost-v15-operator-mix-{result,score,audit}.json`. Their SHA-256 digests are respectively `18d768888a485b4b067de70c2d86caa81c221f7e6a2428f071bb806879915a19`, `5511f5c4ea0c41bfa3f5c17d0ef9b2f1980d7ee27f933ec5f00b3db4e45fca8a`, and `0cf7830efdb6e9f917a77b1a5d860c15d955e3d652ea30a6d6d9699cd9b52864`. The saved raw packages, manifests, 66 proofs, native reports, and negative-control files are in `/tmp/s31-v15-operator-mix-3dc83f5/.v15-artifacts`; the result ledger pins binary and proof hashes. That temporary path must be archived separately if long-term native replay is needed.
