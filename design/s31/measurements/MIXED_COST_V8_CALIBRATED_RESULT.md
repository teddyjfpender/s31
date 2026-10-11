# Prospective V8 calibrated whole-prover transfer

**The single preregistered V8 run passes all eight gates.** This follows the
failed V5 and V7 transfers and the unscored V6 integrity failure. V8 uses a
new model fit from clean V4/V5/V7 evidence and entirely fresh source and
claim identities. There was no score-selected rerun or post-result refit.

The exact [model](language/mixed-cost-v8-calibrated-model.json),
[protocol](language/mixed-cost-v8-calibrated-protocol.json),
[source JSON](language/mixed-cost-v8-calibrated-sources/), and runner were
committed in `1a40c8f` before the first native package build. Model SHA-256
is `9ee6ff418843065db49d1015b06e24c65739f4e67d48f1eaf9d35c3e2792a35c`;
protocol SHA-256 is
`877e7cddf0a80dc18986231f217f362f81366ac4689d9deee47955923c48d8e6`.
The final compiler/runtime/tool/source pin check passed. The fixed gates are
the same as V7: at most 30% median wall error, at least 80% coverage of a
nominal 90% wall interval, at most 10% median proof-size error, and at least
80% coverage of a nominal 90% proof-size interval, for **each** source.

| Fresh source | Predicted wall p50 | Observed warm wall p50 | Median error | Wall interval coverage | Predicted proof center | Observed proof p50 | Proof median error | Proof interval coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `folded_seed_n1` | 90.29 ms | 96.37 ms | 6.32% | 76/80 = 95.0% | 70,007 B | 70,047 B | 0.057% | 79/80 = 98.75% |
| `braided_scan_n8` | 94.41 ms | 87.04 ms | 8.47% | 78/80 = 97.5% | 171,831 B | 172,155.5 B | 0.189% | 78/80 = 97.5% |

The frozen empirical source-rate median envelopes were 62.78–129.52 ms for
N=1 and 66.91–133.65 ms for N=8; both observed medians lie inside. These
envelopes are descriptive bounds from four training source rates, not
confidence intervals. The predicted nominal 90% wall intervals were
34.88–335.55 ms and 39.01–339.68 ms, respectively. Their high observed
coverage shows the model was conservative on this run; it does not establish
nominal coverage elsewhere. The proof half-widths were 5.869% for N=1 and
4.235% for N=8, also conservative on these claims.

## Native geometry and PoW decomposition

Both sources compiled to the preregistered mixed profile at 20-bit
interaction and 26-bit FRI PoW. Their manifests matched the frozen source
IDs, component geometry, constraint totals, column trees, and registry
manifest digests.

| Source | Calls / slots | Constraints | Tree columns | Max / composition log | FRI PoW p50 | Interaction PoW p50 | Non-PoW whole-wall p50 | Package build wall |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| `folded_seed_n1` | 1 / 3 | 30 | `[8, 29, 36, 8]` | 9 / 9 | 65.57 ms | 1.13 ms | 28.84 ms | 74.67 s |
| `braided_scan_n8` | 8 / 17 | 163 | `[8, 148, 232, 8]` | 9 / 9 | 49.66 ms | 1.29 ms | 35.21 ms | 74.26 s |

The N=8 cohort happened to have a lower median FRI PoW duration than N=1.
The model does not assume PoW cost grows with call count; the deterministic
non-PoW work does. First-post-build verified walls were 1,032 ms and 1,124
ms, and immediate same-claim repeats were 37.46 ms and 152.94 ms. Those
claim-zero observations and build times were descriptive, never scored.

## Verification, reproducibility, and limits

The [compact result](language/mixed-cost-v8-calibrated-result.json) SHA-256
is `6c2b36039ec9827aa6aeed61a93f2dce27f2d9eb9cbe70fff8b4a09098662500`.
It retains all 164 proof process pairs, source/claim/proof hashes, monotonic
endpoints, native stages/PoW phases, manifests, and build times. All **164
honest proofs** verified against their public statements; all **164 ABI-valid
changed public results** rejected at `InvalidMixedInteractionNonce`. The
independent [audit](language/mixed-cost-v8-calibrated-audit.json) checked
local source, binary, manifest, statement, and proof bytes, recomputed the
frozen [score](language/mixed-cost-v8-calibrated-score.json), and replayed
every saved proof and changed claim through the native verifier. The score
SHA-256 is `a7e789e771ca6f021900165b78f339a39b9a0352b3518f446b40859bb331df83`.
The raw replay bundle remains locally in `zig-out/s31-mixed-cost-v8-calibrated/`;
without it, a reviewer can check committed hashes and scoring logic but
cannot replay these particular stochastic proofs.

This is one prospective transfer on one host and one compiler/runtime stack.
Four recent PoW source blocks and four proof-width blocks per profile are too
few to establish general coverage or accuracy. The geometry remains
collinear with call count in this admitted profile; independently varying
geometry, changed PoW settings, process contention, host rate drift, and
other program families need new prospective tests. The run establishes no
Cairo speedup claim. V5 and V7 remain failed historical transfers.
