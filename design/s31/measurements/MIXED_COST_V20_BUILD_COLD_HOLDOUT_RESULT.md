# V20 build and first-use cost holdout: local pass

**The one preregistered native attempt passed every frozen gate.** The
protocol was committed first at `5d93582` (SHA-256
`80c8661bfd0d9a09faf4904194318161018bfbe8a99ed098c73548fdf4650d63`),
and the same preregistration was pushed to the PR as `ae2e14a` before the
native run,
then the one-attempt marker was created before the native package build. The
measured compiler base is `93114dfa53b9f8762d4da20a41b158992ce61de9`
with engine gitlink `fde847ea374ade2ae07ef5b3a42ba07e15655b64` on the
same Apple M5 Max host as V18/V19. The source is V18's
`calls6_log14_b8`, which has a different `log14` bundled trace from V19's
`calls6_log13_b8`; it is **not** a previously unseen topology.

## Frozen forecast against measured process durations

| Metric | Predicted | Observed | Observed-relative error | Frozen maximum |
| --- | ---: | ---: | ---: | ---: |
| One package build | 78.164 s | 78.172 s | 0.010% | 25% |
| First post-build verified proof | 1.184 s | 1.308 s | 9.44% | 40% |
| Immediate same-claim verified repeat | 0.291 s | 0.267 s | 8.81% | 50% |
| Build plus 22 verified proof-process durations | 86.060 s | 86.541 s | 0.56% | 25% |

The build/first/repeat centers are the componentwise medians of the four
already recorded V18/V19 lifecycle observations. The 22-process prediction
adds V18's frozen `321.025 ms` warm center for 20 fresh claims. The observed
20-claim warm median was `336.155 ms`, a 4.50% error; 19/20 draws fell in
the frozen wall interval, the sample median was in its frozen band, and all
20 proof sizes fell in the frozen proof interval. The observed proof-size
median was 254,442.5 bytes versus 251,990.25 predicted (0.96% error).
Non-PoW process wall error was 1.46%; prover and verifier peak-RSS median
errors were 2.35% and 2.88%; the largest of four native package-stage
median errors was 3.79%. All inherited V18 warm gates and the V20 lifecycle
gates passed.

The exact source-derived native admission passed before proofs: six ordered
chip calls, 13 slots, 125 constraints, tree columns `[8, 114, 176, 8]`,
and frozen slot trace logs `[14, 12, 4, 10, 4, 8, 4, 6, 4, 11, 4, 9, 4]`.
All 22 honest proofs, including first and repeat, were accepted by the
external verifier. All 22 exact changed-result statements were rejected at
`InvalidMixedInteractionNonce`. The committed audit recomputed raw source,
claim, proof, binary, manifest, stage, and timing identities and independently
replayed all 44 verifier calls; it passed.

The measured 86.541 seconds is a **sum of separately measured process
durations**, with idle gaps omitted. It corresponds to 3.934 seconds per
proof at this 22-proof batch size; the one package build accounts for 90.33%
of that sum. Build plus the first proof alone was 79.480 seconds. The first
proof is the first proof process after the package build and manifest
inspection; it is not a controlled OS cold-cache experiment.

The canonical result, score, attempt, and audit SHA-256 digests are,
respectively,
`7b8c30b30fd24691110510d485da84b0906d70a87d468cad3e9efde8cf2bf8f8`,
`7071a44623175051eb3302132ae2d1a25845f32e3dfe9a3e9d6fd8ef3c1bdbbf`,
`34e30162b978b657f2e9284e664c3a2cd03b773043ebf43f1245cf91f1c506e4`,
and `bb395472a7ac458883e83b3236102c8ab6246215d9a8420d23b91c346647ba74`.
The canonical protocol, marker, result, score, and audit are in
`design/s31/measurements/language/`. Raw proofs and binaries remain under
`/private/tmp/s31-v20-build-cold-holdout-93114df-artifacts`; preserving native
replay requires separately archiving this directory.

This pass supports a one-host prospective build/first-use prediction for this
previously measured source and current compiler revision. Four prior
lifecycle observations and one target run do not establish calibrated
intervals, cross-host reliability, unseen-topology accuracy, cold-cache
behavior, or a Cairo speedup. V17's N8 warm-model failure remains a failure.
