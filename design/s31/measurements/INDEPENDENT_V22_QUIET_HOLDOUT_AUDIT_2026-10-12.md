# Independent V22 quiet-host holdout audit

**Verdict:** The frozen V22 one-attempt run passes its committed mechanical gates. I found no discrepancy in the frozen input, source arithmetic, artifact identities, manifest geometry, score arithmetic, or a direct honest/changed verifier replay. This is evidence for one new source on one host, not a general cost guarantee.

## Frozen input and native attempt

- The pushed preregistration commit is `794f76c`; its canonical protocol SHA-256 is `2a3ba103db66175a70e33265d33426e18f8c845cf41864ce7bc7141ebeb407de`. The protocol and source bytes match the frozen regeneration check. The source has three 1,536-step arithmetic branches (4,608 branch operations), two joins, and six ordered repeated-square calls with rounds 2,048, 256, 4,096, 128, 1,024, and 512. An independent generic evaluation of the source reproduced all 21 frozen assignment hashes.
- The recorded `ps` snapshot SHA-256 is `4793eaac130931f9bbd251ec6000507291f9a7f191b636ea7a6df41dbdc5b4f8`; its executable-name column contains no Lean, lake, or Zig process. The attempt marker has one start and one completed event. The result SHA-256 is `1de8896e6325efe67f448eb6f218b4a2460e99fd6501c2284a2aa5c0dfa03cb5`; the score SHA-256 is `f6d96d36e2a276e9f35bd52b7a11951a7b9ccfc4f3814aa72e5ced20d0a74b6b`.
- The native manifest has the frozen six calls, 13 slots, 125 constraints, tree columns `[8, 114, 176, 8]`, and trace logs `[13, 11, 4, 8, 4, 12, 4, 7, 4, 10, 4, 9, 4]`. Its source identity and the generated verifier binary hash match the recorded artifacts. I checked every one of the 22 proof, assignment, statement, emitted statement, changed-result, and process-duration records against the raw files. All 22 stored honest verifier logs say `verified`; all 22 stored changed-result logs say `InvalidMixedInteractionNonce`. A fresh direct replay of claim `a00r0` gave exit 0 and `verified` for the honest statement, then exit 1 and `InvalidMixedInteractionNonce` for the changed result.

## Independent score arithmetic

The frozen warm forecast is 222.022 ms; the observed 20-claim median is 209.789 ms, a 5.83% relative error using the observed value as denominator. All 20 warm walls fall in the frozen one-draw band, and all 20 proof sizes fall in the frozen interval. The observed proof median is 227,445 bytes versus 227,381.25 predicted. The non-PoW wall median error is 3.02%; the largest reported native package-stage median error is 5.98%. The recorded RSS median errors are 4.29% for the prover and 0.54% for the verifier.

The build took 78.124 s versus 78.172 s forecast (0.061% relative error). The first verified proof took 1.340 s versus 1.212 s forecast; the immediate same-claim repeat took 0.228 s versus 0.285 s forecast. The build plus 22 separately measured verified-proof process durations totals 84.455 s versus 84.110 s forecast (0.41% relative error); build accounts for 92.50% of that measured sum. Recomputing the median, interval hits, proof sizes, lifecycle sum, and relative errors from the raw trial records agrees with the committed score. The producer's full 44-call native replay is separately recorded in the audit artifact; my independent replay sampled one honest/changed pair.

## Limits

The preflight snapshot checks one instant and does not prove exclusive CPU use throughout the attempt. The first post-build process is an immediate first use, not a controlled operating-system cold-cache experiment. The lifecycle total sums measured process durations and excludes idle gaps. The model transfers to this one new topology on this host; cross-host reliability, automatic lowering choice, a Cairo comparison, and the preserved V17 eight-call miss remain open.
