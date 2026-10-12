# V22 quiet-host six-call topology holdout: local pass

**The single preregistered native attempt passed every frozen gate.** The source and protocol were committed as `c7cc51b` and cherry-picked to PR commit `794f76c`, which was pushed before the native run. The protocol SHA-256 is `2a3ba103db66175a70e33265d33426e18f8c845cf41864ce7bc7141ebeb407de`; the pinned compiler base is `07cdb2100398132f2d1121f9d17c68836f0ae6ea`, with engine gitlink `fde847ea374ade2ae07ef5b3a42ba07e15655b64`. This was one Apple M5 Max host run. A `ps` snapshot immediately before the one-attempt marker found no Lean, lake, or other Zig process and is saved with the raw artifacts; its SHA-256 is bound into the marker. The snapshot establishes the start condition, not exclusive host control throughout the run.

## New source and native admission

The canonical source SHA-256 is `e26a2d293033f362e319fae45ba661e59fe037c3dc2cbb0e42ad5c89e5f9dfd0`. Its topology was not measured in V11–V21: three live branches with 1,536 arithmetic operations each, one multiplication every four steps, two join additions, and six ordered repeated-square chip calls of 2,048, 256, 4,096, 128, 1,024, and 512 rounds. The source-derived native manifest matched **6 ordered calls**, **13 component slots**, **125 constraints**, tree columns `[8, 114, 176, 8]`, and exact slot logs `[13, 11, 4, 8, 4, 12, 4, 7, 4, 10, 4, 9, 4]`. The manifest check also matched each source-derived call, registry slot field, chip/bridge role, node ID, constant, and consecutive four-lane address roster.

## Frozen forecast and observation

| Measure | Frozen forecast | Observed | Observed-relative error | Frozen maximum |
| --- | ---: | ---: | ---: | ---: |
| Package build | 78.172 s | 78.124 s | 0.061% | 25% |
| First post-build verified proof | 1.212 s | 1.340 s | 9.51% | 40% |
| Immediate same-claim verified repeat | 0.285 s | 0.228 s | 24.67% | 50% |
| Build plus 22 proof-process durations | 84.110 s | 84.455 s | 0.409% | 25% |
| 20 fresh-claim warm median | 222.022 ms | 209.789 ms | 5.83% | 35% |
| 20 fresh-claim proof median | 227,381 bytes | 227,445 bytes | 0.028% | 10% |

The frozen V18 model predicted a **153.687–514.929 ms** one-draw wall band. All **20/20** fresh wall draws fell inside it, as did the sample median inside its frozen sample-20 median band. All **20/20** proof sizes fell inside the frozen proof band. The non-PoW wall median error was 3.02%; the four package-stage median errors ranged from 2.42% to 5.98%. Every inherited V18 metric gate and V22 lifecycle gate passed.

All **22 honest proofs** were accepted by the generated native verifier. All **22 exact changed-result statements** were rejected at `InvalidMixedInteractionNonce`. The committed native audit checked source, claim, proof, binary, manifest, stage, timing, and quiet-host snapshot identities, independently recomputed the score, and replayed all **44 verifier calls**. It passed.

The measured 84.455 s is the sum of separately measured process durations and excludes idle gaps. The package build accounts for 92.50% of that sum, or 3.551 s amortized per proof at this 22-proof batch size. The first proof is the first proof process after package build and manifest inspection; it is not a controlled OS cold-cache measurement.

Canonical source, protocol, marker, result, score, and audit SHA-256 digests are respectively:

```text
e26a2d293033f362e319fae45ba661e59fe037c3dc2cbb0e42ad5c89e5f9dfd0
2a3ba103db66175a70e33265d33426e18f8c845cf41864ce7bc7141ebeb407de
8b7294a0d46398a0d2b23adfceba91e4167b33b457557eea34bd3d35ce66d26c
1de8896e6325efe67f448eb6f218b4a2460e99fd6501c2284a2aa5c0dfa03cb5
f6d96d36e2a276e9f35bd52b7a11951a7b9ccfc4f3814aa72e5ced20d0a74b6b
eb96d2a99e0fc73f5d00bae9815640586b6737c932fc013e17aa1ad8c6b3211e
```

Canonical records are in `design/s31/measurements/language/`; raw binaries, proofs, `quiet-host-preflight.ps`, and logs remain at `/private/tmp/s31-v22-quiet-holdout-artifacts-07cdb21`. Native replay requires separately archiving that directory. This is one local unseen-topology result. It does not establish cross-host calibration, automatic lowering quality, a Cairo speedup, or recovery from the V17 eight-call warm-model failure. The lifecycle point forecasts still use five previously measured one-host records and remain exploratory.
