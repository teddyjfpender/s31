# V21 unseen mixed topology holdout: local pass

**The one preregistered native attempt passed every frozen gate.** The protocol was committed as `518c54c`, then cherry-picked to the PR as `9fdcc35` and pushed before the native build. Its SHA-256 is `fc5b28ea6d6e98891c62c06862ea2e7983ef1d95802abb310d9764d35b68b7fd`. The pinned compiler base is `4c0872c9a654d0847e129f04e7662a0b1ee81efd`, with engine gitlink `fde847ea374ade2ae07ef5b3a42ba07e15655b64`, on the same Apple M5 Max host used for the prior local cost runs. The attempt marker was created before package build and records one completed attempt.

## New source and exact native admission

The canonical source SHA-256 is `97bb5a74a22112e950de6220823d44f782d93069ff6820d75118235130adaa24`. Its topology was not measured in V11–V20: four live branches with 1,024 arithmetic operations each, one multiplication every five branch steps, a balanced join, and five ordered repeated-square chip calls of 4,096, 512, 128, 2,048, and 256 rounds. The source-derived native manifest matched **5 ordered calls**, **11 component slots**, **106 constraints**, tree columns `[8, 97, 148, 8]`, and exact slot trace logs `[13, 12, 4, 9, 4, 7, 4, 11, 4, 8, 4]`. The manifest checker also matched every deterministic registry slot field, chip/bridge role, source and feeder node ID, call constant, and consecutive four-lane call addresses.

## Forecast against observed process durations

| Measure | Frozen forecast | Observed | Observed-relative error | Frozen maximum |
| --- | ---: | ---: | ---: | ---: |
| Package build | 78.172 s | 93.728 s | 16.60% | 25% |
| First post-build verified proof | 1.212 s | 0.971 s | 24.86% | 40% |
| Immediate same-claim verified repeat | 0.285 s | 0.281 s | 1.51% | 50% |
| Build plus 22 proof-process durations | 84.079 s | 99.979 s | 15.90% | 25% |
| 20 fresh-claim warm median | 220.485 ms | 243.133 ms | 9.32% | 35% |
| 20 fresh-claim proof median | 212,278 bytes | 210,450 bytes | 0.87% | 10% |

The V18 warm model predicted a **152.150–513.392 ms** one-draw wall band and a **191,377–233,178 byte** proof band. The observed warm wall median was in the frozen sample-20 median band; **19/20** wall draws were in the one-draw band and **20/20** proof sizes were in the proof band. The non-PoW wall median relative error was 3.22%; the largest of four package-stage median errors was 19.05%. Prover and external verifier peak-RSS median errors were 1.63% and 2.42%. Every inherited V18 metric gate and every V21 lifecycle gate passed.

All **22 honest proofs** were accepted by the generated external native verifier. All **22 exact changed-result statements** were rejected by that verifier at `InvalidMixedInteractionNonce`. The committed audit checked source, claim, proof, binary, manifest, stage, and timing identities, independently recomputed the warm score, and replayed all 44 verifier calls; it passed.

The measured 99.979 seconds is the **sum of separately measured process durations**, excluding idle gaps. The package build accounts for 93.75% of that sum, or 4.545 seconds amortized per proof at this 22-proof batch size. Build plus the first proof was 94.699 seconds. The first proof is the first proof process after build and manifest inspection, not a controlled OS cold-cache experiment.

**Host contention limits the timing inference.** During the ~01:01–01:03 UTC native attempt, a Lean `AxiomAudit` process and a `leanchecker` process were each consuming about one CPU core, and focused Zig tests overlapped. The preregistered protocol forbids a retry, so the result remains the one observed attempt. The mechanical accuracy gates passed under this contention, but the 16.60% build error and warm timing cannot be treated as a clean quiet-host transfer validation.

The canonical source, protocol, marker, result, score, and audit SHA-256 digests are respectively:

```text
97bb5a74a22112e950de6220823d44f782d93069ff6820d75118235130adaa24
fc5b28ea6d6e98891c62c06862ea2e7983ef1d95802abb310d9764d35b68b7fd
1502f0059388e994999da1a7e1bc1f0b676708ff6de6366d8dd01a9b00e883a7
db017f7f1a79d96d7938a343f1638d2a5f1313cc74d0d7c26f0437145e8f8c0d
59b22ac286b6e21fb3f5c20f9e47898bbc1910192185b8cc3d6ed107a8a3246e
3620903fa8331ad2894696284b94c8c334060a8113c983821b908f174fd95671
```

Canonical records are in `design/s31/measurements/language/`; raw binaries, proofs, and logs remain under `/private/tmp/s31-v21-unseen-topology-artifacts-4c0872c`. Native replay requires separately archiving that directory. This is one local unseen-topology success; it does not establish calibrated cross-host intervals, general automatic lowering choices, a Cairo speedup, or recovery from V17's eight-call warm-model failure. The lifecycle point forecasts inherit five previously measured one-host records and remain exploratory.
