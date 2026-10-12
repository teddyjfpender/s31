# Independent V21 unseen-topology cost audit (2026-10-12)

## Verdict and measurement limit

The frozen V21 one-attempt experiment **passes its committed mechanical gates**. This audit found no arithmetic, manifest, artifact-linkage, or verifier-control discrepancy. The run does **not** establish quiet-host cost accuracy: its package build and proof measurements overlapped with Lean axiom/kernel checks and focused Zig tests on the same machine. The 93.728 s observed build versus 78.172 s forecast is therefore a contended-host observation. The frozen protocol barred a retry, so this result is preserved rather than replaced with a favorable run.

The result supports only the measured five-call, four-branch topology on this host at the pinned compiler revision. It is not evidence for cross-host performance, arbitrary mixed programs, or a Cairo speedup.

## Frozen provenance

- PR preregistration `9fdcc35` was pushed before the native attempt. Its canonical protocol SHA-256 is `fc5b28ea6d6e98891c62c06862ea2e7983ef1d95802abb310d9764d35b68b7fd`; source SHA-256 is `97bb5a74a22112e950de6220823d44f782d93069ff6820d75118235130adaa24`.
- The native compiler inputs are pinned to S31 revision `4c0872c9a654d0847e129f04e7662a0b1ee81efd`, engine gitlink `fde847ea374ade2ae07ef5b3a42ba07e15655b64`, and the per-file SHA-256 roster in the protocol. Later changes on the PR branch were not measured. `freeze.py check-record` verifies the historical committed protocol; a strict current-stack `check` on the later PR HEAD is expected to fail.
- The raw result was committed as `653c48d`; the artifact directory is `/private/tmp/s31-v21-unseen-topology-artifacts-4c0872c`. Canonical result SHA-256 is `db017f7f1a79d96d7938a343f1638d2a5f1313cc74d0d7c26f0437145e8f8c0d`, score SHA-256 is `59b22ac286b6e21fb3f5c20f9e47898bbc1910192185b8cc3d6ed107a8a3246e`, and two-line one-attempt marker SHA-256 is `1502f0059388e994999da1a7e1bc1f0b676708ff6de6366d8dd01a9b00e883a7`.
- The protocol's forecasts independently reconstruct from the frozen V18 model and five earlier lifecycle observations, with matching hashes. Tool hashes and the pinned revision's file hashes match. The O_EXCL attempt marker precedes the native build.

## Independent checks

I read the committed protocol/result/score and raw artifact files directly, without importing the V21 scorer to compute the checks below.

1. Re-evaluated all 22 source executions from the 4,114-node JSON relation over M31, including all five repeat calls. Every output matched its public assignment and statement. There are 21 distinct frozen claims; claim zero is run twice to measure immediate repetition.
2. Matched all 22 assignment, statement, proof SHA-256, proof byte counts, emitted-statement files, and exact changed-result statements. Each changed statement increments only the first result lane by one. Raw recorded verifier stderr shows 22 honest acceptances and 22 `InvalidMixedInteractionNonce` rejections. Separately replayed the native verifier for `a14r0`: honest exit 0 with `verified`, changed-result exit 1 with `InvalidMixedInteractionNonce`. The producer's separate native audit replayed all 44 verifier calls.
3. Matched the manifest stdout hash, generated binary hashes, five ordered calls, 11 component slots, 106 constraints, trace logs, and four tree-column counts `[8, 97, 148, 8]` to the frozen protocol.
4. Recomputed warm wall, proof bytes, native phases, reported-PoW residual, RSS, interval coverage, package-stage medians, relative errors, and gate predicates from the 20 fresh claim rows. Recomputed the build, first-use, repeat, and build-plus-22-process-duration lifecycle metrics. All equal the committed score.

| Frozen measure | Forecast | Observed | Check |
| --- | ---: | ---: | --- |
| Warm verified wall median | 220.485 ms | 243.133 ms | 9.32% observed-denominator error; 19/20 one-draw wall bands |
| Proof median | 212,277.625 bytes | 210,450 bytes | 0.87% error; 20/20 proof bands |
| Build wall | 78.172 s | 93.728 s | 16.60% error; host contended |
| First verified proof after build | 1.212 s | 0.971 s | 24.86% error |
| Immediate repeat of same claim | 0.285 s | 0.281 s | 1.51% error |
| Build plus 22 proof-process durations | 84.079 s | 99.979 s | 15.90% error; excludes idle gaps |

The experiment's pass means these committed bounds held under the recorded run. Because other compiler and proof work competed for CPU during the attempt, the lifecycle result should not be used as a clean calibration point for a quiet-host whole-prover model. The next prospective holdout needs exclusive host time, a source/topology fixed before measurement, and the same one-attempt discipline.
