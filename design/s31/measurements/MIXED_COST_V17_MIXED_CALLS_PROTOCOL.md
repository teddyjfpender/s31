# V17 prospective mixed-length N4/N8 chip-call cost challenge

Status: **pre-native frozen candidate**. This model, protocol, exact source/claim bytes, runner, audit, and design must be committed and independently preflighted before any V17 native build. Only one scored native run is permitted. Preserve an unsupported geometry, control failure, or failed score unchanged.

## Fresh computation and native admission

Each program takes one public four-lane M31 input, feeds 16 shifted/scaled seeds, and follows 16 live chains of 256 or 512 add/multiply operations. At position `i` on branch `b`, the chain multiplies by that branch's fixed shift when `(i+b) mod 5 = 0`; otherwise it adds the shift. A balanced four-level addition tree combines the branches. Four or eight sequential chip recurrences of differing power-of-two round lengths follow, then the public output scales the final recurrence value and adds the first branch shift. Every chain and call reaches the output.

For example, branch zero of `calls4_log13` starts `shift0 = x + 401`, `seed0 = 43 * shift0` modulo `p = 2^31−1`. Its first loop step multiplies `seed0 * shift0`, the next four add `shift0`, and the sixth multiplies again. After the 16-way join, call zero applies `z <- z² + 257` for 4,096 rounds; calls one to three apply the same recurrence with their own constants for 1,024, 256, and 64 rounds. An independent Python M31 oracle evaluates all four lanes for all 21 claim inputs/source and checks the source interpreter before freeze.

| New source | Live operations (mul/add) | Sequential chip rounds | Expected slot trace logs | Constraints |
|---|---:|---|---|---:|
| `calls4_log13` | 4,096 (820/3,276) | 4,096, 1,024, 256, 64 | `[13,12,4,10,4,8,4,6,4]` | 87 |
| `calls8_log13` | 4,096 (820/3,276) | 4,096, 2,048, 1,024, 512, 256, 128, 64, 32 | `[13,12,4,11,4,10,4,9,4,8,4,7,4,6,4,5,4]` | 163 |
| `calls4_log14` | 8,192 (1,639/6,553) | 4,096, 1,024, 256, 64 | `[14,12,4,10,4,8,4,6,4]` | 87 |

V16 already admitted a log-14 circuit, but neither eight mixed-length calls nor these V17 sources have native admission evidence. All 126 new assignment/statement digests and three source digests are disjoint from declared V4–V16 evidence. The frozen runner builds all packages and checks each native manifest **before any proof** for exact source hash, call count/rounds, slots/logs, tree columns, constraints, max/composition log, registry digest, and interaction/FRI PoW bits 20/26. A mismatch ends the single run; no source is dropped or substituted.

## Prospective model

V11 and V15 failed; V12, V13, V14, and V16 passed their frozen local gates. All six ledgers are declared V17 training evidence, with their exact SHA-256 input hashes in the canonical model. The matched baseline for circuit log 13 or 14 is respectively V16 `fanout16_log13_n1` or `fanout16_log14_n1` scored medians. The extra *short-call* step is the positive part of `(V13 fork_joint_n4 − fork_joint_n1)/3`, reflecting three extra 32/16/64-round components. The extra *long-call* step is the positive part of `V16 fanout16_log13_n2 − fanout16_log13_n1`, reflecting an extra 4,096-round component. Small negative measured differences are set to zero because the model assumes an added component cannot reduce algorithmic work; this rule is frozen before V17 timing.

For each extra call of `r` rounds, `alpha = clamp((log2(r)−6)/6, 0, 1)` and the model adds `(1−alpha) * short_step + alpha * long_step` independently to warm non-PoW process wall, proof bytes, prover/verifier RSS, and four native package-stage centers. Thus a 64- or 32-round call uses the short step, a 4,096-round call uses the long step, and the intermediate rounds interpolate. The explicit falsifiable hypothesis is that these incremental costs add across N4/N8 components and transfer to the one-fifth multiplication circuit and log-14 base without a new cross-call premium. V13 and V16 sources differ in constants/topology, and per-call effects are not causally identified.

The fixed proof-size relative half-width remains V16's **9.846%**, which was calibrated using V15's failed proof interval before V16 was run. V17 does not widen it after seeing N4/N8 data. The separate proof-median gate remains ≤10% error. Whole verified wall one-draw and sample-of-20 bands add the predicted non-PoW center to V12's unchanged stochastic PoW/residual simulation. FRI and interaction PoW bands are retained separately. Fresh prover plus external verifier wall is collected under `/usr/bin/time` for OS peak RSS, the same method as V12–V16. The non-PoW residual subtracts native-reported FRI and interaction PoW from that process wall.

| Source | Frozen wall one-draw p50 | Non-PoW center | Proof center | Prover / verifier RSS centers |
|---|---:|---:|---:|---:|
| N4 log13 | 218.88 ms | 144.13 ms | 197,471 B | 24.94 / 15.15 MB |
| N8 log13 | 224.41 ms | 149.66 ms | 258,336 B | 25.69 / 15.23 MB |
| N4 log14 | 316.62 ms | 241.87 ms | 222,904 B | 38.11 / 21.75 MB |

The canonical protocol contains all exact predictions, phase centers, intervals, source/claim hashes, and pins: production source commit `7e90b5833eecb893c6db5f260e5d1cfc69cd230f`, compiler fingerprint, engine gitlink, host equality with V12, and transfer-tool hashes. **Package build and cold-start costs have no defensible prediction gate**: each earlier source has only one build and claim-zero first/repeat observations, confounded by compiler cache and process state. V17 records one build wall and claim-zero first/immediate repeat per source separately and reports them regardless of score.

## Single run, controls, and conjunctive gates

After all three packages pass native manifest admission, claim zero is proved twice/source for descriptive first/repeat cost. Claim indices 1–20/source are shuffled into 60 interleaved scored tasks using seed `202610130173`. Every proof must emit its exact public statement, pass a native external verifier, and reject an exact ABI-valid changed public result at `InvalidMixedInteractionNonce`. The independent audit checks saved binaries, sources, claims, proofs, native reports, physical timing endpoints/order, and can replay all 66 honest plus 66 negative verifier calls.

Frozen gates are conjunctive: per-source whole verified wall median relative error ≤30%; nominal 90% one-draw wall interval hits ≥14/20/source and ≥49/60 pooled; observed sample-of-20 wall median in its frozen 90% band for ≥2/3 sources; non-PoW median relative error ≤20%; each of four native package-stage median relative errors ≤30%; proof median relative error ≤10%; proof interval hits ≥16/20/source; prover and verifier median peak-RSS relative errors ≤30% each. Admission and proof-control failures fail the study. Build/cold costs are descriptive, with no gate.

A passing score would be evidence only for these three sources on this pinned host/compiler/engine/method. The V11/V15 failures, broad PoW intervals, unresolved build/cold model, and three related V17 source families prevent any general whole-prover reliability, speedup, or cryptographic-soundness claim.
