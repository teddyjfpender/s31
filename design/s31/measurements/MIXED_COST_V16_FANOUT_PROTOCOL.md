# V16 prospective sixteen-way fanout and log-14 cost challenge

Status: **pre-native frozen candidate**. Commit the exact model, protocol, three source files, runner, independent audit, and this design before any V16 native package build. An independent reviewer must check the committed hashes and static tests before the one scored run. Preserve a native admission failure or any failed scored gate unchanged.

## Why this holdout

V15's wider eight-way circuit falsified the inherited proof-size interval: only 5/20, 5/20, and 7/20 proofs fell in their frozen intervals, below the 16/20 gate. V11 also failed a frozen wall gate. V12–V14 passed local frozen challenges. V16 declares all five ledgers as training, including both failures, and tests **new source hashes, claims, a sixteen-way topology, a 1:2 multiplication/addition mix, and a circuit log-14 source**. V16 native results do not enter its own model. A pass would still be local to one host and compiler/engine revision.

## Source arithmetic and geometry

One public four-lane M31 input feeds 16 shifted/scaled seeds. Each seed follows a live chain of 256 or 512 operations. At each position `i` and branch `b`, the chain multiplies by its branch shift when `(i+b) mod 3 = 0` and otherwise adds the shift. A balanced four-level addition tree combines the 16 branches, then one or two sequential 4,096-round chip recurrences run. The public result scales that value and adds the first branch shift. Every chain contributes to the result.

For example, in `fanout16_log13_n1` branch zero starts with `shift0 = x + 401` and `seed0 = 43 * shift0` modulo `p = 2^31−1`. Its first operation is `seed0 * shift0`; its next two add `shift0`; the fourth multiplies by `shift0` again. Branch one has different constants and phase. The independent Python M31 oracle evaluates all four lanes of all 21 claim inputs per source and checks agreement with the source interpreter before freezing.

| Fresh source | Live add/mul operations | Multiplications / additions | Chip rounds | Frozen expected slot logs | Constraints |
|---|---:|---:|---|---|---:|
| `fanout16_log13_n1` | 4,096 | 1,366 / 2,730 | 4,096 | `[13,12,4]` | 30 |
| `fanout16_log13_n2` | 4,096 | 1,366 / 2,730 | 4,096 + 4,096 | `[13,12,4,12,4]` | 49 |
| `fanout16_log14_n1` | 8,192 | 2,731 / 5,461 | 4,096 | `[14,12,4]` | 30 |

The exact sources and all 126 assignment/statement hashes are disjoint from previous declared source/claim hashes. Native manifest admission is **exact** before any proof: source hash, call count/rounds, slot logs/counts, tree columns, constraints, max/composition log, registry digest, and interaction/FRI PoW bits 20/26 must match. These logs are predictions until native inspection. If log 14 is unsupported or the compiler chooses another geometry, the single frozen study fails admission; no source is swapped.

## Frozen prediction rule

The matched log-13 N1 baseline is the mean of V15 `wide_mix_n1` and `wide_addheavy_n1` scored medians, applied independently to warm whole-process non-PoW residual, proof bytes, prover/verifier RSS, and four reported native package stages. The extra-call increment is V15 `wide_mix_n2` minus `wide_mix_n1` (a signed observed difference). For the log-14 source, the log-13 baseline is increased by V15 N1 mean minus V13 `fork_joint_n1`: **twice** that difference for non-PoW residual, package phases, and RSS because live operations rise by 4,096 versus the 2,048-operation V13→V15 contrast; **once** for proof bytes because the circuit trace grows by one log step. This is a stated extrapolation, not a causal cost estimate. The new 16-way fanout and operation ratio may break it.

V15's missed proof bands motivate a predeclared recalibration: the V16 proof relative half-width is the maximum of V12's frozen width, 1.25 times the worst V15 proof-center relative miss, and 1.5 times the worst V15 within-source proof deviation from its median. A 15% cap is enforced before freeze. The resulting fixed half-width is **9.846%**, versus V12's narrower width; it is not changed after V16 scoring. The separate proof median gate remains 10%, and the interval still must cover 16/20 proofs per source. This tests whether the V15-informed uncertainty transfers to genuinely unseen topology and log size; a wider interval alone is weak evidence.

Wall one-draw and sample-of-20 median distributions add the frozen non-PoW center to V12's unchanged stochastic PoW/residual simulation. FRI and interaction PoW are reported separately. The measurement is fresh prover-process plus fresh external-verifier-process wall under `/usr/bin/time` for peak OS RSS, the same method as V12–V15. The non-PoW residual subtracts reported FRI and interaction PoW durations from that process wall.

| Source | Predicted whole-wall one-draw p50 | Predicted non-PoW residual | Proof center / band | Prover RSS center |
|---|---:|---:|---:|---:|
| Log-13 N1 | 213.50 ms | 138.75 ms | 152,965 B / 137,904–168,026 B | 24.27 MB |
| Log-13 N2 | 214.96 ms | 140.21 ms | 167,527 B / 151,032–184,022 B | 24.92 MB |
| Log-14 N1 | 306.15 ms | 231.40 ms | 178,319 B / 160,762–195,876 B | 37.76 MB |

All exact phase centers and distribution quantiles are in the canonical model/protocol JSON. The protocol pins production source commit `7e90b5833eecb893c6db5f260e5d1cfc69cd230f`, tool/source hashes, compiler fingerprint, engine gitlink, and host equality with V12. There is **no defensible build or cold-start prediction gate**: one package build/source and first-post-build claim observations are confounded by cache and cold process state, as V15's 74–78-second packages and one-second first invocations showed. V16 records package build wall and claim-zero first/repeat separately, outside the warm score, and reports them even if the score fails.

## Single run, controls, and gates

All three packages are built and exactly manifested before any proof. Claim zero is proved twice per source for descriptive cold/repeat cost. Claim indices 1–20/source are shuffled into 60 interleaved scored tasks with seed `202610130163`. Each proof must emit the exact public statement, pass the native verifier, and reject an exact ABI-valid changed public result at `InvalidMixedInteractionNonce`. The independent audit recomputes metrics from saved artifacts and can replay 66 honest and 66 negative verifier calls.

All gates are conjunctive: each source wall median relative error ≤30%; nominal 90% one-draw wall hits ≥14/20/source and ≥49/60 pooled; observed sample-of-20 median in its frozen 90% band for ≥2/3 sources; non-PoW median relative error ≤20%; each of four native package-stage median relative errors ≤30%; proof median relative error ≤10%; proof interval hits ≥16/20/source; prover and verifier median peak-RSS relative errors ≤30% each. A native admission/control failure also fails the study. Build and cold costs are descriptive, with no gate.

The PoW intervals are broad, and three related sources on one host cannot establish general whole-prover reliability, speedup over another language, or cryptographic soundness. A failed V16 score must remain visible alongside the earlier passes and failures.
