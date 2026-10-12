# V15 prospective mixed-operator whole-prover cost challenge

Status: **pre-native frozen candidate**. Commit the canonical model, protocol, three exact source files, runner, audit, and this design before building V15 native packages. The independent preflight must verify that commit. No V15 native build or timing has contributed to the model. Preserve any native admission failure or scored failure unchanged.

## Source and admission

Each program takes one public four-lane M31 input. It creates eight distinct shifted/scaled feeders; each feeder follows a live 512-operation chain; the eight chains join through a balanced three-level addition tree. A sequential SHA-like *arithmetic* chip-call recurrence then runs 4,096 rounds once or twice, followed by a scaled public result. This is **not SHA**. Every arithmetic node contributes to the public result. A separate Python M31 oracle computes all four lanes of all 21 claim inputs per source and checks agreement with the source interpreter before freeze.

For one lane, the first branch begins with `shift0 = x + 401` and `seed0 = shift0 * 43` in `wide_mix_n1`. Its first loop step multiplies `seed0 * shift0` because `(index + branch) mod 4 = 0`; the next three steps add `shift0`. Other branches use distinct constants, and every result reaches the final join. The add-heavy source uses multiplication every eighth step. All arithmetic is modulo `2^31−1`.

| Source | Live chain operations | Multiplications | Additions | Sequential chip rounds | Expected slot logs | Constraints |
|---|---:|---:|---:|---|---|---:|
| `wide_mix_n1` | 4,096 | 1,024 | 3,072 | 4,096 | `[13,12,4]` | 30 |
| `wide_addheavy_n1` | 4,096 | 512 | 3,584 | 4,096 | `[13,12,4]` | 30 |
| `wide_mix_n2` | 4,096 | 1,024 | 3,072 | 4,096 + 4,096 | `[13,12,4,12,4]` | 49 |

The exact source/claim digests and schedule are in `language/mixed-cost-v15-operator-mix-protocol.json`. They are disjoint from declared V4–V14 source/claim digests. The *expected* circuit log 13 is a frozen admission claim, not an observation. The runner builds all three packages, then checks the native manifests for exact source digest, call count/rounds, slot trace logs, tree columns, constraints, composition/max log, registry digest, and PoW bits 20/26 **before producing any proof**. An unsupported geometry stops the one frozen run; it cannot be exchanged for an easier source.

## Predeclared prediction

V11's frozen unseen-geometry score **failed** 14/16; V12's, V13's, and V14's local prospective scores passed. V15 openly treats the V11–V14 scored ledgers as training data. V15 does not refit V12's stochastic PoW simulation or its proof interval width. Source/claim hashes and exact input-ledger hashes are pinned in the model.

The base medians are V13 `fork_joint_n1` (two live 1,024-multiplication branches). The structural increment per 1,024 further live operations is the positive part of V12 `circuit_cascade_n1` minus V11 `gate_surge_n1`, except proof bytes use V12's previously frozen `gate_surge_n1` proof-log coefficient. Two such increments forecast V15's additional 2,048 live operations. The extra-call increment is the positive median of V14 N2 minus V13 N1 and half V14 N3 minus V13 N1. This rule is applied independently to warm process non-PoW residual, proof bytes, prover/verifier RSS, and four native package stages. PoW one-draw and sample-of-20 bands are copied from V12 and translated by each predicted non-PoW center. FRI/interaction PoW phase bands remain separately reported.

This rule explicitly hypothesizes that a live packed add costs the same marginal amount as a live packed multiply, and that an eight-way fanout carries no further premium at fixed 4,096-node/log-13 geometry. V11/V12 constants and geometry differ, so their contrast is confounded; the rule is a falsifiable extrapolation, not an identified causal cost. It predicts identical N1 cost for the 1:3 and 1:7 multiplication/addition mixes. The frozen centers are:

| Source | Whole verified process wall p50 | Non-PoW residual p50 | Proof center | Prover RSS center |
|---|---:|---:|---:|---:|
| `wide_mix_n1` | 213.40 ms | 138.65 ms | 164,860 B | 26.70 MB |
| `wide_addheavy_n1` | 213.40 ms | 138.65 ms | 164,860 B | 26.70 MB |
| `wide_mix_n2` | 214.19 ms | 139.44 ms | 180,505 B | 27.53 MB |

The four N1 native package-stage center predictions are topology compile 7.79 ms, witness compile 8.41 ms, profile rebuild 22.35 ms, and semantic evaluation 2.27 ms. Every numeric quantile and source-specific stage center is frozen in the canonical protocol. Whole wall is fresh prover process plus fresh external native verifier process wrapped with `/usr/bin/time` for OS peak RSS, the same collection method as V12–V14. The non-PoW residual subtracts native-reported FRI and interaction PoW durations from that measured wall. It is a diagnostic decomposition; reported phases need not sum perfectly to process wall.

One package build per source and claim-zero first/repeat are recorded separately and excluded from the warm score. One-shot build and cold starts are confounded by compiler cache and process state. **There is no defensible frozen build/cold prediction gate**. This limits any claim of a reliable whole-prover cost model.

## Single run, controls, gates

The exact production source-base commit is `7e90b5833eecb893c6db5f260e5d1cfc69cd230f`; the protocol pins compiler/runtime/tool hashes and requires the same host, Zig fingerprint, and engine gitlink as V12. Claim 0 is proved twice per source for descriptive cold/repeat cost. Scored claim indices 1–20 per source are shuffled into 60 interleaved trials with seed `202610130013`. Each trial must emit its exact public statement, pass the external native verifier, and reject the ABI-valid changed public result at `InvalidMixedInteractionNonce`. The independent audit checks saved binary/source/claim/proof hashes, native phase reports, physical schedule, score arithmetic, and can replay 66 honest plus 66 negative verifier calls.

All gates are conjunctive and frozen before native builds:

| Per-source gate | Threshold |
|---|---:|
| Whole verified wall median relative error | ≤30% |
| Nominal 90% one-draw wall interval hits | ≥14/20 |
| Observed sample-of-20 wall median in frozen 90% median band | ≥2/3 sources |
| Pooled nominal 90% one-draw wall interval hits | ≥49/60 |
| Non-PoW whole-process residual median relative error | ≤20% |
| Each of four native package-stage median relative errors | ≤30% |
| Proof-byte median relative error | ≤10% |
| Proof-byte interval hits | ≥16/20 |
| Prover and verifier median peak-RSS relative errors | ≤30% each |

Wall intervals are broad because PoW variance is large; coverage alone is weak evidence. A pass supports only this host, revision, measurement method, and source roster. It does not establish broad cost reliability, a speedup claim, or cryptographic soundness.
