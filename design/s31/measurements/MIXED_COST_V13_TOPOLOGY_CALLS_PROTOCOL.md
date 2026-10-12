# V13 prospective topology and call-count challenge

Status: **pre-native frozen candidate**. Commit the canonical protocol, rule, new sources, scripts, and this document before the first V13 native package build. The V11 failed score and V12 passed score remain unchanged. V13 tests whether V12's local log-12 transfer extends to a different circuit graph and three or four chip calls; it is not a refit of V12.

## New source family and admission

V12's log-12 circuit examples used one serial chain of 2,048 live packed M31 multiplications. V13 has **two live branches of 1,024 multiplications each**, interleaved in the source graph and joined by one addition before the chip calls. The left branch periodically squares and otherwise multiplies by a shifted public input; the right branch uses a distinct shifted input and a different squaring cadence. Both branches are needed for the public output. Independent Python arithmetic evaluates each claim over `p = 2³¹−1`, four lanes at a time.

| Frozen source | Live packed `mul` nodes | Sequential chip rounds | Expected native slot trace logs | Constraints |
|---|---:|---|---|---:|
| `fork_joint_n1` | 2,048 | 4,096 | `[12,12,4]` | 30 |
| `fork_joint_n3` | 2,048 | 4,096, 32, 16 | `[12,12,4,5,4,4,4]` | 68 |
| `fork_joint_n4` | 2,048 | 4,096, 32, 16, 64 | `[12,12,4,5,4,4,4,6,4]` | 87 |

These logs are **predictions of geometry**, not assumed facts. Before any scored proof, every compiled native manifest must exactly match frozen source digest, call/round list, slots/logs, tree-column widths, constraint count, composition and max-column log 12, registry digest, and 20/26 interaction/FRI PoW bits. If N3/N4 is unsupported or the compiler produces a different geometry, V13 fails admission; no source swap, gate adjustment, or after-the-fact selection is allowed. Sources and 21 claims per source are new and hash-disjoint from V4–V12.

## Predictor without V12 refitting

V13 reads the **frozen V12 protocol predictions** and unchanged V12 model bytes. The V12 result and score are read only to check their hashes and label the earlier score as passed, **excluded** from V13 prediction training. No observed V12 wall, proof, or RSS value appears in the V13 rule. V11's frozen failure remains an input to the unchanged V12 model as already declared in V12.

The base prediction for every forked source is V12's frozen `joint_cascade_n1` prediction. This sets a **zero topology premium** at the same log-12 circuit/chip geometry, a falsifiable hypothesis. For each call beyond one, V13 adds the positive part of the frozen V12 `serial_spiral_n2 − chip_spiral_n1` prediction difference to non-PoW wall, proof bytes, prover RSS, and verifier RSS. FRI and interaction PoW predictive distributions are reused unchanged because the configured proof-level nonce search is unchanged. The proof interval retains V12's fixed relative width. The rule is weak for N3/N4: V12's non-PoW N2-minus-N1 prediction difference is negative, so its positive part is **zero**. V13 therefore predicts **154.11 ms** warm whole-verified wall median for N1, N3, and N4; it may fail if additional calls add material process work. This is a predeclared limitation, not a post-hoc adjustment.

| Source | Frozen wall one-draw median | Frozen proof center | Frozen prover RSS center |
|---|---:|---:|---:|
| N1 | 154.11 ms | 128,189.5 B | 15.41 MB |
| N3 | 154.11 ms | 161,471.5 B | 15.47 MB |
| N4 | 154.11 ms | 178,112.5 B | 15.51 MB |

The exact per-draw 5–95% wall/PoW bands and sample-of-20 median bands are in the canonical protocol. The PoW simulation algorithm, seed, host-method assumptions, proof/RSS intervals, and phase predictions are inherited byte-for-byte from the frozen V12 predictions. V13 adds only the explicit call-count rule above. Package builds remain a separate reported cost.

## One scored run and gates

The protocol pins clean isolated production source-base commit `7e90b5833eecb893c6db5f260e5d1cfc69cd230f` and exact Zig/compiler/engine/tool/host hashes. It requires the host, compiler fingerprint, and engine gitlink to equal the frozen V12 validation pins, eliminating a compiler or host revision as an explanation of V13 topology/call-count differences. The runner builds and admits all **three** native packages before any proof, measures claim 0 once and immediately repeats it for each package (both descriptive and excluded from score), then executes 20 scored claims/source. Seed `202610122313` shuffles claim indices and source order within each round, yielding 60 interleaved scored proofs. For every proof the native verifier must accept the exact statement and reject an exact ABI-valid changed public result at `InvalidMixedInteractionNonce`. The independent audit checks saved source/claim/proof/binary bytes, native manifests and phase reports, process timing endpoints, physical scored order, score arithmetic, and replays all honest/negative controls.

All gates are conjunctive and frozen before native builds:

| Gate | Threshold |
|---|---:|
| Per-source warm whole-verified wall median relative error | ≤30% |
| Per-source 90% one-draw wall interval hits | ≥14/20 |
| Pooled 90% one-draw wall interval hits | ≥49/60 |
| Sources with observed sample-of-20 wall median in frozen 90% median band | ≥2/3 |
| Per-source proof median relative error | ≤10% |
| Per-source proof interval hits | ≥16/20 |
| Per-source prover and verifier median peak RSS relative errors | ≤30% each |

The less stringent 14/20 and 49/60 thresholds recognize sampling variation in nominal 90% coverage; wide PoW bands make coverage alone weak evidence. A pass or failure is confined to this host, compiler/engine revision, source family, and `/usr/bin/time` wall/RSS method. No V13 result supports a Cairo speedup or cryptographic security claim.
