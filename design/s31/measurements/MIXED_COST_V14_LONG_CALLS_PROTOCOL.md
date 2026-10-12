# V14 prospective multiple-long-call and log-13 cost challenge

Status: **pre-native frozen candidate**. The canonical rule, protocol, three fresh sources, runner, audit, and this document must be committed before the first V14 native package build. V11 failed, V12 passed, and V13 passed as previously scored; they are now declared V14 training evidence. No V14 source, claim, or native timing enters the fit. A failed native geometry admission or score is preserved unchanged.

## What changes

V13 added only short 32/16/64-round calls after a 4,096-round first call. V14 gives every additional call **4,096 rounds** and adds a source whose first call has **8,192 rounds**, reaching chip trace log 13. The programs retain V13's two live 1,024-multiplication branches joined before the chip, holding circuit topology at log 12 while varying aggregate chip work.

| New source | Sequential chip rounds | Aggregate rounds | Frozen expected slot logs | Native constraints |
|---|---|---:|---|---:|
| `long_fork_n2` | 4,096, 4,096 | 8,192 | `[12,12,4,12,4]` | 49 |
| `long_fork_n3` | 4,096, 4,096, 4,096 | 12,288 | `[12,12,4,12,4,12,4]` | 68 |
| `long_fork_log13_n2` | 8,192, 4,096 | 12,288 | `[12,13,4,12,4]` | 49 |

The source graph and an independent Python M31 oracle agree for all four lanes of all 21 claims/source. The source/claim digests are disjoint from earlier V4–V13 experiments. Expected logs are not treated as observed: all three native manifests must exactly match source digest, calls/rounds, slots/logs, tree columns, total constraints, max-column and composition log 12 or 13, registry-manifest digest, and interaction/FRI PoW bits 20/26 **before any proof**. If a log-13 component is unsupported, this frozen challenge fails admission; it is not substituted or dropped.

## Predeclared predictor

V14 retains V12's frozen stochastic PoW predictive simulation and proof relative interval width. The warm verified-process non-PoW baseline, proof-byte center, and prover/verifier RSS centers are the **V13 fork N1 scored medians**. For each additional chip call, V14 adds a *short-call step*: the positive part of the median of V13 `(fork N3 − fork N1)/2` and `(fork N4 − fork N1)/3` for each metric. The resulting steps are +0.908 ms non-PoW wall, +15,007.625 proof bytes, +0 prover RSS bytes, and +147,456 verifier RSS bytes per call.

The explicit, falsifiable **long-call hypothesis** is that a second or third 4,096-round call at an already-paid maximum trace log 12 adds no more non-PoW cost, proof bytes, or RSS than those V13 short calls. This could fail: V13 contains no second long call. For the 8,192-round first call, one chip-log step is added: +3.138 ms non-PoW wall and +2,998,272 prover RSS bytes from the positive V12 chip-only minus V11 chip-only medians, and +20,571 proof bytes from V12's pre-native joint proof log-step coefficient. V11 and V12 chip sources use different constants, so the measured log step is confounded; it is a weak transfer assumption, not an identified structural cost.

Wall one-draw and sample-of-20 median distributions add these frozen non-PoW centers to V12's unmodified PoW/residual simulation. FRI and interaction PoW phase bands are retained separately; proof and RSS forecasts are separate. The full model, its source hashes, algorithm and numeric predictions are in `language/mixed-cost-v14-long-calls-model.json` and the canonical protocol. The centers are:

| Source | Frozen warm wall one-draw median | Frozen 90% sample-of-20 median band | Proof center | Prover RSS center |
|---|---:|---:|---:|---:|
| N2 log12 | 168.09 ms | 128.33–259.86 ms | 142,618.625 B | 17.52 MB |
| N3 log12 | 169.00 ms | 129.24–260.76 ms | 157,626.25 B | 17.52 MB |
| N2 log13 | 171.23 ms | 131.47–262.99 ms | 163,189.625 B | 20.52 MB |

The whole verified-process wall is the fresh prover process plus fresh external verifier process under the same `/usr/bin/time` OS-RSS wrapper as V11–V13. Native FRI/interaction PoW reports are saved separately. V14 runs from the same production source-base commit `7e90b5833eecb893c6db5f260e5d1cfc69cd230f`, engine gitlink, compiler fingerprint, and host as V12/V13. All scripts, compiler/runtime files, model inputs, Zig executable, and source template are pinned by hashes.

**Build and cold cost:** V11–V13 have only one package build/source and claim-0 first/repeat observations. Compiler caching, source size, and process cold-start effects are not identified, so there is **no defensible prospective build or cold-start prediction gate**. V14 records build wall, first post-build claim-0 wall, and immediate repeat per source separately, excludes them from warm score, and reports them regardless of outcome. This limitation must remain explicit in any whole-prover cost claim.

## Single run and prespecified gates

The runner builds/manifests all three packages first, then proves claim 0 twice per source as descriptive observations. Scored claim indices 1–20/source are shuffled into 60 interleaved tasks using seed `202610122359`: shuffled claim order, then shuffled source order within each claim round. Every trial must emit the exact public statement, pass an external native verifier, and reject an exact ABI-valid changed public result at `InvalidMixedInteractionNonce`. The independent audit recomputes scores from saved files, checks binary/source/claim/proof hashes, native geometry and timing reports, and physical order, and can replay all 66 honest and 66 negative verifier calls.

All scored gates are conjunctive:

| Gate | Threshold |
|---|---:|
| Per-source warm whole-verified wall median relative error | ≤30% |
| Per-source nominal 90% one-draw wall interval hits | ≥14/20 |
| Pooled nominal 90% one-draw wall interval hits | ≥49/60 |
| Sources with observed sample-of-20 wall median in frozen 90% median band | ≥2/3 |
| Per-source proof-byte median relative error | ≤10% |
| Per-source proof interval hits | ≥16/20 |
| Per-source prover and verifier median peak-RSS relative errors | ≤30% each |

The coverage thresholds account for sampling variation, but the PoW bands are wide and their coverage alone is weak evidence. A pass would support only these sources, host, compiler/engine revision, and method; it cannot establish broad cost reliability, speedup over Cairo, or cryptographic soundness.
