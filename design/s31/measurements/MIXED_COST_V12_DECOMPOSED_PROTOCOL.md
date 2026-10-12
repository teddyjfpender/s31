# V12 whole-prover cost falsification at unseen log-12 geometry

Status: **pre-native protocol**. The canonical frozen protocol, model, sources, runner, and independent audit are committed together before any V12 package build. A result is valid only if `protocol.py check` succeeds in the isolated worktree on the pinned host and its exact frozen source/compiler bytes. The one scored run is not a model-fitting exercise.

## Question and evidence classification

Can a model fitted to earlier native measurements forecast the **whole verified process wall**, proof size, and peak process memory on four new source programs whose circuit/chip trace geometry reaches log 12? V10 supplied proof-byte log-step increments only. V11 supplied same-method process wall, native PoW phases, and RSS. **V11's prospective score failed 14/16 gates**; its gate-only log-11 wall median missed by 46.37% and is explicitly reclassified as V12 training. No V12 source, claim, or native timing is in that fit. The four V11 source blocks are a very small fit and cannot establish broad reliability.

V12 runs from isolated source-base commit `7e90b5833eecb893c6db5f260e5d1cfc69cd230f` and the pinned `deps/stwo-zig` gitlink, before the concurrent public-u8 ABI edit. Source, compiler, engine, host, Zig executable, prior artifacts, and all V12 scripts are hashed in the protocol. The protocol checker rejects changed bytes. The specific repo commit that contains this protocol may be newer than the source-base commit; the protocol hashes and `git show` check make the production source identity exact.

## Four frozen source programs

Each program takes one four-lane public M31 input, feeds a live arithmetic chain, calls the native repeated-square/add chip, and emits one public four-lane result. For lane input `x`, a typical gate chain is `g0 = f²`, `g1 = g0·shifted_input`, through 2,048 live multiplication nodes; an independent Python field oracle evaluates every claim. Calls use `r ← r² + c (mod 2³¹−1)` for their declared number of rounds. Public outputs are recomputed from the input; a changed public result is an ABI-valid negative verifier control.

| Source | Live packed multiplication nodes | Chip rounds | Expected slot trace logs | Calls |
|---|---:|---|---|---:|
| `circuit_cascade_n1` | 2,048 | 16 | `[12,4,4]` | 1 |
| `chip_spiral_n1` | 0 | 4,096 | `[9,12,4]` | 1 |
| `joint_cascade_n1` | 2,048 | 4,096 | `[12,12,4]` | 1 |
| `serial_spiral_n2` | 0 | 4,096, 32 | `[9,12,4,5,4]` | 2 |

A package is admitted only if its **native manifest** matches frozen source SHA-256, call/round list, slot count/logs, tree-column widths, constraint count, composition/column log 12, registry-manifest digest, and PoW bits (interaction 20, FRI 26). A predicted geometry does not substitute for this manifest check. If any source fails admission, the prospective run fails before scoring; the source is not replaced.

## Frozen predictor

For V11 scored trial `i`, define `Nᵢ = (fresh prover process wall + fresh external verifier process wall) − native FRI PoW duration − native interaction PoW duration`. The same `/usr/bin/time` wrapper obtains wall and OS peak RSS in V11 and V12. It is included in `Nᵢ`. The V11 centered residuals form an empirical non-PoW noise pool. V12 starts with each source shape's V11 median `N` and extrapolates one circuit/chip log step from positive V11 cross-shape contrasts. This extrapolation is fragile: geometry cost is not identified from four blocks.

PoW is modeled separately, with a declared **assumption**: nonce-search time is exponential conditional on a rate. For FRI, each of the four V11 source blocks supplies 20 durations and a scale-invariant `1/rate` prior; one block is chosen uniformly and its posterior rate is drawn as Gamma(shape=20, scale=1/sum durations). Interaction PoW uses all 80 V11 durations and Gamma(shape=80, scale=1/sum durations). For a future 20-claim source, rates are drawn once per simulated sample, then 20 fresh exponential durations are drawn. This preserves source-level rate uncertainty across the sample. Each draw adds one uniformly sampled centered V11 `N` residual. Python `random.Random` seed `202610122121` gives 100,000 one-draw simulations and 10,000 sample-of-20 median simulations. Quantiles 0.05/0.5/0.95 use sorted linear interpolation at `(n−1)q`. The model freezes one-draw wall/phase bands **and** a separate 20-draw wall-median band. These are empirical predictions, not formal cryptographic guarantees.

Proof bytes use V10→V11 same-shape median increments per trace-log step and V10's frozen relative interval width; the two-call source uses the chip increment. Prover and verifier peak RSS each use V11 medians plus positive circuit/chip cross-shape contrasts. Proof and RSS extrapolations are explicitly fragile. Package-build wall is reported as a separate, unforecast cost and excluded from the scored whole-proof wall.

## One prospective run

The runner builds and manifests **all four** native packages before any proof. Each package proves claim 0 once immediately after the builds, then proves it again; these are descriptive cold/repeat costs and excluded from score. Scored claims are indices 1–20 for every source, with no reused prior claim digest. Seed `202610122241` shuffles claim indices and then shuffles all four source names per round. This produces 80 interleaved scored proofs, with exactly one proof per source per round; no adaptive choice of order is allowed.

Every trial must emit the exact frozen public statement, pass an external native verifier, and reject the exact ABI-valid changed public result at `InvalidMixedInteractionNonce`. The runner saves source/assignment/statement/changed/proof files, binary hashes, native manifest, native phase reports, monotonic timing endpoints, proof bytes, build wall, and OS peak RSS. An independent audit recomputes scores from the raw ledger, checks every saved byte and geometry, and replays every honest and negative verifier invocation when asked. The single scored result and failure remain preserved even if the model misses.

## Prespecified pass gates

All gates are conjunctive; a single miss falsifies the local V12 transfer claim.

| Gate | Threshold |
|---|---:|
| Per-source wall median relative error, denominator observed median | ≤30% |
| Per-source 90% one-draw wall band hits | ≥14/20 (70%) |
| Pooled 90% one-draw wall band hits | ≥67/80 (83.75%) |
| Sources whose observed 20-draw wall median lies in frozen 90% median band | ≥3/4 |
| Per-source proof-byte median relative error | ≤10% |
| Per-source proof-byte interval hits | ≥16/20 (80%) |
| Per-source prover median peak-RSS relative error | ≤30% |
| Per-source verifier median peak-RSS relative error | ≤30% |

The 14/20 and 67/80 wall thresholds acknowledge binomial sampling variation in nominal 90% one-draw coverage; the 20-draw median band is a separate distributional check. Four source medians remain statistically weak. Per-phase FRI and interaction PoW predictions are reported for diagnosis, not silently folded into proof or RSS gates. A pass would support only this host, compiler/engine revision, source family, and fixed measurement method. It does not prove general accuracy, security, or a Cairo speedup.
