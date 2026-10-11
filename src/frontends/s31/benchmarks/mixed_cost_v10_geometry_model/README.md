# V10 prospective geometry transfer

This is a one-run prospective **same-geometry transfer to fresh source instances** of a frozen one-call whole-prover cost model. V9 showed that the V8 model's proof-size center missed all three one-call geometry variants while its wall-time gates passed. V9 remains a failed transfer. V6 was invalidated by a changed compiler pin and contributes no performance data.

Post-run wording correction: the pre-run version called V10 an “out-of-distribution” check. All three circuit/chip log pairs were used to fit the V10 model from V9, and the new sources use closely related operator skeletons. The appropriate claim is prospective transfer to fresh instances at **observed** geometry. This correction changes no frozen model, protocol, gates, or score. The single run passed all 12 declared gates; see [the result report](../../../../../design/s31/measurements/MIXED_COST_V10_GEOMETRY_TRANSFER_RESULT.md).

## What is fitted

`model.py` reads the committed V4 fit/calibration and clean V5, V7, V8, and V9 result artifacts. It checks the exact source roster, scored claim counts, changed-claim rejection, and native manifest circuit/chip logs. The model is deliberately restricted to **one call** and the four observed `(circuit trace log, chip trace log)` pairs `(9,4)`, `(10,4)`, `(9,10)`, and `(10,10)`. It is not a general geometry regression.

The V4 proof center at one call is 70,006.75 bytes. The V9 chip-only median was 85,369.5 bytes, so the fitted jump when the maximum trace log changes from 9 to 10 is **15,362.75 bytes**. The gate-only and joint medians were 87,355.5 and 87,503.5 bytes. Their average minus the chip-only median is **2,060 bytes**, the fitted extra circuit-log effect. The joint case pays the shared maximum-log jump once. These are contrasts on three source blocks, not independent estimates of an AIR law.

For wall time, the V4 non-PoW baseline and 156 residuals remain. A two-by-two contrast of the V8 baseline and V9 three geometry blocks adds circuit/chip non-PoW shifts. The FRI PoW distribution is an equal mixture of nine source-level exponential rates from clean V5/V7/V8/V9 blocks; interaction PoW retains V4's scale. This accounts for random nonce search and source-to-source rate variation, with no claim of a distribution-free guarantee.

The proof interval half-width is the largest finite-sample 95th-percentile absolute relative residual across the 13 fit source blocks **plus** the largest baseline one-call source-median bias in V5/V7/V8: 6.462%. This conservatively includes a measured source-level offset. The median center, interval, PoW rates, and source-rate envelope are serialized in the model before any V10 proof is generated.

## Prospective holdout

`protocol.py` defines three new source families with 256 live multiplication gates and 16 chip rounds, zero gates and 1,024 rounds, and both changes. Their constants, gate wiring, source names, and 81 claim identities per source are fresh and checked for collision against V4–V9 and the V9 feasibility probes. Native admission must report one call, three component slots, 30 constraints, tree columns `[8,29,36,8]`, 20-bit interaction PoW, 26-bit FRI PoW, and respectively `(10,4)`, `(9,10)`, or `(10,10)` component logs. A mismatch invalidates the run before scoring.

Claim 0 is measured once after build and repeated immediately, for description only. Claims 1–80 are scored in ascending order; each runs in a fresh prover and verifier process. Each proof must verify against its original statement and reject a changed public result at the proof layer. The package binaries, source, manifest, statements, assignments, proofs, timing endpoints, and protocol pins are retained under the run output directory and replayed by `audit.py --native`.

| Source | Circuit/chip logs | Frozen proof center | Frozen proof interval | Wall median |
| --- | ---: | ---: | ---: | ---: |
| `gate_weave_n1` | 10/4 | 87,429.5 B | 81,779.6–93,079.4 B | 97.87 ms |
| `chip_twirl_n1` | 9/10 | 85,369.5 B | 79,852.7–90,886.3 B | 88.38 ms |
| `joint_weave_n1` | 10/10 | 87,429.5 B | 81,779.6–93,079.4 B | 97.95 ms |

Each source has four independent gates: wall-median relative error at most 30%, nominal 90% wall interval coverage at least 80%, proof-median relative error at most 10%, and nominal 90% proof interval coverage at least 80%. These limits match V9. Any miss remains a failed transfer; there is no scored rerun or holdout refit.

## Reproduction

Before native timing, run `python3 -B model.py check`, `python3 -B protocol.py check`, and `python3 -B -m unittest discover -s . -p test_static.py -v` from this directory. The protocol and model must already be committed, and `protocol.py check` compares every pinned compiler/runtime/tool byte to the pre-native protocol. After the quiet-window single run, use `python3 -B study.py run --out <artifact-dir>` and `python3 -B audit.py --out <artifact-dir> --native --write`. The result, score, and audit are canonical JSON in `design/s31/measurements/language/`.

The sample is three source blocks of 80 scored claims. It tests transfer to fresh source structure at known log pairs. It cannot establish a reliable predictor for other trace lengths, chip families, hardware, or future compiler/engine versions.
