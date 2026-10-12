# Paired S31 direct circuit versus mixed circuit/chip proving (v1)

## Question and result

Does S31's authenticated circuit-to-chip lowering improve **actual native
proving** for the same source program and public claim? In this bounded study,
the answer depends on shape. One 1,024-round square/add call gave a **25.8%
smaller median proof** and **37.1% lower median prover peak RSS** with mixed
lowering. At 16 rounds, mixed proofs were **24.5% larger** for one call and
**106.4% larger** for four calls. These are observed outcomes for this source
family, not a general language or prover speedup.

The 12-pair process-wall medians appear faster for mixed in the four-call and
high-round cases, but do **not** establish a computational speedup. Both
profiles use a 26-bit FRI proof of work, whose randomly variable search time
is a large fraction of these short proofs. After arithmetically subtracting
the prover's native-reported interaction and FRI proof-of-work timers, the
median residual process wall is **higher for mixed in all three cases**. That
residual is a diagnostic, not a separately timed or controlled execution.

## Matched work and verification boundary

The public v2 S31 record has `x.words[4]` and `result.words[4]`, each word an
M31 element. In every lane, each call applies `v = v² + (13 + call_index)`
for either 16 or 1,024 rounds. Four-call chaining adds the original `x`
between calls; the final output adds `x`. The [benchmark source generator](../../../../src/frontends/s31/benchmarks/paired_mixed_vs_direct/design.py)
is the precise definition. Both lowerings consume identical normalized source
bytes and, within each pair, identical assignment and typed statement bytes.
An independent Python arithmetic oracle computes each public result.

`direct-gate` expands the work into the generic Gate AIR. The experimental
`direct-mixed-general` profile keeps surrounding arithmetic in a bundled
circuit, with a dedicated square/add chip and an authenticated bridge for
each call. Each package has a generated source-pinned external native verifier.
The measured first-verified boundary is one fresh native prover process plus
one fresh native verifier process. The direct package uses
`prove-for-external-verification`, so neither prover internally verifies
before the external check. Package builds and one warmup per case/profile are
outside the scored set.

Each saved honest proof was accepted by its generated verifier. The same
verifier rejected a validly encoded typed public statement with one output
word changed, at `InvalidInteractionNonce` for direct and
`InvalidMixedInteractionNonce` for mixed. The replay audit repeated these
controls on all **78 proofs** (72 scored and six warmups): **78/78 honest
acceptances and 78/78 changed-claim proof-layer rejections**. This checks the
specified claims and negative control; it is not a complete proof of all
compiler/runtime soundness properties.

## Scored measurements

Medians below use 12 matched, randomized-order scored pairs per source.
`D/M` is the median of the 12 *paired* direct-to-mixed ratios; it need not
equal the ratio of the two displayed medians. Times include fresh process
startup. RSS is peak resident bytes reported by macOS `/usr/bin/time -l`.

| Source | First verified, direct / mixed (ms) | Prover, direct / mixed (ms) | Proof, direct / mixed (bytes) | Prover RSS, direct / mixed (MiB) |
| --- | ---: | ---: | ---: | ---: |
| 1 call × 16 rounds | 87.60 / 114.79 (D/M 0.68) | 67.52 / 94.93 (D/M 0.64) | 55,425 / 69,003 (D/M 0.80) | 7.66 / 7.39 |
| 4 calls × 16 rounds | 94.74 / 70.73 (D/M 1.18) | 75.44 / 50.94 (D/M 1.29) | 55,663 / 114,865 (D/M 0.48) | 7.70 / 7.65 |
| 1 call × 1,024 rounds | 113.57 / 103.04 (D/M 0.94) | 92.25 / 83.64 (D/M 0.93) | 112,921 / 83,784 (D/M 1.34) | 13.15 / 8.27 |

The high-round proof was smaller for mixed in **all 12 pairs**; both
16-round mixed proofs were larger in **all 12 pairs** for each short case.
The high-round mixed prover RSS was 37.1% lower by the displayed medians.
The external verifier's median wall was roughly 19–20 ms for both profiles:
19.55 / 19.99 ms, 19.97 / 20.38 ms, and 20.22 / 19.40 ms respectively.
Mixed verifier peak RSS was higher in all three shapes: 6.39–6.45 MiB versus
5.22–5.86 MiB for direct.

The median process-wall residual after *subtracting* native-reported
interaction and FRI proof-of-work time was, in source order, **36.55 / 40.45
ms**, **37.05 / 42.71 ms**, and **38.76 / 39.42 ms** (direct / mixed). Median
FRI proof-of-work time alone varied from 24.86 to 75.66 ms between
case/profile cells. This is why the observed first-verified wall direction
cannot be attributed to the chip. We have not run a separately timed
proof-of-work-controlled variant.

## Geometry and setup cost

| Source | Direct raw / padded Gate rows | Mixed slots (circuit + chips + bridges) | Mixed constraints | Direct / mixed package build (s) |
| --- | ---: | ---: | ---: | ---: |
| 1 × 16 | 354 / 512 | 3 (1 + 1 + 1) | 30 | 52.03 / 74.76 |
| 4 × 16 | 456 / 512 | 9 (1 + 4 + 4) | 87 | 52.28 / 75.16 |
| 1 × 1,024 | 2,370 / 4,096 | 3 (1 + 1 + 1) | 30 | 52.16 / 74.09 |

The direct high-round Gate trace is padded to 4,096 rows and has 32,768
preprocessed cells. The mixed high-round manifest has circuit, chip, and
bridge trace log sizes 9, 10, and 4; 29 main and 36 interaction columns in
the composed tree. Its total constraint count stays at 30 as rounds grow,
though chip trace length grows. The four-call mixed manifest has 80 main and
120 interaction columns across nine slots. This component and bridge cost
explains the large short-call proof envelope. Both use 70 FRI queries and
26-bit FRI proof of work; their AIR geometry and proof envelopes differ.

ReleaseFast package construction was measured separately from proving. The
direct packaging command invokes the Python package generator and two Zig
builds/checks; the mixed package uses one Zig install. These durations are
whole setup costs for the respective current tools, **not isolated compiler
comparisons**. The direct and mixed builds averaged roughly 52 s and 75 s
per source on this host, respectively.

## Reproduction and limits

The [prospectively committed protocol](paired-mixed-vs-direct-v1-protocol.json)
has SHA-256 `e1a703de522b13f322964607b892149962b0911f7cc2f8920f897dc0754f5c02`.
It pins compiler and benchmark bytes, source and claim hashes, randomized
balanced order, profile, build mode, host, and process bounds. It was
committed before the scored run. The [raw structured result](paired-mixed-vs-direct-v1-result.json),
[summary](paired-mixed-vs-direct-v1-summary.json), and
[replay audit](paired-mixed-vs-direct-v1-audit.json) retain exact measurements,
component manifests, binary hashes, and verification outcomes. The saved
proofs live under ignored `zig-out/s31-paired-mixed-vs-direct-v1/` in the run
workspace. The [benchmark README](../../../../src/frontends/s31/benchmarks/paired_mixed_vs_direct/README.md)
gives commands and source semantics.

Host: Apple arm64, macOS 26.7.1, Zig 0.15.2, Python 3.14.6; pinned Stwo
engine gitlink `fde847ea374ade2ae07ef5b3a42ba07e15655b64`. The study has
one host, 12 scored pairs per shape, one arithmetic source family, public
inputs, and no separate controlled proof-of-work cohort. It does not test
private-input confidentiality or establish a general speedup. The next
performance experiment should control proof-of-work cost and test broader
chips or repeated work where bridge costs can amortize. The next soundness
step remains independent scrutiny of the generated AIR and compiler
correspondence, beyond native honest/changed-claim acceptance.
