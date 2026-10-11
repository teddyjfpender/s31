# S31 stage-resolved cost v1: local prospective result

The frozen stage model passed all ten predeclared local diagnostics on three
new lagged alternating sources (96, 256, and 448 gates, 12 trials each),
without refitting. Its measured separation of first-use process startup from
later proof processes is useful. **Raw whole-wall prediction is still too
uncertain for one-shot scheduling:** the historical later-process interval is
0.349–3.201 times its point estimate. This result adds evidence for one
direct-gate source topology on one host; it is not a general whole-prover
reliability certificate. The [protocol](STAGE_RESOLVED_COST_V1.md) explains
the seven-stage equation and predeclared gates.

## Frozen inputs and proof controls

The [plan](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/plan.json)
was sealed before these three new native package builds, SHA-256
`90b9369a734a30d8f6295e15762d9bde5e5e91a044c6aa62b9a9a6216b9b8446`.
It pins 36 assignments and all three source hashes, historical stage ledger
SHA `1f25924ae8d40e8e758c291eb0f6bd1542600dedd1d495707f5afb67efd3af0c`,
frozen calibration SHA
`85ed27e398b7d39b26bc3273b9e3d9470f2e8a15d445fae7984768689aadc8b9`,
runner, model, independent scorer, value-oracle provenance, compiler
fingerprint `893ce1f78d19783eaafac3094dbbe847bdbb61de9a4b2055d3c8ff50b2e4dd1b`,
engine gitlink `7d544c6839497ca19b6c7ef9b982e464f10cfeed`, and the host identity
(arm64 macOS 26.7.1, Python 3.14.6, Zig 0.15.2). Compiler, engine and host
identity were rechecked before the first build.

All **36/36 native proofs** were accepted, all 36 changed public claims were
rejected, and all 36 independent value-oracle checks passed. The separate
[native replay audit](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/audit.json)
accepted the same 36 originals and rejected the 36 changed claims again.
The prospectively pinned [independent scorer](../../../src/frontends/s31/benchmarks/stage_resolved_v1/independent_score.py)
reconstructed the seven stage terms and agreed with the frozen score from
each raw report. Actual raw/padded QM31 rows were 416/512, 576/1024 and
768/1024 at 96, 256 and 448 gates, respectively.

## Point estimates and interval coverage

The table uses the **11 later proof processes per source**, excluding the
first process after package build. Millisecond entries are observed median
and frozen point estimate. Relative error divides their absolute difference
by the observed median; it is a point error, distinct from interval coverage.

| Gates | Later wall observed / predicted | Wall error | Later wall after reported PoW observed / predicted | After-PoW error | Proof-byte error | RSS error |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 96 | 126.21 / 101.78 ms | 19.35% | 37.68 / 38.79 ms | 2.95% | 2.75% | 0.68% |
| 256 | 127.31 / 102.84 ms | 19.22% | 43.24 / 42.53 ms | 1.66% | 0.48% | 0.88% |
| 448 | 112.39 / 133.08 ms | 18.41% | 43.26 / 42.79 ms | 1.08% | 0.0024% | 0.67% |

The first process had 420–432 ms of observed unclassified prover process
residual; later median residuals were 14.90–18.50 ms. The first-use wall
observations were 626.41, 479.93 and 548.50 ms, against frozen point
estimates of 506.00, 512.29 and 520.02 ms at 96, 256 and 448 gates.
All three first-use wall observations fell in the deliberately broad
three-source historical interval. There are only three first-use calibrators
and three new first-use trials; this is not a tail guarantee.

| Historical empirical interval | Frozen lower / center | Frozen upper / center | New trial coverage | Predeclared minimum |
| --- | ---: | ---: | ---: | ---: |
| Later whole wall | 0.349× | 3.201× | 31/33 = 93.94% | 75% |
| Later wall after reported PoW | 0.774× | 1.083× | 30/33 = 90.91% | 80% |
| Later proof bytes | 0.957× | 1.065× | 30/33 = 90.91% | 80% |
| Later prover peak RSS | 0.978× | 1.027× | 32/33 = 96.97% | 80% |
| First-use whole wall | 0.509× | 2.494× | 3/3 = 100% | 2/3 |

All ten declared diagnostics passed. The worst later program-median errors
were 2.95% after reported PoW (15% limit), 2.75% for proof bytes (10%
limit), and 0.88% for RSS (10% limit). Later whole-wall interval upper /
center was 3.201× (8× limit); later after-PoW was 1.083× (1.5× limit).
There was no predeclared wall **point-error** gate. Although its interval
coverage was high, a 3.201× upper ratio and roughly 19% median point errors
make whole-wall timing unsuitable for a precise one-shot scheduler. The
after-PoW view subtracts a measured timer from the **same proof**; it does
not represent a faster proving mode.

The [held-out score](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/heldout-score.json)
has SHA-256 `c01aea2104a7235b299ccedfd053b9d785adb6295427e6d62bb8e1f64ed44493`.
Observed package build walls were 52.35–53.17 seconds, outside the paired
proof-process target and dependent on local Zig cache state. The
[held-out report](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/heldout-report.json)
records package manifests and each proof/report hash.

## Independent audit and provenance limits

The [compact 36-trial ledger](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/compact-trials.json)
has SHA-256 `7063eac054152592ca5e0b2eaac2d5b2e01111765fe710e2fc52c238aee4ed7e`.
It preserves every measured stage, wall time, proof size, RSS value, AIR row
size, source assignment/trial/proof hash and control outcome. Raw packages,
proofs, statements, and trial reports remain under the ignored local
`zig-out/s31-stage-resolved-v1` directory (about 28 MB). Git alone cannot
replay native verification without those binaries/proofs.

The historical calibration was also checked by a **separate second-source
replay written after the new-family measurement**. It reproduced all 21
stage centers, 24 first/later target centers and eight empirical ratio bands
from the previously saved 108-trial historical ledger. Its
[saved audit](../../../src/frontends/s31/benchmarks/stage_resolved_v1/results-2026-10-11/posthoc-calibration-audit.json)
is an extra consistency check, **not prospectively pinned code**. The
publication tool and compact ledger were likewise made after measurement;
the presealed runner, model, plan and independent scorer were not changed.

The plan was sealed locally, without an external timestamped pre-phase
commit. This is a controlled local prospective check of one `direct-gate`
lowering on one machine and engine. The new 96–448-gate programs exceed the
1–16-gate bounded release correspondence certificate; native verification
and value checks do not supply that missing compiler proof. No chip,
cross-host, private-boundary, recursive, or package-build-cost transfer claim
follows. Automatic lowering remains disabled.
