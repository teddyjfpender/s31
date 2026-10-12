# Independent V24 conditional-repeat result audit

**The one frozen V24 native attempt passed all preregistered gates.** Its atomic
marker has one `started` entry at 2026-10-12 01:51:21 UTC and one `completed`
entry at 01:52:56 UTC, with no failed or second attempt. The amended protocol
SHA-256 is `7fe65548d434faaecbcdc1969456ea0db02df7fa21ba36bdf8ee640f31c7572c`;
the source SHA-256 is `9755a1005c8533607e2457b3c900f6d0d81cb4dabfed3b02697c57d0357ee5f9`.
The source, forecast formula, claims, manifest prediction, and gates were held
fixed through the two documented **pre-native** tool and compiler pin
amendments. V17 and V23 remain failed holdouts.

I ran the pinned V24 `audit.py --out /private/tmp/s31-v24-conditional-repeat-artifacts --native`
from the shared pushed checkout after the single attempt completed. It exited
0 and independently replayed **42 honest external-verifier acceptances and 42
changed-result proof-layer rejections**. I did not rerun proof timing. The
canonical audit JSON committed alongside this report records that successful
stdout; writing it required no second verifier replay. A separate read-only
stdlib check verified canonical JSON and SHA-256 links for protocol, marker,
result, and score; raw source, manifest, three binary hashes, 42 assignment,
statement, and proof hashes; the exact changed-result stderr; process-duration
sums; and every paired forecast and warm aggregate in the score.

The native manifest matched the frozen 8 ordered calls, **17 slots, 163
constraints**, slot trace logs, source/feeder IDs, constants, and tree columns
`[8, 148, 232, 8]`. Every adjacent same-claim pair had identical assignment,
statement, and proof hashes. The independently recomputed repeat forecast used
the first proof's measured FRI and interaction PoW plus the frozen 150.346 ms
source-specific non-PoW center; no repeat measurement entered its forecast.

| Frozen measure | Forecast or gate | Observed | Outcome |
| --- | ---: | ---: | --- |
| Paired repeat median observed-relative error | ≤20% | **5.83%** | Pass |
| Repeat pairs within 35% error | ≥18/21 | **21/21** | Pass |
| Repeat non-PoW median | 150.346 ms, ≤20% error | **163.146 ms**, 7.85% error | Pass |
| Fresh-claim warm verified-wall median | 225.096 ms, ≤35% error | **207.692 ms**, 8.38% error | Pass |
| Warm one-draw wall and proof-size intervals | ≥14/20 and ≥16/20 hits | **20/20 and 20/20** | Pass |
| Package build | 78.172 s, ≤25% error | **77.351 s**, 1.06% error | Pass |
| First post-build proof | 1.212 s, ≤40% error | **1.386 s**, 12.52% error | Pass |
| Build plus 42 verified-proof process durations | 88.613 s, ≤25% error | **88.329 s**, 0.32% error | Pass |

All inherited V18 warm, proof-size, RSS, and native-stage gates passed. The
measured sum excludes gaps between processes; package build accounts for
87.57% of it. The first proof is first use after build, not a controlled OS
cold-cache measurement. This is one new topology on one Apple M5 Max host;
it does not establish cross-host calibration, automatic lowering quality, a
Cairo speedup, or general proof-system soundness.

Canonical artifact hashes: attempt
`e6d6f51ffab0d35b96b010f7a2ab43c6e5ccec687731f29f7b9517182d9edf38`,
result `efd1d86a512072beeb34aa5dffe59f26f6e35d828c2b946fbdfe75a571b403a1`,
score `9ee6b9f2d6483f5f3239cd85099cdf2f72caad820e81ca8981cec4d4bfa20d92`,
and canonical audit
`32d90e6a7bb275b14da1084bf7c4acd30ee6e77755547176a40ab97f372d58c0`.
Raw binaries and proofs remain at
`/private/tmp/s31-v24-conditional-repeat-artifacts`; preserving native replay
requires retaining that directory separately from Git.
