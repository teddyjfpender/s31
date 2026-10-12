# Fresh 80-claim transfer of the frozen v4 cost model

**The preregistered v7 transfer fails two of eight per-source gates.** The
N=1 proof-size 90% interval covers **62/80 = 77.5%**, below its frozen 80%
limit. The N=8 predicted warm-wall median has **32.47%** relative error,
above its 30% limit. The other six gates pass. No v4 coefficient, residual,
interval, limit or score has been changed after observing the result.

The [protocol](language/mixed-cost-v7-transfer-protocol.json) and the two
exact [source JSON files](language/mixed-cost-v7-transfer-sources/) were
committed as `95bd61a` before the first native package build. Protocol
SHA-256:
`aa635c494492543e5cfe83ac232d25bbbb80100e78f803a220240c8c2be73d0d`.
These source and claim identities are disjoint from v4, v5 and the unscored
v6 attempt. The final pinned-stack check passed. V6 data were not inspected
or used to fit or score this run.

| Source | Predicted wall p50 | Observed warm median | Wall median error | Wall interval coverage | Predicted proof center | Observed proof median | Proof median error | Proof interval coverage |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `affine_seed_n1` | 84.21 ms | 92.34 ms | 8.80% | 70/80 = 87.5% | 70,007 B | 70,422 B | 0.59% | **62/80 = 77.5% (fail)** |
| `switchback_n8` | 88.34 ms | 130.82 ms | **32.47% (fail)** | 67/80 = 83.75% | 171,831 B | 173,173 B | 0.78% | 74/80 = 92.5% |

Each source had to meet wall median error ≤30%, 90% wall interval coverage
≥80%, proof median error ≤10%, and 90% proof interval coverage ≥80%. N=1
proof interval coverage misses by two of 80 claims. Eight proofs were below
its 67,629-byte lower bound and ten above its 72,385-byte upper bound,
despite an accurate proof median. N=8 wall median misses by 2.47 percentage
points. Its 26-bit FRI PoW median was **98.47 ms** versus the frozen v4
exponential clock's **53.13 ms** median; this is post-run attribution, not a
predictor feature or a proof of cause. The measured N=8 non-PoW whole-wall
median was 34.48 ms. The result suggests the model's PoW distribution and
proof interval need fresh calibration for this stack and source range.

## Native geometry and process observations

Both packages reported 20-bit interaction and 26-bit FRI PoW, and the
native manifests matched source IDs, component rosters, constraint sums,
tree-column totals and registry manifest digests.

| Source | Calls / slots | Constraints | Commitment tree columns | Max / composition log | First post-build verified wall | Immediate same-claim repeat | Build wall |
| --- | ---: | ---: | --- | ---: | ---: | ---: | ---: |
| `affine_seed_n1` | 1 / 3 | 30 | `[8, 29, 36, 8]` | 9 / 9 | 1,070 ms | 93.69 ms | 72.97 s |
| `switchback_n8` | 8 / 17 | 163 | `[8, 148, 232, 8]` | 9 / 9 | 883 ms | 97.71 ms | 74.32 s |

Build and the two claim-0 observations were descriptive and never scored.
Build wall depends on cache state. The N=8 geometry has more constraints and
interaction columns than the v4 fit/heldout seven-call programs. The model
uses call count alone, so these extra dimensions were not predictors.

## Verification and scope

The [compact result](language/mixed-cost-v7-transfer-result.json) SHA-256 is
`f620b0ef446e7d4dfa8df28e717822967aa3cc0a3ccde555dbe793bfc5d58127`.
It retains all 164 process pairs, exact source/claim/proof hashes, monotonic
endpoints, native stage and PoW reports, manifests and build walls. All **164
honest proofs** verified with their typed public statements, and all **164
ABI-valid changed public results** rejected at `InvalidMixedInteractionNonce`.
The separate [audit](language/mixed-cost-v7-transfer-audit.json) checked
local source, binary, manifest, statement and proof bytes, recomputed the
frozen [score](language/mixed-cost-v7-transfer-score.json), and independently
replayed every proof and changed claim. Raw artifacts remain locally under
`zig-out/s31-mixed-cost-v7-transfer/`; without that bundle a reviewer can
check the committed hashes and score but cannot replay the same stochastic
proofs.

This is a one-host, one-stack transfer test of v4 predictions on two new
source families at call counts outside the v4 fit set. It does not establish
general cost accuracy, statistical coverage for arbitrary programs, or a
speedup against Cairo. Any successor model needs a new committed fit and a
fresh heldout cohort; this v7 score remains a failure.
