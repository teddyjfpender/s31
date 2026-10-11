# Mixed-stage cost transfer v1: audited, unscored local corpus

**Status: `unscored_missing_frozen_model_bytes`.** Twelve source-embedded
mixed-chip programs produced 360 native-verified proofs under the prospectively
frozen [transfer protocol](MIXED_STAGE_COST_TRANSFER_V1.md). The exact older
training-only `model.json` required by that protocol, SHA-256
`92d4bc1847f7ad69b08c3405e84f7df7e69e9492f403fd7a6286d59c75e9e9f3`,
was not retained in this repository or the available local measurement
directories. **No prediction, interval coverage, diagnostic gate, model
transfer, or speedup result is reported.** A substitute model or refit would
break the frozen protocol.

## Chronology and audit

The candidate protocol was committed before native work and its SHA-256 is
`87f0cccb359ab28501ce9f12d99e83fd2090097e16c1ab5f17d52445b664a862`.
The UTC freeze anchor is full commit
`4ab81c7daf3d01361f487add41e0ab5b8cef6a3f` (15:36:55 UTC). It pins
the exact source/assignment/statement roster, the frozen old model hash,
compiler and Python tools, Zig executable, engine gitlink, host, build mode,
and all gates. Twelve ReleaseFast packages then built once and 360 fresh
prover/external-native-verifier process pairs ran in the frozen interleaved
order. The [raw phase root](language/mixed-stage-cost-transfer-v1-unscored/phase-root.json)
covers 4,069 files, with internal content root
`75aeda466db66aa714719be68c5ef75044f6656a213b96eadcc2cb89152bcb20`.

The first phase-anchor commit,
`089c313b4856b6f9f53020a6324b91c78c71cba3`, mistakenly recorded that
**internal content root** where the audit required the SHA-256 of the
`phase-root.json` **file**. Audit preflight rejected the mismatch before any
native proof replay. Read-only recomputation showed the same 4,069 raw files
and internal root. The corrected UTC phase anchor was committed at
`fb8c8b48c9e53355c4c39c78db7741412d9596a4` (15:58:06 UTC) with the
file SHA-256
`0cd7e3b3bdaaf7f5f84c39d8b2698ad5b8a72d889fd5539b34fba6c4758d5e2f`.
Both commits remain in history. No raw proof, package, or compiler/tool byte
was changed during this correction.

The frozen [native audit](language/mixed-stage-cost-transfer-v1-unscored/audit.json)
then passed: **360/360 original proofs accepted**, and a changed public input
and a changed public result were each rejected for every proof. It replayed
source, assignment, typed statement, package binary and component-manifest
hashes, process/build endpoints, stage lines, proof hashes, and the raw phase
root. The audited [360-trial corpus](language/mixed-stage-cost-transfer-v1-unscored/corpus.json)
has SHA-256
`a1d591bbf7c37703d24b84728f37fd593caf40b61456edba552f85eb8828bd6c`;
the audit SHA-256 is
`16fe257c763a91aa06b0eee73dffb3ebaf944f42a7d88c1ab5ac8b1830379b38`.
The separate [unscored evidence seal](language/mixed-stage-cost-transfer-v1-unscored-evidence-anchor.json)
binds these copies and records that `evaluation.json` was never made. The
ignored frozen-worktree `zig-out/s31-mixed-stage-transfer-v1-20261011`
directory retains full packages, proofs, logs, and raw trial reports; Git
alone cannot replay native verification from the compact corpus.

## Observed values only

Each wall entry is the median of 30 fresh prover-plus-verifier process pairs.
Proof KiB uses 1024 bytes. Package build time is a **separate** one-time
measurement per source, not part of a proof-process wall or a predicted
target. These are descriptive observations, not errors against a model.

| Shape | Live calls | First-verified process wall median | Proof median | Package build wall |
| --- | ---: | ---: | ---: | ---: |
| Control | 2 | 88.79 ms | 82.83 KiB | 61.50 s |
| Control | 4 | 138.80 ms | 111.38 KiB | 55.58 s |
| Control | 6 | 126.29 ms | 139.73 KiB | 54.16 s |
| Feeder | 2 | 120.65 ms | 82.89 KiB | 53.63 s |
| Feeder | 4 | 96.89 ms | 111.21 KiB | 53.30 s |
| Feeder | 6 | 126.12 ms | 140.10 KiB | 53.40 s |
| Fork | 2 | 114.33 ms | 83.52 KiB | 53.27 s |
| Fork | 4 | 104.91 ms | 111.44 KiB | 53.27 s |
| Fork | 6 | 107.83 ms | 140.30 KiB | 53.13 s |
| Deep32 | 2 | 106.57 ms | 82.42 KiB | 53.79 s |
| Deep32 | 4 | 85.49 ms | 111.65 KiB | 53.46 s |
| Deep32 | 6 | 108.93 ms | 139.70 KiB | 53.25 s |

The pinned older reference protocol has compiler fingerprint
`c239a0e26ad812ada345cac8da63d852f41721689492029ee2f3281698cd7668`.
This measured frozen worktree has fingerprint
`9845d65e43f7233226b0e679535fa0e9efa750f5521d08ef3983e0ca33d019a9`.
At publication review, current PR HEAD `b903769d48dc6f399d27cbfd32e81d87931dbf32`
has fingerprint
`0a4a41ba1b9df806156d45e7d0d3356ca414f9ed7130624600aa10508bb2b46c`.
These are three distinct compiler fingerprints; this corpus only measures the
frozen worktree. All use the pinned engine gitlink
`7d544c6839497ca19b6c7ef9b982e464f10cfeed` where applicable.

The earlier [mixed-stage v1 result](MIXED_STAGE_COST_MODEL_V1_RESULT.md)
documented the missing artifact's hash and training-only freeze, but did not
commit the model bytes. Neither the tracked Git object history nor available
local measurement directories or snapshots supplied those exact bytes. A
future prospective study needs a retention gate that commits or externally
archives the frozen model bytes, checks their hash, and verifies retrieval
**before** any held-out build. This run is intentionally left unscored.
