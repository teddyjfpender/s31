# S31 v0.1 supported-profile audit

`s31_v01_audit.py` enumerates **every lowering exposed by the current `s31
build --lowering` CLI**, plus the supported fold-step-4 schedules for `gate`
and `sparse-wide-gate`. It fails if the lowering inventory changes without a
matrix row. Each row uses a checked-in example and assignment. Nine rows
compile `.s31` text; the three specialized SHA rows use normalized
`.s31.json` relations.

From the repository root:

```sh
python3 -B scripts/release/s31_v01_audit.py --list
python3 -B scripts/release/s31_v01_audit.py --profile direct-gate \
  --out zig-out/s31/release-audit-direct-gate.json
python3 -B scripts/release/s31_v01_audit.py \
  --out zig-out/s31/release-audit-all.json
```

`--list` is a quick inventory and fixture check. It reports every row as
`not-run`. One or more `--profile` arguments select a short native loop; no
`--profile` runs all twelve. Use `gate-fri4` or `sparse-wide-gate-fri4` for
the alternate schedules. A selected row passes only after package integrity,
an honest native proof, generated-verifier acceptance, changed public claim
rejection, altered-key and altered-proof rejection, and an independent
value-oracle check. For text rows, the script
also compares the source relation shape and the package's canonical IR,
component geometry, preprocessing, public binding, finalization, and FRI
report against a handwritten first-order equivalent. Local temporary proof
artifacts are removed after each row; the JSON report retains source, key,
verifier, proof, compiler, and engine identities plus the measured geometry.
The script checks that source and assignment bytes remain stable through each
trial and that reused fixtures have identical recorded hashes across rows.
Reported hashes identify what ran; trusted distribution pins must come
from outside the package and this report.
The command exits nonzero on a selected failure, compiler fingerprint drift,
fixture digest disagreement, or repository commit drift during a native run;
unselected rows remain
`not-run` rather than inheriting an old result.

| Lowering | Fixture type | Exercise |
| --- | --- | --- |
| `gate`, `sparse-gate`, `direct-gate` | Text | Higher-order four-lane square versus handwritten arithmetic |
| `gate-fri4` | Text | Same square with four FRI folds per commitment |
| `chip`, `sparse-chip`, `direct-chip` | Text | Named static recurrence step versus handwritten repeat |
| `sparse-wide-gate` | Text | Checked 256-bit sum versus handwritten wide relation |
| `sparse-wide-gate-fri4` | Text | Same wide sum with four FRI folds per commitment |
| `sha-joint`, `sha-shift`, `sha-fused` | JSON relation | Byte-exact Bitcoin header hash and target relation |

`complete_profile_matrix_passed` only means all twelve finite rows passed **in
that invocation** under one compiler fingerprint that still matches the
compiler at audit completion. `release_candidate_worktree_clean` separately
reports whether the S31 repository and pinned engine had clean worktrees at
both ends of the run. `release_claim` always remains `not-established`: this
command does not prove the Python compiler correct, the production AIR or
PCS/FRI sound, or the general private chip boundary. Public record ABI v2,
recursion, and arbitrary programs have separate
acceptance gates and are outside this matrix. A v0.1.0 release audit must
combine those gates and discharge the remaining obligations in
[`FUNCTIONAL_V01.md`](../../design/s31/language/FUNCTIONAL_V01.md); no tag or
distribution claim follows from this command.
