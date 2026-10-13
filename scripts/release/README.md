# S31 v0.1 supported-profile audit

## Bounded M31 structural release verification

For a direct-Gate package in the Lean `linear-ssa-m31-effects-v1` structural grammar, use
[`structural_lean_release.py`](structural_lean_release.py) to verify a proof.
This strict release class requires every structural, source-relation, and ABI
artifact and a separately pinned Lean executable. It checks a captured package
with Lean before the native verifier receives the same captured proof and
public statement. Missing artifacts, an absent checker, a wrong checker pin,
and unsupported source grammar fail closed. Supply all six SHA-256 pins from
an authenticated channel outside the package:

```sh
python3 -B scripts/release/structural_lean_release.py PACKAGE PROOF \
  --statement PROOF.statement.json \
  --source-sha256 SOURCE_JSON_SHA256 --text-sha256 SOURCE_TEXT_SHA256 \
  --key-sha256 KEY_SHA256 --prover-sha256 PROVER_SHA256 \
  --verifier-sha256 VERIFIER_SHA256 \
  --lean-checker formal/s31/.lake/build/bin/s31-general-linear-structural-check \
  --lean-checker-sha256 CHECKER_SHA256
```

The full release-candidate feature gate requires a real two-lane helper and
tuple package to pass this command and native proof verification. It also
requires wrong-checker-pin and missing-tree rejection. `release_candidate.py`
rejects a full feature receipt that omits those controls or whose checker
digest differs from the formal receipt's built executable. The older
`s31 verify-release` command covers a separate direct-Gate
certificate class and does not invoke this Lean checker. Neither path proves
native AIR or PCS/FRI soundness. This package gate checks source, relation,
tree, and public ABI bytes; it does not check a private assignment against a
particular proof.

## Proven PCS/FRI preflight

The v0.1.0 policy requires a published, implementation-matched PCS/FRI
soundness bound. The current fixed `pow=26, blowup=2, queries=70` profile is
only a nominal target. Run the exact-arithmetic [published-bound preflight](pcs_fri_proven_preflight.py)
to inspect necessary Johnson-regime query arithmetic for an illustrative
geometry:

```sh
python3 -B scripts/release/pcs_fri_proven_preflight.py
python3 -B scripts/release/pcs_fri_proven_preflight.py --require-proven
```

The preflight also bounds the tiny bias introduced when the native M31
channel reduces BLAKE2s words before masking query indices. This is
conditional ideal-oracle arithmetic, not a native Fiat–Shamir proof.

For one sealed fold-step-1 gate package with a `2^20` maximum trace and
conditional `2^21` FRI input domain, the
[fail-closed error ledger](pcs_fri_gate_error_ledger.py) records the actual
source-bound observations beside the still-unassigned theorem parameters,
per-round errors, adversary budget, ROM and Merkle collision terms. See its
[scope and formulas](../../design/s31/security/PCS_FRI_GATE_ERROR_LEDGER.md).

`--require-proven` exits nonzero until native protocol refinement, all
published error terms, and cryptographic assumptions have a checked release
certificate. Passing native acceptance tests or increasing the query count
does not change that status. See the [bound audit](../../design/s31/security/PCS_FRI_PUBLISHED_BOUND_AUDIT.md)
for the precise missing interfaces.

For the complete v0.1 profile roster, inspect the
[machine-readable blocker matrix](../../design/s31/security/pcs-fri-v01-blockers.json)
and its [independent review](../../design/s31/security/PCS_FRI_V01_BLOCKER_REVIEW_2026-10-13.md):

```sh
python3 -B scripts/release/pcs_fri_v01_blockers.py --check
python3 -B scripts/release/pcs_fri_v01_blockers.py --check --require-admissible
```

The first command rejects a stale source/profile snapshot. The second also
exits nonzero while any published-proof obligation remains open. This matrix
does not upgrade scoped candidate gates into a proven-security release.

The [query epoch source audit](../s31_formal_lib/pcs_fri_query_epoch.py) checks
one bounded part of P07:

```sh
python3 -B -m scripts.s31_formal_lib.pcs_fri_query_epoch
```

For the pinned v0.1 path, the post-PoW raw-query epoch uses counters 0–8.
The native BLAKE2s channel now traps before counter overflow in any draw,
including an unbounded rejection loop. The report still leaves a formal
full-transcript control-flow argument and random-oracle independence unproved.

The selected direct Gate has a further [P07 byte-level transcript refinement](../../design/s31/security/PCS_FRI_BCS_TRANSCRIPT_REFINEMENT.md):
an independent Python model is checked against a native Zig replay for both
PoW barriers, lookup/PCS/FRI challenge draws, and all 70 raw queries. The
source audit rejects order and encoding mutations. This is deterministic
correspondence evidence, not a BCS or 96-bit soundness certificate.

## Formal receipt

Run the Lean source-binding check, full build, and kernel replay on a clean
candidate commit with one Lean thread. The receipt tool executes the commands
in that order, saves each complete command log and its SHA-256, and rejects
command failure or a source, compiler, inventory, or worktree change during
the run:

```sh
python3 -B scripts/release/formal_receipt.py \
  --out zig-out/s31/formal-checks.json
```

The generated JSON has the `s31-v01-formal-checks-v1` shape required by the
candidate checker. A command failure or detected drift writes a receipt marked
`failed`; a setup error exits without a receipt. Neither can be used as
passing release evidence. The receipt pins the tool's own
source hash, which the candidate checker compares with the current tree. The
command runs no native proof.

## Complete source bundle

GitHub's automatic source archives omit `deps/stwo-zig`. After the candidate
checker passes on a clean commit, make an offline-buildable archive containing
the **complete tracked source trees** at the candidate and pinned engine
commits. Every archive member must stay under the single tag-named root;
long Git paths are covered by a PAX regression test, and symlinks may not
escape that root:

```sh
python3 -B scripts/release/source_bundle.py --tag v0.1.0-rc.N \
  --out zig-out/s31/s31-v0.1.0-rc.N-source-with-stwo-zig.tar.gz
```

Extract into a directory outside another Git checkout and run the bundled
`SOURCE-BUNDLE.md` instructions. The bundle has no `.git` directories. Its
`SOURCE-BUNDLE.json` pins both commits, both Git tree IDs, a SHA-256 over the
engine code and build assets used by S31, and the compiler fingerprint. The
compiler validates the engine digest and fingerprint before building a package.
Publish and independently check the archive's SHA-256 alongside the asset.
The bundle is complete rather than a selected set of engine files; its size is
dominated by tracked stwo-zig test vectors and research reports.

## Supported-profile audit

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
