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

## Bounded multi-field record row certificate

[`record_v2_multifield_row_certificate.py`](record_v2_multifield_row_certificate.py)
is an opt-in path for the nominal scalar record-v2 grammar, including public
and private inputs and flat record-pattern aliases. It runs exact-byte Lean
source-to-typed-`Program` admission, a source-derived audit of live native
Gate rows and their exact use counts, full fixed-column recommitment to the
pinned key, typed public statement checks, and native proof verification in
one private snapshot. Supply the same five package pins and a separately
pinned `s31-general-record-v2-program-admission-check` executable. The
[worked two-field example](../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneralRecordV2MultiFieldNativeRows.md)
shows the exact source, field values, physical rows, and proof boundary.

This certificate is not part of the v0.1.0 supported-profile release gate.
It does not identify the native proof's private witness or prove the native
PCS/FRI, Gate lookup, or verifier implementation sound.

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

The experimental CAS05 branch has a separate
[short-cascade field-capacity diagnostic](pcs_fri_cas05_field_capacity.py) and
[decision ledger](../../design/s31/security/PCS_FRI_CAS05_CONSERVATIVE_PROFILE_DECISION.md).
It compares exact published unique-decoding expressions for hypothetical
even-degree challenge fields and distinguishes absolute error from the
paper's work-factor convention. Its `--require-proven` option always fails;
the calculation neither admits CAS05 nor assigns native security bits.

For the reviewed draft PR #249 revision, the
[P05 source/profile diagnostic](pcs_fri_cas05_source_profile.py) checks the
exact draft Git commit and seven source hashes before calculating sparse
verifier, legacy XDM03 host, bounded CAS05 host, terminal, and candidate
small-table geometry. It does
not change the production blocker matrix. See the
[production migration map](../../design/s31/security/PCS_FRI_CAS05_PRODUCTION_MIGRATION.md)
for proof-format, dispatch, pinning, testing, and theorem steps. The draft
source is separate from S31's pinned engine; `--require-proven` remains closed.

The [CAS07 Gate roster audit](pcs_fri_cas07_gate_roster.py) checks one sealed
Gate package against the exact experimental sparse-height draft and derives
its proposed ordered source slots. Its [worked analysis](../../design/s31/security/PCS_FRI_CAS07_GATE_ROSTER_AUDIT.md)
shows the 311-column candidate roster, the eight omitted composition
columns, and why the existing four commitment epochs cannot be collapsed
into one XDM05 root by metadata alone. It rejects a changed draft source or
unreviewed Gate geometry; `--require-production-equivalent` remains closed.

The [Gate paper-batch boundary](pcs_fri_gate_paper_batch_boundary.py) inventories
all four production roots and their source heights from a sealed legacy Gate
key. Its [review](../../design/s31/security/PCS_FRI_GATE_PAPER_BATCH_BOUNDARY.md)
derives a conditional exact-arithmetic cap: at hypothetical `N=2^20, B=2`
and selected `T=2^64`, the quoted paper batching term crosses the 96-bit
work-factor target at `M=65`. The actual native proof has no identified paper
ensemble width `M`; `--require-paper-mapping` fails closed.

The [raw Gate BCS transcript audit](pcs_fri_raw_gate_bcs.py) source-pins its
distinct proof-byte selector, verifier challenge/commitment epochs, PoW
barriers, whole-block rejection and nine raw query hash blocks. Its
[security review](../../design/s31/security/PCS_FRI_RAW_GATE_BCS_AUDIT.md)
separates exact fixed-prefix counts and hypothetical 256-bit paper collision
arithmetic from the still-open native adaptive BCS and P09 bound.
It also source-pins the raw channel/plain Merkle hash-input role overlap and
the exact paper-only 162-bit collision-term threshold at `T=2^64`. Neither
assigns a native collision width or establishes the adaptive reduction.
`--require-adaptive-bcs` fails closed.

The proposed [framed BCS v2 byte model](pcs_fri_framed_bcs_v2.py) reserves a
new proof selector and separates root, field, nonce, draw and Merkle hash-input
roles with a canonical length/event frame. Its
[engineering brief](../../design/s31/security/PCS_FRI_FRAMED_BCS_V2_DESIGN.md)
aligns the two FRI degree tracks with the four Gate source roots and costs the
extra Merkle hashing. The model has no native selector or soundness theorem;
`--require-native-soundness` fails closed.

The candidate [line-tree descriptor model](pcs_fri_line_descriptor_v2.py)
pins the versioned tree geometry, ordered column roster and named root event
inside the initial statement digest. Its
[byte and custody brief](../../design/s31/security/line-tree-descriptor-v2.md)
lists the selected-verifier obligations, including consistent query
projection through every Circle FRI fold. It does not change release
admission.

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
escape that root. The bundler rechecks the same three candidate receipts,
remote branch tip, and exact S31 Gitlink before writing an archive:

```sh
python3 -B scripts/release/source_bundle.py \
  --tag v0.1.0-rc.N \
  --audit zig-out/s31/release-audit-candidate.json \
  --features zig-out/s31/feature-gate-full-final.json \
  --formal zig-out/s31/formal-checks-final.json \
  --compiler-sha256 '<PINNED_COMPILER_SHA256>' \
  --branch '<RELEASE_BRANCH>' \
  --out zig-out/s31/s31-v0.1.0-rc.N-source-with-stwo-zig.tar.gz
```

Extract into a directory outside another Git checkout and run the bundled
`SOURCE-BUNDLE.md` instructions. The bundle has no `.git` directories. Its
`SOURCE-BUNDLE.json` pins both commits, both Git tree IDs, a SHA-256 over the
engine code and build assets used by S31, and the compiler fingerprint. The
manifest also pins SHA-256 hashes of the three candidate receipts. The final
`v0.1.0` tag fails closed: the current native PCS/FRI blocker matrix has no
proven security bits, and no whole-compiler correspondence release checker
exists. A stale blocker snapshot also rejects; refresh it only after reviewing
the changed source and proof obligations. Only `v0.1.0-rc.N` developer candidate
bundles can be made until both proof obligations have source-bound release
certificates. Candidate receipts check finite profiles; they do not certify
general soundness.

The compiler validates the engine digest and fingerprint before building a package.
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
