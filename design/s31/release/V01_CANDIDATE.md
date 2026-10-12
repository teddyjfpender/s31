# S31 v0.1 scoped release candidate

This is a **candidate for a bounded developer release**, not a general proof
of compiler correctness, STARK soundness, or witness confidentiality. A
candidate may be published only after the check below passes on the exact
clean commit at the named remote branch tip. A passing check establishes that
the named finite evidence ran, its identities agree, and the candidate has
not changed the pinned compiler fingerprint. It does not infer untested
program behavior from those samples.

## What is in scope

The twelve-row native matrix covers every current `s31 build --lowering`
choice, with the two additional FRI fold-step-4 schedules. It tests one
checked-in fixture and assignment per row. Nine rows compile `.s31` text and
compare its canonical IR and reported AIR geometry against a handwritten
first-order equivalent. The three specialized SHA rows start from normalized
JSON relations. Every row requires an accepted native proof, independent
value oracle, changed public claim rejection, altered key rejection, and
damaged proof rejection. This is **one fixture per profile**, not a claim over
all source programs.

The seventeen-check feature matrix covers typed source arithmetic for
`u8`–`u128` and `i8`–`i128`, checked and wrapping multiplication, bounded
record source rules, public `u8`/`u16`/`u32` record ABI examples, and native
controls for the supported direct arithmetic and public record cases. Public
`u32` record leaves use two little-endian 16-bit limbs and range constraints;
the direct-gate result must alias a public input. The feature gate's finite
controls do not admit private or derived narrow leaves, or narrow leaves in
chip or mixed profiles.

The formal gate checks that the committed Lean inventory and source bindings
match the candidate tree, `lake build S31` succeeded, and `leanchecker S31`
succeeded for the evidence-bearing revision. Lean proofs cover specified local
semantics and scoped correspondence lemmas. **Full production compiler
correspondence, native PCS/FRI refinement, and a general soundness theorem
remain open.**

Source `private` means omitted from the public statement. The current
experimental mixed bridge puts private endpoint words into constant committed
columns, and accepted proof openings disclose them to a proof holder. Do not
use these profiles when witness secrecy is required. A confidential proof
version needs trace and transcript masking plus a zero-knowledge argument.

The paired fixed-integer measurements identify proof size and preprocessing
cell savings for their measured witnesses. They do not establish a reliable
current-host whole-prover timing or automatic lowering policy; deterministic
FRI proof-of-work searches have high variation. No cross-host speed claim is
part of this release candidate.

## Candidate gate

Run the native matrix and feature gate on a clean, pinned source revision,
then run the formal commands. Keep all three formal command logs. Produce a
JSON formal receipt of this shape (actual hashes and paths are required):

```json
{
  "schema": "s31-v01-formal-checks-v1",
  "source_commit": "<40- or 64-character git commit of formal run>",
  "compiler_sha256": "<64-character compiler fingerprint>",
  "inventory_sha256": "<SHA-256 of formal/s31/proof-inventory.json>",
  "bindings_sha256": "<SHA-256 of formal/s31/source-bindings.json>",
  "checks": {
    "bindings": {"command": ["python3", "-B", "scripts/s31_formal.py"], "returncode": 0, "log": "<path>", "log_sha256": "<SHA-256>"},
    "lake_build": {"command": ["lake", "build", "S31"], "returncode": 0, "log": "<path>", "log_sha256": "<SHA-256>"},
    "leanchecker": {"command": ["lake", "env", "leanchecker", "S31"], "returncode": 0, "log": "<path>", "log_sha256": "<SHA-256>"}
  }
}
```

The logs are command evidence supplied by the release operator, not
cryptographic attestations. The checker verifies their current bytes and the
committed inventory bytes. A formal run may follow the native audit commit if
the audit, formal, and candidate commits are ancestors of the candidate; all
must share the same compiler fingerprint. The audit's engine commit must still
be checked out and clean.

After the candidate commit is pushed, run:

```sh
python3 -B scripts/release/release_candidate.py \
  --audit zig-out/s31/release-audit-candidate.json \
  --features zig-out/s31/feature-gate-full-final.json \
  --formal zig-out/s31/formal-checks-final.json \
  --compiler-sha256 '<PINNED_COMPILER_SHA256>' \
  --branch feat/s31-v01-release-20261011 \
  --out zig-out/s31/release-candidate-check.json
```

The checker rejects a missing/partial row, failed control, compiler mismatch,
changed audit fixtures or release runners, stale formal inventory, changed Lean
sources or binding checker since the formal report, failed or missing formal log,
dirty worktree, engine drift, or a candidate commit absent from the remote branch tip. Its success
status is `scoped-candidate-gates-passed`. The release operator must still
review the source, evidence provenance and disclosed limitations before a tag
or distribution. The checker does not publish anything.
