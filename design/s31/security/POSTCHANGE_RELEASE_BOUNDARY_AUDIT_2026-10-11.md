# Release boundary audit, 2026-10-11

Scope: the opt-in bounded direct-gate release path and the current uncommitted
checkpoint snapshot changes. This review looked for a package, proof, or
statement substitution that could cause a successful verification claim for
different bytes than those checked. It did not review the Stwo PCS/FRI verifier.

## Corrected checkpoint path gap

`runtime/folds.py::_audit_fold_chain_admitted` previously called
`Path.resolve()` on each checkpoint and then read its proof and statement with
`Path.open()`. This followed a linked proof or parent directory, changed which
adjacent statement was selected for a linked proof, and allowed a file to be
replaced between path resolution and opening. It also used a blocking open on
untrusted file types. The loop now uses `runtime/proof_inputs.py`'s bounded
`proof_inputs_snapshot`, which opens each path component without following
links, checks regular files, captures each input from one opened descriptor,
and checks the private copies again after native verification. The fold
statement limit remains 4096 bytes. A linked proof, linked statement, or
linked parent now fails before invoking the native verifier.

The focused regression is
`tests/python/security/test_recursive_verification_snapshot.py`; its six
tests pass. The complete Python security directory passes 48/48 tests.

## Checked release path

`package/trust.py` copies every directory entry under hard per-file, total
byte, and entry limits before validating the copy. `admitted_snapshot` checks
externally supplied SHA-256 pins for source relation, verifier key, prover,
verifier, and original text when present. `release_admission.py` requires the
v2 direct-gate key, recomputes the certificate with
`package/correspondence.py`, and calls the copied native verifier's
`check-key`. `cli/commands.py` snapshots proof and statement inputs before
package admission, invokes only the copied verifier with the copied key, and
prints native success only after both snapshot contexts exit cleanly.

The correspondence checker independently reparses exact bounded source
bytes, rebuilds canonical IR bytes, requires the normalized relation and
native source schedule, replays every direct-gate fixed row, and compares the
exported fixed root to the pinned key. These checks support the opt-in
1–16-gate fragment only. A package's manifest hashes alone do not authenticate
the five externally pinned artifacts. No bypass was found in this pass.

## Remaining trust limits

The private copies protect against changes to the caller's original paths.
They are not an operating-system isolation boundary against another process
running as the same user: such a process could discover and transiently edit
a temporary copied file during native execution, then restore it before the
post-verification digest check. A malicious externally pinned executable is
also trusted executable code. Applications facing same-user adversaries need
OS process isolation or an API that passes opened, unlinked file descriptors
to the verifier and binds the exact bytes read. Fold-chain checkpoints are
captured one at a time after package admission, so the API authenticates each
captured checkpoint, not a pre-admission snapshot of the entire original path
list. The current source-to-fixed-row checks do not prove that the PCS
commitment, Gate lookup, AIR, FRI, or the native verifier implementation is
sound.
