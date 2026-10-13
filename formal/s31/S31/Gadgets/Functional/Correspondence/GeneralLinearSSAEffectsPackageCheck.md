# Generic effectful package admission

[`GeneralLinearSSAEffectsPackageCheck.lean`](GeneralLinearSSAEffectsPackageCheck.lean)
removes the reviewed fixture's hardcoded field inputs. `checkStatic` checks
the exact source, certificate, normalized relation, and public ABI bytes
for any program in the bounded effectful M31 grammar. A compiled package
does not have a witness, so this static result says nothing about whether
its assertions can be satisfied.

The package gate accepts the two exact production v1 ABI encoding labels:
the generic `gate` label and the canonical M31 `direct-gate` label. It checks
the original descriptor and its source-derived field layout before
normalizing the generic label for the existing M31 byte-run theorem. The
public statement still has to contain canonical M31 values.

`checkRun` parses a canonical typed assignment, derives every indexed input
lane and the claimed output from those bytes inside Lean, and calls the
theorem-backed [`checkEffectsByteRun`](GeneralLinearSSAEffectsByteRun.lean).
`checked_run_sound` proves that any accepted run has a source denotation
including all assertions, exact ordered public words, and actual normalized
interpreter acceptance. The caller cannot supply a different interpretation
of its private input lanes.

For production version-1 public statements, `checkRunStatement` parses the
exact canonical JSON bytes given to the native verifier, requires exactly
the assignment's public inputs and outputs, and encodes the eight little
endian M31 words inside Lean before running `checkRun`. The file's byte size
is capped at 65,536. It rejects a private-input field in the public
statement.

The executable `s31-general-linear-effects-package-check` has modes:

```text
static SOURCE CERT RELATION ABI
run SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_WORDS_BIN
statement SOURCE CERT RELATION ABI ASSIGNMENT PUBLIC_STATEMENT_JSON
```

The opt-in Python `verify-effects-lean` command additionally snapshots a
package, checker binary, proof, assignment, and public statement. It requires
external SHA-256 pins for the package and checker, runs Lean's static and
statement gates, then gives the **same captured public statement path** to
the installed native verifier. It rejects a missing checker, wrong checker
pin, unsupported profile, mismatched assignment or statement, and any Lean
failure. Ordinary `verify` and `verify-pinned` retain their existing scope.

This is a bounded source-to-normalized-interpreter semantic admission. It
does not prove production Python parser equivalence, native gate-row custody,
native public-pin ownership, or PCS/FRI soundness. The equality between the
native verifier's JSON statement interpretation and Lean's JSON interpretation
also remains an implementation trust boundary; the wrapper binds identical
statement bytes to both processes.

The private assignment is an independently checked witness for the same
public claim. Native verification sees the public statement, not those
private assignment bytes, so this gate does **not** prove the native proof
used that particular private witness.

## Recheck

```sh
cd formal/s31
lake build s31-general-linear-effects-package-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsPackageCheck
python3 tests/audit/general_linear_effects_package.py
```
