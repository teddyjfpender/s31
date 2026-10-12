# Gate AIR component roster

The transparent `gate` profile now emits `gate-component-roster.json` with
schema `s31-component-roster-gate-v1`. The compiler builds it from the same
finalized circuit and preprocessed columns used for the proof. Its 11 entries
follow the circuit AIR evaluator order: `eq`, `qm31_ops`, `triple_xor`,
`m_31_to_u_32`, `blake_g_gate`, five bitwise XOR table components, and
`range_check_16`. Each entry records its proof and claimed-sum index, trace
log size, main and interaction column widths, log-size source, and lookup
uses per row. Each fixed column records its commitment index, ID, log size,
row count, and SHA-256 of its little-endian M31 values.

For example, a small `affine4_v1` circuit has 11 proof components. Its
`qm31_ops` component uses 12 main and
8 interaction columns, and the bitwise table components still appear at
their fixed sizes. The full roster is about 14 KB, while the sealed key
contains only `gate_component_roster_sha256` and remains about 1 KB.

The digest is SHA-256 of the ASCII domain
`S31-GATE-COMPONENT-ROSTER-V1\0` followed by the compact JSON serialization
of the typed Zig roster. The Python package checker reconstructs that order
before hashing, so JSON file key order and whitespace do not affect it. A
native verifier compiled with the key rebuilds the roster from its embedded
source and compares its digest before reading the proof. The package checker
also requires the roster file, report, and key digest to agree.

This is an authenticated **key extension for new transparent gate packages**.
The existing circuit proof transcript is unchanged: the roster digest is
not separately mixed into Fiat–Shamir. The circuit identity and fixed root
remain checked by the existing native verifier. The roster makes that
compiled geometry inspectable and rejects a key whose declared roster differs
from the verifier's own construction. A coherent edit to all package JSON
files can pass package consistency checks alone; it fails in the native
verifier unless the embedded source produces that edited roster.

Historical `s31-verification-key-v1` packages have no roster and retain
their old verifier semantics. Blinded `gate` packages also retain their
separate key schema. The new transparent gate key schema is
`s31-verification-key-gate-roster-v1`; stripping the roster or changing its
schema is rejected by the new verifier. This slice does not expose AIR
constraint polynomials, proof query indices, or a transcript-level manifest
commitment for the old gate proof format.
