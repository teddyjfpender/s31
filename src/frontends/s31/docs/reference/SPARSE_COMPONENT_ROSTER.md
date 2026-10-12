# Sparse gate AIR component roster

The `sparse-gate` compiler emits `sparse-component-roster.json` with schema
`s31-component-roster-sparse-gate-v1`. It rebuilds this roster from the
finalized source circuit and the sparse preprocessing used by the proof.
The native verifier independently rebuilds it from its embedded source before
accepting a proof.

The sparse AIR has three claimed components, in this proof order:

| Proof and claim index | Source AIR index | Component | Main columns | Interaction columns | Trace log size |
| ---: | ---: | --- | ---: | ---: | --- |
| 0 | 1 | `qm31_ops` | 12 | 8 | `qm31_ops_in0_address` column |
| 1 | 3 | `m_31_to_u_32` | 4 | 12 | `m31_to_u32_input_addr` column |
| 2 | 10 | `range_check_16` | 1 | 4 | fixed at 16 |

The first two row counts depend on the compiled circuit. For example, a
16-row arithmetic trace gives each of those components log size 4, while
the range table remains 65,536 rows (log size 16). The roster also lists the
12 fixed columns in commitment order with their ID, log size, row count, and
SHA-256 of their little-endian M31 values. The table above describes widths
and ordering; the emitted JSON contains actual row counts and hashes.

`s31-verification-key-sparse-roster-v1` carries
`sparse_component_roster_sha256`. This digest is SHA-256 of
`S31-SPARSE-GATE-COMPONENT-ROSTER-V1\0` followed by the compact typed roster
JSON. The package checker requires matching key, cost report, and sidecar.
The native verifier independently reconstructs and compares the digest from
the source it was compiled with. A key with a coherently resealed false
digest, a changed claim, a rehashed sidecar edit, or a downgrade to the old
`s31-verification-key-v3` schema is rejected by the appropriate check.

This changes the **new sparse package key** and inspection artifacts. It
does not change the `S31NAT3G` proof bytes or introduce a new Fiat–Shamir
input. The circuit identity and fixed commitment root continue to be checked
by the native verifier. The old sparse key schema remains historical; the
new verifier requires the roster-bearing schema.
