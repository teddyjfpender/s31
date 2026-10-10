# Generated component manifest: direct gate slice

The first generated manifest covers `direct-gate` (`direct-m31-v4`) only. It is
derived from the sealed relation after topology compilation and padding, the
actual direct preprocessed circuit, and the rebound AIR program. A package
contains the manifest as `component-manifest.json`; the same typed value is
embedded in the verification key and reported by `inspect`. The native verifier
recompiles the sealed relation and reconstructs the manifest before reading a
proof. A package reader also checks the artifact, key, and report agree.

For this profile the ordered component list has exactly one entry,
`qm31_ops`. Its source AIR bundle index is 1, but its selected proof index is
0. The manifest records its trace and evaluation log sizes, 12 base trace
columns, 8 interaction trace columns, its constraint count and random
coefficient offset, its ordered preprocessed indices, and a cryptographic
program binding. The latter hashes the pinned AIR bundle bytes, source index,
and rebound component part semantic hashes. The pinned bundle hash is also
recorded separately. These values describe the exact selected AIR; the native
verifier still binds and executes the AIR from the pinned bundle.

The ordered preprocessed list has the eight QM31 operation flags and address /
multiplicity columns. Each entry contains its commitment index, log size, row
count, and SHA-256 of its canonical little-endian M31 values. The existing
preprocessed Merkle root remains the proof's commitment. Per-column digests
make the fixed data independently inspectable and expose altered values even
when an attacker rehashes package metadata. The manifest also records the
source and canonical IR digests, circuit identity, preprocessed root, and the
one claimed sum. It has no fixed lookup table or chip component.

The proof envelope structure and transcript algorithm are unchanged for this
slice. The `direct-gate` key schema is
`s31-verification-key-direct-manifest-v1`; old and new key files are not
interchangeable in newly built verifiers. The schema change alone does not
prevent replay of an otherwise valid proof for the same source and public
statement. A key without this manifest is rejected by newly built verifiers.
An already sealed legacy verifier remains able to read its own legacy key and
proof. Other profiles retain their current keys until each is migrated. The verifier
checks the manifest against the sealed source and pinned AIR rather than
trusting a package-provided digest. Its existing key equality check prevents
substituting a different external key for the embedded one.

## Remaining work

- Extend generation to `direct-chip` and the private bridge. Include the chip
  component and its separate claimed sum, preprocessed geometry, relation
  domain and constraint identity.
- Extend to sparse, wide, full circuit, SHA and recursive profiles. These need
  explicit lookup dependency closure, fixed-table digests, all selected
  component orders, and the exact composition coefficient schedule.
- Make the manifest authoritative for constructing prover and verifier trees,
  rather than a checked description of the existing direct profile layout.
- Version the key and transcript if the manifest ever changes proof semantics;
  a package-only metadata change must not silently redefine an old profile.

This slice proves manifest generation and independent reconstruction for one
existing arithmetic profile. It is not a general component selector.
