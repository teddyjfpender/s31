# Generated component manifests: direct M31 profiles

The first generated manifest covered `direct-gate` (`direct-m31-v4`). It is
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

## One-call direct-chip roster

The next schema, `s31-component-manifest-direct-chip-v1`, describes the
existing one-call `direct-chip` proof. The public variant has two components
in proof and claimed-sum order: `qm31_ops`, `repeated_step_chip`. The private
variant adds `private_boundary_bridge` as component and sum index 2. The
bridge's eight endpoint addresses come from compiler topology and are
included in the manifest; proof bytes cannot choose them. The call ID is
fixed at zero because the current six-field chip lookup tuple has no call ID.
Consequently this schema permits exactly one call.

| Component | Main columns | Interaction columns | Log size | Constraints | Lookup relations |
| --- | ---: | ---: | --- | ---: | --- |
| `qm31_ops` | `[0,12)` | `[0,8)` | circuit log | selected AIR count | circuit Gate |
| `repeated_step_chip` | `[12,21)` | `[8,16)` | `log2(rounds)` | 6 | chip state |
| `private_boundary_bridge` | `[21,29)` | `[16,36)` | 4 | 5 | circuit Gate, chip state |

These are offsets in commitment trees 1 and 2. Tree 0 still contains the
eight fixed QM31 circuit columns; the chip and bridge have no fixed columns.
Each roster row records its ordered claimed-sum index, degree bound, trace
spans, source index, and a SHA-256 binding of the selected AIR source and
parameters. The circuit row retains the pinned AIR bundle binding. The
verifier recomputes the manifest from sealed source and AIR before it reads
proof bytes. The native prover and verifier still construct the selected
components with their existing explicit code; manifest equality checks that
the key describes that code's layout. This is a checked schedule, not yet a
manifest-driven scheduler.

The new key schema is `s31-verification-key-direct-chip-manifest-v1`. Its
proof envelope and transcript remain the existing direct-chip profile. The
source digest, chip parameters, and private addresses already enter that
transcript. The manifest itself is checked against sealed compiler output and
native AIR source before proof deserialization, but its JSON digest is not
mixed as an additional transcript element. A future multi-call profile needs
a new chip tuple with call ID and a separately versioned transcript.

## Remaining work

- Extend to sparse, wide, full circuit, SHA and recursive profiles. These need
  explicit lookup dependency closure, fixed-table digests, all selected
  component orders, and the exact composition coefficient schedule.
- Make the manifest authoritative for constructing prover and verifier trees,
  rather than a checked description of the existing direct profile layout.
- Version the key and transcript if the manifest ever changes proof semantics;
  a package-only metadata change must not silently redefine an old profile.

These slices establish manifest generation and independent reconstruction for
the direct arithmetic profiles. They do not yet provide a general component
selector or a multi-call chip boundary.

## Single-call security boundary

For multiple chip calls, the roster needs an instance index and explicit
multiset multiplicities; the current single-call bridge cannot supply that
information. The private bridge authenticates a private endpoint but its
opened columns can reveal that value. No secrecy guarantee follows from this
manifest.
