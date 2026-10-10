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

The current schema, `s31-component-manifest-direct-chip-v2`, describes the
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

The v2 key schema is `s31-verification-key-direct-chip-manifest-v2` and its
proof envelopes start with `S31NAT6C` (public) or `S31NAT6P` (private). Older
v1 packages remain readable with their own sealed binaries. The v2 verifier
rejects a v1 key or proof tag. The source identity in the key remains the
SHA-256 of the literal program bytes.

Before proving, the compiler hashes a typed, length-delimited encoding of
the generated manifest, including ordered components, sum indices, offsets,
fixed columns, chip parameters, and private endpoint addresses. It omits
`circuit_hash` because that value depends on the transcript binding. The
preprocessed root is safe to include: it is computed from fixed circuit data
first. The key and `inspect` expose this hash as
`manifest_precommitment_sha256`. The engine receives a separate effective
source digest:

```text
manifest_digest = SHA256("S31-COMPONENT-MANIFEST-PRECOMMIT-V2\0" || typed_manifest_without_circuit_hash)
effective_digest = SHA256("S31-DIRECT-CHIP-MANIFEST-TRANSCRIPT-V2\0" || true_source_digest || manifest_digest)
```

The encoding is fixed and typed: strings are UTF-8 with a little-endian
`u64` byte length; list lengths and `usize` fields are little-endian `u64`;
`u32` fields are little-endian four-byte words; optional values start with a
one-byte `0` or `1`. The ordered fields are:

1. schema, profile, source digest, canonical IR digest, AIR bundle digest,
   preprocessed root, composition plan hash, claimed-sum count;
2. component count, then for each component: name, source and proof indices,
   trace and evaluation logs, base and interaction widths, constraint count,
   coefficient offset, ordered trace spans, ordered fixed-column indices,
   AIR binding digest, optional claimed-sum index, optional main and
   interaction spans, optional degree bound, and optional ordered lookup IDs;
3. fixed-column count, then for each column: ID, commitment index, log size,
   row count, and values digest;
4. optional chip call: call ID, relation ID, rounds, constant, and optional
   four input plus four output boundary addresses.

Each span is three `u32` words `(tree, start, end)`. `circuit_hash` is
excluded. The Python package reader independently reconstructs this digest
from the sidecar and compares it with the key and report.

The engine mixes `effective_digest` before its first witness/base commitment
and uses it in the circuit identity. The verifier regenerates the typed manifest from
its sealed source and pinned AIR, checks the key's digest, and derives the
same effective digest before it verifies the proof. The digest contains no
witness values. This is a precommitment to the one-call roster, while the
engine's component constructors remain explicit code. A future multi-call
profile needs a new lookup tuple with call ID and its own versioned transcript.

### What `source_index` identifies

The sealed v1/v2 JSON inherited one integer called `source_index`, but it
encodes two different source classes. `qm31_ops` has `source_index: 1`: it is
selected from the pinned AIR bundle at index 1 and placed at proof index 0.
The chip and bridge have `source_index: 0`: zero is a **native AIR sentinel**,
not another bundle index. Their `name` and `program_binding_sha256` distinguish
the pinned Zig AIR and its parameters. For example:

| Proof index | Name | `source_index` | Internal source role |
| ---: | --- | ---: | --- |
| 0 | `qm31_ops` | 1 | Bundled AIR 1 |
| 1 | `repeated_step_chip` | 0 | Native repeated-step AIR |
| 2, if private | `private_boundary_bridge` | 0 | Native bridge AIR |

The manifest generator and key matcher now resolve these pairs to an internal
tagged source role and reject an unknown native name, wrong source index, or
wrong proof/claimed-sum position. This adds a fail-closed check without
changing existing sealed JSON, key schemas, digest domains, or proof tags.
It does **not** make `source_index: 0` a sufficient identity for a general
scheduler. A future versioned manifest must serialize an explicit source
kind and stable program identity and derive the constructed component from
that typed reference. The staged two-call profile also uses the legacy
sentinel for its native tagged chip and bridge; it is not a released general
manifest scheduler.

## Remaining work

- Extend to sparse, wide, full circuit, SHA and recursive profiles. These need
  explicit lookup dependency closure, fixed-table digests, all selected
  component orders, and the exact composition coefficient schedule.
- Make the manifest authoritative for constructing prover and verifier trees,
  rather than a checked description of the existing direct profile layout.
- Give a future multi-call schema its own key, proof envelope, typed digest
  domain, and transcript so one-call proofs cannot be reinterpreted.

These slices establish manifest generation and independent reconstruction for
the direct arithmetic profiles. They do not yet provide a general component
selector or a multi-call chip boundary.

## Single-call security boundary

For multiple chip calls, the roster needs an instance index and explicit
multiset multiplicities; the current single-call bridge cannot supply that
information. The private bridge authenticates a private endpoint but its
opened columns can reveal that value. No secrecy guarantee follows from this
manifest.
