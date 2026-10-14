# CAS05 candidate key, statement, and proof boundary

**Status:** audit-only format work. S31's pinned production stwo-zig still
verifies the legacy quotient-only PCS. No S31 build emits this candidate key,
and the admission function always ends with Cas05NotProduction, even when
every field matches. It does not authenticate a commitment, replay a
Fiat–Shamir transcript, verify an AIR, or establish security bits.

The [candidate v6 parser](../runtime/pcs/cas05_candidate_v6.zig) models the
smallest S31-facing interface to the experimental S31CAS05 wire. It is
separate from the Native CPU JSON proof-exchange artifact and the ordinary
S31 S31NAT binary proof envelope.
The field order follows stwo-zig draft PR #249 at commit
234ac67b2819e6b102e8d43da93a38a4a902075e. Any draft wire change needs
a fresh source comparison before this parser can be reused.

## Three independent inputs

| Input | Custody | Fields this gate checks |
| --- | --- | --- |
| Installed key | Exact bytes embedded in a trusted verifier binary; a supplied key must match byte for byte | Distinct s31-verification-key-cas05-candidate-v1 schema, cas05_sparse_v6 mode, S31CAS06 transcript tag, S31XDM04 source-wire tag, source/program digest, public ABI digest when present, circuit hash, AIR-bundle digest, and bounded profile |
| Public statement | Supplied independently of the proof; the installed verifier reconstructs its eight words from the source ABI | Distinct s31-public-statement-cas05-candidate-v1 schema, installed-key SHA-256, eight public words, one source root, and ordered canonical QM31 claims at every profile height and column |
| Proof bytes | Untrusted prover | Exact S31CAS05 outer magic/version 6, reserved fields, declared length, profile/columns, source root and claims matching the key and statement; nested S31XDM04 header/profile/root; bounded line and terminal shapes and canonical field words |

The source root is a **proof commitment asserted by the public statement**;
matching its 32 bytes in the two places is only an equality check. The
candidate gate also parses line roots, coordinates, and terminal words so
that malformed lengths and noncanonical M31 values fail early. It does not
authenticate Merkle paths, derive the sampled OOD point, check paired
quotients/folds, or validate the nested XDM04 opening body.

For example, a key can select two heights with one source column each:

~~~json
{
  "schema": "s31-verification-key-cas05-candidate-v1",
  "pcs_mode": "cas05_sparse_v6",
  "transcript_version": "S31CAS06",
  "source_wire_version": "S31XDM04",
  "profile": {
    "largest_log_size": 6,
    "height_count": 2,
    "log_blowup": 1,
    "query_count": 2,
    "columns": [1, 1, 0, 0, 0, 0, 0, 0]
  }
}
~~~

The actual key also carries exact source, public ABI, circuit, and AIR-bundle
digests. The corresponding statement has public_words, a 64-character
lowercase source_root, and claims shaped as two arrays of one four-limb
QM31 value. Its verification_key_sha256 must hash the *whole installed key
file*, including the profile and all digests. A claim such as [1,0,0,0]
means one canonical QM31 element with first M31 coordinate 1.

## Transcript contract still to connect

The experimental CAS05 v6 verifier in stwo-zig has a concrete absorption
order: version/XDM04 tags, profile and source root before OOD sampling,
ordered height claims before the shared batch challenge, line roots after
each fold challenge, then terminal coefficients before raw queries. Its
complete verifier also authenticates XDM04 and line openings and checks the
paired folds. The S31 candidate key pins the **version tag** but this module
does not execute that schedule.

Production S31 additionally needs a reviewed channel prelude that binds the
installed program/circuit identity and reconstructed public words **before**
CAS05's first challenge. Both prover and verifier must use the same prelude.
The prelude and the source-to-AIR column/claim mapping are not yet specified
or implemented. A proof of the experimental CAS05 relation alone would not
prove that its committed source columns are the S31 program's AIR columns.

Activation requires the reviewed production CAS05 prover/verifier and
canonical wire, a key-selected dispatch into that verifier, exact prelude
and transcript replay, authenticated source/line commitments and statement
binding, compiler-to-AIR correspondence, and a published-proof conservative
PCS/FRI profile. The [P05 migration map](../../../../design/s31/security/PCS_FRI_CAS05_PRODUCTION_MIGRATION.md)
and [blocker matrix](../../../../design/s31/security/pcs-fri-v01-blockers.json)
track those obligations. The candidate admission gate discharges none of
them.
