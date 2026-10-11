# Public record ABI

`binding_v2.py` implements the Python side of the sealed public-record ABI v2
for `direct-gate` relations. Its descriptor preserves nominal record names,
field declaration order, tagged tuple positions, wire references, and
public/private visibility. The native verifier independently validates the
descriptor, its key digest, and the canonical statement. M31 leaves and
public `bit` leaves are admitted. A `bit` occupies one M31 relation/proof
word but its public statement value must be `0` or `1`. Private `bit` leaves
and all `u16` leaves remain outside this boundary.

The two public readback functions are:

- `decode_typed_public_statement(source, statement_bytes)` validates canonical
  v2 bytes against the relation's ABI and returns named **public** inputs and
  the result. It never returns private input values.
- `encode_typed_public_statement(source, claim)` checks exact roots, field
  shapes, canonical M31 words, public bit values, aliases, version, and ABI digest, then returns
  the same canonical statement bytes.

For a verified readback, use `s31 inspect-record-proof PACKAGE PROOF`. That
command copies the supplied package, proof, and statement into private
snapshots, checks the package copy, verifies the copied proof with its
generated native verifier, rejects changes to the copied source, key,
verifier, proof, or statement during verification, and decodes the captured
statement bytes.
`s31 inspect-record-proof-pinned` uses the same readback path after admitting
the copied package against external source, key, prover, verifier, and (for
text packages) source-text SHA-256 pins. Pins must come from a trusted source;
the codec functions alone check a claim's format and binding, not its proof.

`record_v2.py` is the earlier standalone nominal-layout codec. Its layout
digest is separate from the proof-bound descriptor digest in `binding_v2.py`.
See [the worked record examples](../../docs/records.md) and the
[implementation contract](../../../../../design/s31/language/RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md).
