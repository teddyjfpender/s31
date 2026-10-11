# Public record ABI

`binding_v2.py` implements the Python side of the sealed public-record ABI v2
for `direct-gate` relations. Its descriptor preserves nominal record names,
field declaration order, tagged tuple positions, wire references, and
public/private visibility. The native verifier independently validates the
descriptor, its key digest, and the canonical statement. Only M31 leaves are
admitted at this boundary.

The two public readback functions are:

- `decode_typed_public_statement(source, statement_bytes)` validates canonical
  v2 bytes against the relation's ABI and returns named **public** inputs and
  the result. It never returns private input values.
- `encode_typed_public_statement(source, claim)` checks exact roots, field
  shapes, canonical M31 words, aliases, version, and ABI digest, then returns
  the same canonical statement bytes.

For a verified readback, use `s31 inspect-record-proof PACKAGE PROOF`. That
command copies the supplied package, proof, and statement into private
snapshots, checks the package copy, verifies the copied proof with its
generated native verifier, and decodes the copied statement bytes. The codec functions
alone check a claim's format and binding; they do not verify a proof.

`record_v2.py` is the earlier standalone nominal-layout codec. Its layout
digest is separate from the proof-bound descriptor digest in `binding_v2.py`.
See [the worked record examples](../../docs/records.md) and the
[implementation contract](../../../../../design/s31/language/RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md).
