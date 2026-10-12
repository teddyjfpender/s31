# Public record ABI

`binding_v2.py` implements the Python side of the sealed public-record ABI v2
for `direct-gate` relations. Its descriptor preserves nominal record names,
field declaration order, tagged tuple positions, wire references, and
public/private visibility. The native verifier independently validates the
descriptor, its key digest, and the canonical statement. M31 leaves, public
`bit` leaves, and public `u16`/`u32` leaves are admitted under `direct-gate`. A
`bit` occupies one M31 relation/proof word but its public statement value
must be `0` or `1`. A public `u16` input word is decomposed into 16 Boolean
arithmetic gates and reconstructed in the circuit; its claimed statement
value must be below 65536. A `u16` result leaf must alias one of those
public input wires. Private `bit`/`u16` leaves and derived `u16` result wires
remain outside this boundary. `direct-chip` and `direct-mixed-general` do
not admit this u16 shape. A public `u32` scalar is represented by two
little-endian `u16` relation limbs. Direct Gate proves 16 Boolean bits for
each limb; the result must alias a public input wire with the same `u32`
tag. Private `u32` inputs, derived `u32` results, and the chip profile are
excluded. The descriptor digest distinguishes `u32` from `[u16; 2]` even
though both use the same two-limb range circuit.
The native canonical JSON writer rejects nesting beyond 128 containers;
valid v2 type trees are limited to 32 record or tuple edges. Malformed deep
statement values fail before proof decoding.
For v2 source, this statement check also permits a public bit input to be
passed through or left unused without adding a Boolean computation node;
the v1 source boundary still requires a Boolean operation or select.

The two public readback functions are:

- `decode_typed_public_statement(source, statement_bytes)` validates canonical
  v2 bytes against the relation's ABI and returns named **public** inputs and
  the result. It never returns private input values.
- `encode_typed_public_statement(source, claim)` checks exact roots, field
  shapes, canonical M31/u16/u32 limbs, public bit values, aliases, version, and ABI digest, then returns
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
