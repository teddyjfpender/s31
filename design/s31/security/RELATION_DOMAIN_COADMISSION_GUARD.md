# Mixed lookup relation co-admission guard

Status: source-derived mixed registry check; native tests pending.

The general pair/many manifest now constructs a `RelationDomain` while it
walks the source-selected component roster. Each registered constructor
declares the relation ID, tuple arity, and tuple layout for every lookup it
emits. Repeated uses of one relation ID in a lookup challenge domain must have
exactly the same schema. The circuit and bridge use the six-coordinate Gate
schema; pair/many chips and bridges use the seven-coordinate tagged-step
schema. These are the only relations admitted by this mixed registry today.

This check closes a specific future composition trap. The existing SHA-word-v1
bus uses relation ID `0x53333103` for its six-coordinate tuple
`(id, call, address, lo, hi, 0)`. The existing pair/many bus uses the **same**
ID for its seven-coordinate tuple `(id, call, step, s0, s1, s2, s3)`. Padding
the SHA tuple to seven coordinates can make the two encodings identical.
The focused registry test admits the SHA-word-v1 schema and rejects every
pair/many chip or bridge constructor in that same domain; it also checks the
reverse order. A future SHA + mixed profile must call this guard before proof
decoding and allocate a distinct versioned relation ID and proof profile.

The guard does not change existing relation IDs, AIR equations, manifest
digests, transcript tags, or proof bytes. Its layout declarations are a
reviewed registry contract, not automatically extracted from AIR evaluator
code. A new component must supply a checked schema and evidence that its AIR
emits that encoding. This guard establishes relation-schema compatibility at
admission; it does not establish LogUp, AIR, PCS, or Fiat–Shamir soundness.
