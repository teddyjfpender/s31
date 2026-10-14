# P06: complete-tree multiproof collision reduction

The [Lean join](../../../formal/s31/S31/Gadgets/PcsFri/MultiproofByteCollisionReduction.lean)
connects three previously separate mathematical steps:

1. A successful raw-query decoder yields a full Merkle opening for **each
   caller slot**, including duplicate queries.
2. A complete tree built from projected columns yields an opening of its
   committed row at the same index and root.
3. If those two rows differ, the exact plain leaf or parent encoding exposes
   **distinct byte messages with the same digest**.

This works for arbitrary modeled tree height, column count, and query count.
It does not assume that a finite-output hash is globally injective. The
constructed tree's path digests are proved to have 32 bytes and valid byte
values. The proof-supplied captured path must have that shape, and both rows
must contain canonical M31 representatives. These are explicit premises
because the Lean decoder uses generic lists; the selected native hash type is
`[32]u8` and the exact Zig-to-Lean decoder bridge remains open.

For a hand example, take a height-zero tree with committed row `[1]`, one
query claiming `[2]`, and a toy hash that always returns 32 zero bytes. The
modeled decoder accepts the wrong row because both leaf messages hash to the
same root. Lean checks this example. The theorem exposes the concrete leaf
collision between little-endian bytes `01 00 00 00` and `02 00 00 00`; it
does not incorrectly conclude that the accepted row must be `[1]`.

The result removes the **abstract** `noCollision` premise from one-slot
origin reasoning by turning its failure into an explicit collision witness.
It does not yet prove that the installed Zig verifier runs the Lean decoder,
that an arbitrary installed prover root is the modeled complete-tree root,
or a numerical BLAKE2s collision probability under an adaptive hash budget.
P06 and release admission therefore stay open.

Focused check:

```sh
(cd formal/s31 && lake build S31.Gadgets.PcsFri.MultiproofByteCollisionReduction)
```
