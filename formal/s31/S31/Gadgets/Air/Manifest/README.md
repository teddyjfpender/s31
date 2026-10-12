# Interleaved mixed manifest correspondence

`InterleavedRoster.lean` formalizes the checked roster projection used by the
generated direct mixed manifest. For `N` source calls, the native policy is:

| Position | Role | Call | Constructor ID | Claimed sum index |
| --- | --- | --- | --- | --- |
| `0` | circuit | none | `0` | `0` |
| `1 + 2i` | chip | `i` | `1` if `i < 2`, else `3` | `1 + 2i` |
| `2 + 2i` | bridge | `i` | `2` if `i < 2`, else `4` | `2 + 2i` |

For example, three calls give `circuit, chip 0, bridge 0, chip 1,
bridge 1, chip 2, bridge 2`. The final two use the many constructors.
The native manifest stores exactly `1 + 2N` entries for admitted `1 ≤ N ≤ 8`.

## What is proved

The Lean model imports `SourceMixedRoster.sourceSlot`, which models
`registry.zig::forSlot`. It proves both transcript indices equal the roster
position, the constructor IDs above, and injectivity of the logical
`(role, call ID)` key. `CheckedProjection` decomposes the native manifest's
field comparisons into role, key, call ID, proof index, claimed sum index,
and relation IDs. Given those checks, the entire entry sequence equals the
canonical roster; every source call has exactly one chip and one bridge in
the prescribed positions. Projecting an entry's call ID through the copied
source call array returns the full modeled source call identity, including
source node ID, input node ID, rounds, and constant.

The native `registry_manifest.zig` test exercises source reconstruction and
live geometry for all eight call counts, and rejects altered indices,
swapped entries, relations, source fields, AIR identifiers, and geometry.
That is a native test of the implementation; the Lean theorem is a proof of
the corresponding mathematical policy. No native versus Lean parser
differential fixture is claimed here.

## Remaining refinement assumptions

This module takes the following facts from native source inspection as
premises; it does **not** prove the Zig implementation realizes them:

1. The parser and optimizer identify the canonical source calls, in order,
   with call IDs equal to positions, and copy their metadata into the
   selected schedule and generated manifest.
2. Native `inspection.zig` constructs exactly `1 + 2N` live slots, checks the
   registered AIR facts, and interleaves chips and bridges as modeled.
3. `registry_manifest.zig::fromSchedule` performs the field comparisons in
   `CheckedProjection` against those source-derived slots. Its additional
   live geometry, relation schema, digest, and source-binding checks are
   outside this Lean module.
4. Proof admission reconstructs this manifest from verifier-owned source.
   This module makes no PCS, FRI, Fiat–Shamir, witness confidentiality, or
   native parser correctness claim.

Focused checks:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake build S31.Gadgets.Air.Manifest.InterleavedRoster
LEAN_NUM_THREADS=1 lake env leanchecker -v S31.Gadgets.Air.Manifest.InterleavedRoster
```
