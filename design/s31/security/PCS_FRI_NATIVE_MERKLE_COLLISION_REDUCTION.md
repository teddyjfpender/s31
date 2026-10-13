# Native Merkle collision reduction for one fixed tree shape

The lifted PCS capture admission rehashes every opened row and full path
against the proof's four roots. The audit utility in this slice additionally
checks that repeated query positions carry **identical rows and path bytes**.
The native compressed decoder is supposed to copy one deduplicated path back
to every occurrence. This audit is used in tests and is not installed in the
production verifier.

For two accepted openings at the **same root, height and leaf index**, the
[`pcs_merkle_collision_reduction.zig`](../../../formal/s31/tests/lib/pcs_merkle_collision_reduction.zig)
function `Reduction(H).extract` takes their canonical M31 rows and full paths.
It checks both shapes and recomputes both roots. If the rows differ, it
returns one of two independently checkable certificates:

1. `leaf`: distinct equal-length canonical M31 rows with the same leaf digest.
   Their native leaf byte strings are distinct because each canonical word
   has a unique four-byte little-endian encoding.
2. `parent`: distinct ordered `(left, right)` hash pairs with the same parent
   digest, together with the first level where the outputs meet.

The verifier's leaf operation is BLAKE2s over concatenated canonical M31
little-endian words; its parent operation is BLAKE2s over `left[32] ||
right[32]`. The selected S31 profile uses the **plain** hasher, so no leaf or
node prefix is inserted. The certificate's `check` method rehashes both
preimages and requires them to differ. The reduction is constructive and
works for any representable depth below the machine word width; it does not
enumerate a fixed eight-leaf tree.

For a hand example, let an intentionally weak toy hash return each M31 word
modulo 256 at a leaf and XOR its two child bytes at a parent. At leaf index 0
and height 1, rows `[1]` and `[2]` with sibling bytes `5` and `6` both reach
root `4`:

```text
opening A: leaf 1, children (1, 5), parent 1 XOR 5 = 4
opening B: leaf 2, children (2, 6), parent 2 XOR 6 = 4
certificate: (1, 5) != (2, 6), but both parent digests are 4
```

The native test also makes a leaf collision using rows `[1]` and `[257]`
under that toy hash, checks that changing either certificate invalidates it,
exercises a collision first appearing at the second parent level with an odd
leaf index, and rejects out-of-domain indices, short paths, noncanonical rows, wrong
roots, and same-row inputs. Its separate duplicate-query audit accepts native
copied paths, then rejects changed duplicate rows or paths, out-of-domain
aliases, and malformed lengths. With the selected BLAKE2s hasher, a
conflicting row without a collision fails root authentication. Run:

```sh
formal/s31/tests/run_pcs_fri_native_collision_reduction.sh
```

This is the executable counterpart to
[`MerkleOpening.conflicting_openings_produce_collision`](../../../formal/s31/S31/Gadgets/PcsFri/MerkleOpening.lean).
It does **not** prove the Zig decoder implements the Lean model, that the
committed tree originated from the intended columns, or that BLAKE2s has any
particular collision probability. Its guarantee is conditional on two
accepted openings with exactly the same tree shape. Plain BLAKE2s has no
leaf/node domain separation, so cross-height or cross-type collisions need
their own protocol argument. P06 remains open and release admission remains
closed.
