# Array examples

`array_views*.s31` and `array_slice_*.s31` show fixed-length field and u16
views. `static_matvec.s31` and `static_matmul.s31` compose source arrays into
field arithmetic. The adjacent `.s31.json` files are equivalent normalized
relations for the older direct-IR examples; `.valid.json` files contain
complete public/private assignments.

`array_matrix_runtime.s31` erases its complete ordered `reshape<2>` and
`flatten` to the original private array before selecting lane 6. Its matching
`.s31.json` contains only the selection. The
[`expanded_matrix_runtime` fixture](expanded_matrix_runtime/README.md)
keeps the explicit slice/concat relation so the Zig circuit test continues
to check explicit aligned views. For a shifted view whose erasure saves gates,
see [the six-lane comparison](../functional/reshape_flatten_zero_cost/README.md).

[`functional_rotate_hash.s31`](functional_rotate_hash.s31) passes a four-lane
array through a captured hash closure. It takes the last two lanes, appends
the first two, adds a captured field salt, and hashes the result with
Poseidon2. Its [direct form](functional_rotate_hash_manual.s31) must produce
identical normalized IR and AIR cost. The
[fixture](functional_rotate_hash.valid.json) uses `[0,1,2,3]`, so the hash
input is `[9,10,7,8]`. The functional acceptance gate checks that arithmetic
against an independent Poseidon2 oracle, builds both native packages, proves
the fixture and rejects a changed public digest.

Lean's [array core](../../../../../formal/s31/S31/Gadgets/Functional/Arrays.lean)
proves source-level specialization and strict graph soundness for fixed-length
field-array arithmetic and views, including the exact `[9,10,7,8]` prehash
transform. The hash and array-view compiler paths are exercised by the native
acceptance gate; their production AIR correspondence is not a Lean theorem yet.
