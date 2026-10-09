# Circuit AIR row models

`Qm31Ops.lean` models the nine local polynomial residuals emitted by the
production circuit AIR's `evaluateQm31Ops`. A row is accepted exactly when its
four flags encode one opcode and its output is that opcode's result for the
two packed QM31 operands. The theorem covers arbitrary field-valued flags and
output limbs, so malformed flag values and incorrect outputs are rejected.

`row_iff_normalized_node` composes the row theorem with S31's executable
normalized `add` and `mul` nodes for a full four-lane chunk. It uses the proved
M31-to-ZMod field map, so it relates the AIR's packed field values to native
M31 arithmetic. `honest_row`, `output_unique`, `all_flags_zero_rejected`, and
`two_flags_rejected` provide concrete non-vacuity and malformed-row controls.

`SimdChunks.partial_row_iff` covers the short final chunk of an array. For
any `n ≤ 4`, arbitrary M31 values may fill the unused input lanes. An accepted
full row with claimed active output lanes exists exactly when every active
claim is the native `add` or `mul` result. The proof includes `n = 0`; it does
not assume that unused trace limbs are zero.

`partial_row_iff_normalized_node` composes this with the executable normalized
relation evaluator, including its output length, for every `n ≤ 4`.

`FunctionalBridge.array_graph_iff_air_row` composes four modeled boundaries
for a typed pointwise expression: functional source meaning, strict scalar
graph constraints, the executable normalized node, and the packed AIR row for
the **final operation**.
For `x + x` with `x = [3, 5]`, the scalar graph has two addition gates. The
packed row has `add = 1`, active operands `[3, 5]` and `[3, 5]`, and active
output `[6, 10]`. Its two unused lanes may start with arbitrary M31 values;
the row equation constrains their output limbs, and the S31 array result
still has length two. The theorem covers any typed source operands in this
total array core and both pointwise operations, not just this example. It
does not model the AIR rows needed to compute nontrivial operand expressions.

S31 array addition uses the `add` opcode. S31 pointwise array multiplication
uses `pointwiseMul`; `mul` denotes multiplication in the QM31 extension field.

The preprocessed gate addresses and multiplicities, the Gate lookup relation,
trace-wide consistency, and the STARK verifier are outside this local row
theorem. See the [formal proof scope](../../../README.md) for the remaining
compiler and proof-system obligations.

`GateLookup.lean` adds an **ideal exact-multiset** model of the Gate relation.
Each arithmetic row uses `(address, packed value)` for its two inputs and
yields its output tuple with the preprocessed multiplicity. Other circuit
components and public claims contribute external events. Given exact balance
and a unique produced value per address, `addressed_row_sound` proves that
the row operands must equal the values produced at those addresses, then uses
the nine AIR equations to determine the output. `forged_input_rejected`
proves a differing input trace cannot balance the relation. For example, a
row that locally checks `4 + 3 = 7` cannot claim its first operand came from
address 7 when address 7 produced 5.

The kernel-checked `honest_example_local` and `honest_example_balanced` show a
nonempty row with sources `(7,5)` and `(8,3)`, result `(9,8)`, and a public use
of `(9,8)`. `forged_example_local` instead computes `4 + 3 = 7`, with a public
use of `(9,7)`; `forged_example_rejected` proves exact Gate balance fails
because address 7 still produced 5. The output claim was changed to 7 too, so
the rejection isolates the forged input-address binding.

`unique_produced_of_nodup_outputs` derives the row-side uniqueness premise
when output addresses are distinct, external producer events are consistent,
and row outputs have addresses disjoint from those external events.
`indexed_outputs_nodup` proves the abstract straight-line address layout
`start + gate_index` has distinct outputs. A correspondence proof for the
actual Zig allocator and any aliasing or `*Into` call sites remains open.

Exact multiset balance is a **premise** here. Production uses compressed
LogUp over a random challenge; this module does not bound collision
probability, prove trace-to-interaction correctness, or prove the compiler
assigns one producer per address. Addresses and multiplicities are modeled
as natural numbers after their canonical M31 encoding checks.
