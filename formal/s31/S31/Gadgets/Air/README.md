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

`packedRows_iff` covers arrays of **any** length. It creates exactly
`ceil(n/4)` rows, maps source lane `j` to row `j/4` and limb `j%4`, and proves
that every active claimed lane equals source arithmetic if and only if all
row witnesses exist. It permits arbitrary inactive values in the final row.
For a five-lane addition, take `a = [3,5,7,11,13]` and
`b = [2,4,6,8,10]`. Row 0 constrains outputs `[5,9,13,19]`. Row 1
constrains its first output limb to `23`; its remaining three input limbs
may contain arbitrary M31 values. Their output limbs must satisfy the row
equation, but they cannot change the fifth source result.

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
`array_graph_iff_packed_rows` extends that composition to any array length
and all rows of its final pointwise arithmetic operation. It retains the
same operand-subexpression boundary.

`SelectRows.lean` models the compiler's array choice as one shared `1 - bit`
row, then two scalar products and an addition per packed word. It first proves
the four local equations in `acceptsSelect_iff`; arbitrary intermediate row
witnesses cannot change the selected word when the selector is Boolean.
`packedSelectRowsShared_iff` proves that sharing the complement preserves the
accepted claims. `packedSelectRowsShared_iff_evaluateNode` covers every packed
word, including short final words, and matches the executable normalized
`select` node. `source_array_if_iff_shared_rows` composes that exact row
topology with the typed source conditional and its strict graph relation.

The selector's Boolean constraint must come from its producer or an explicit
check. The concrete `nonbit_interpolation_rows` control shows why: selector
`2`, false arm `3`, and true arm `5` satisfy all four arithmetic row equations
with output `7`. That output is neither branch. The source-to-row theorems
include the Boolean premise; they do not assume it follows from arithmetic.
`QuadField.lean` constructs QM31 as two quadratic extensions of M31. Lean
proves that `-1` and `5` are nonsquares in M31 and uses the second extension's
norm, `5`, to establish both field instances. A four-coordinate bridge
matches the AIR multiplication formula to this field.
In symbols, a witness is `q = (a + bi) + (c + di)u`, with `i² = -1` and
`u² = 2 + i`. Since M31's prime is `3 mod 4`, `-1` has no square root there.
The norm of `2 + i` is `2² + 1² = 5`; quadratic reciprocity shows `5` has no
square root in M31 either. Both extensions are therefore fields, so
`q² = q` implies `q(q - 1) = 0`, hence `q = 0` or `q = 1`.
`untrusted_selector_self_product_iff` proves that **any** QM31 wire satisfying
the self-product row is exactly canonical zero or one. This proof does not use
the compiler's `QM31.fromBase` witness hint.
`untrusted_self_product_select_iff_evaluateNode` combines an arbitrary
selector witness, its bound base coordinate, the self-product row, and every
shared selection row to recover the normalized `select` result. Binding
actual circuit addresses to these modeled rows remains a separate Gate
lookup obligation.

`BooleanRows.lean` gives the exact ordinary QM31 row schedules for `not`,
`and`, `or`, `xor`, and Boolean `select`. The OR proof covers a sum, product,
and subtraction; XOR also includes multiplication of the product by two.
`not_iff`, `and_iff`, `or_iff`, `xor_iff`, and `select_iff` show that arbitrary
intermediate witnesses give the expected Boolean result and that honest row
witnesses exist. The premises are base-field encoded Boolean operands, as
provided by a proved bit producer. `QuadField.self_product_iff` also handles
arbitrary untrusted QM31 self-product operands.

`BitRows.lean` proves the other Boolean input path. Its `acceptsZero` is the
compiler's `anchor + value = anchor` self-loop assertion with an arbitrary
anchor witness. `acceptsZero_iff` shows that row accepts precisely the zero
QM31 value. `acceptsBit` then models the ordinary scalar check as multiply,
subtract, and zero assertion rows. `acceptsBit_iff` proves that any satisfying
four-coordinate wire is canonical zero or one, while constructing honest
rows for both bits. `acceptsBit_bound_iff` connects a bound source M31 value;
`nonbit_two_rejected` checks a concrete forged scalar is excluded.

`ZeroRows.lean` models every arithmetic row in `isZeroWord`: multiply by an
inverse witness, subtract the indicator from one, assert the difference is
zero with an anchor self-loop, and assert `input * indicator = 0` with another
anchor self-loop. The field-tower bridge makes the proof apply to arbitrary
QM31 witness values. `acceptsZeroTest_iff` proves that all satisfying rows
force the indicator to one exactly for a zero input, and that an honest
inverse and indicator can always satisfy the rows. A base-field restriction
is proved equivalent to the executable normalized `is_zero` node.
`zero_input_forged_indicator_rejected` rules out the wrong claim for zero;
`seven_input_honest_indicator` supplies a nonzero control. This is a local
row theorem; actual witness generation and address joins are separate.

For `x = 7`, take `z = 0` and inverse `7⁻¹` in QM31. The first product is
`7 · 7⁻¹ = 1`, while `1 - z = 1`, so their difference is zero. The second
product is `7 · z = 0`. Both anchor rows accept. For `x = 0`, take `z = 1`:
both products and `1 - z` are zero, and the inverse witness can be anything.
Trying `x = 0, z = 0` makes the first equation read `0 = 1`, so no witness
can satisfy it.

`InverseRows.lean` models `inverseLanes` for every packed word: one
pointwise product row, subtraction of the active-lane mask, and the same
anchor zero assertion. `acceptsInverse_iff` proves the row schedule imposes
the exact four-coordinate mask equation. Every active lane must be nonzero
and its inverse coordinate is uniquely fixed. `packedInverseRows_iff`
extends this to arrays of any length and arbitrary final-word input padding:
the rows exist exactly when every source lane is nonzero and every claimed
lane equals its M31 inverse. A zero active lane is rejected by an explicit
control theorem. Output wire and Gate address joins remain global obligations.

For a two-lane inverse of packed input `(2, 3, 71, 99)`, the active mask is
`(1, 1, 0, 0)`. Since `p = 2147483647`, an honest inverse word is
`(1073741824, 1431655765, 0, 0)`: multiplying its first two coordinates
by `2` and `3` gives `1 mod p` in each case. The pointwise product is
`(1, 1, 0, 0)`; subtracting the mask gives zero for the anchor assertion.
The values `71` and `99` are arbitrary inactive padding. If lane two were
active with input zero, its required product would be `0 · y = 1`, which is
impossible.
The Zig witness builder now writes zero inverse hints in the inactive lanes
of a short final word. A regression feeds it nonzero padding, checks the
inverse values and unchanged row count, and compares value-carrying and
witness-free circuit topology.

`UnpackRows.lean` models the `unpackIdx` path when an operation needs one
scalar from a packed word. The circuit first multiplies pointwise by a unit
vector. For coordinate zero, that masked wire is already the answer; for
coordinates one through three, one QM31 multiply by the unit vector's
inverse moves the chosen lane into the base coordinate. The row theorem
proves the output is exactly `(chosen value, 0, 0, 0)` for any packed input.
For example, extracting coordinate two from `(8, 13, 21, 34)` starts with
`(0, 0, 21, 0)` and finishes at `(21, 0, 0, 0)`. The array theorem covers any
active index and arbitrary final-word padding. Gate address joins remain a
separate obligation.

`SumRows.lean` models `sum_lanes`: the optional final-word pointwise mask,
left-to-right pairwise add rows with odd-width carry rounds, QM31 multiplication
by the dual projection constant, and a final pointwise base-coordinate mask.
`projection_literal_rows_iff` uses the exact four-coordinate constant emitted
by Zig and proves it equals the algebraic dual projection word.
For `[3,5,7,11,13]`, the first packed word contributes `26`; the second
contributes `13` even if its three unused input coordinates contain arbitrary
values. One accepted add row combines them, and the projection rows bind the
single M31 result to `39`. `compiledSumLanesRows_iff_evaluateNode` proves that
all accepted row witnesses give exactly the normalized `sum_lanes` value for
every nonempty array; it models Zig's one-lane alias as a separate case.

`MixRows.lean` composes the four-lane `sumLanes` reduction with multiplication
by the literal broadcast word `(1, 1, 1, 1)` and one packed addition row.
`mix4Rows_iff_applyStep` proves these rows give exactly the executable
`mix4` step used by repeat bodies, for every M31 input and arbitrary
intermediate row witnesses. For input `(1, 2, 3, 4)`, the sum wire is `10`,
the broadcast word is `(10, 10, 10, 10)`, and the output is
`(11, 12, 13, 14)` modulo M31. This local proof does not establish the
address joins from the sum output to the broadcast input.

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
