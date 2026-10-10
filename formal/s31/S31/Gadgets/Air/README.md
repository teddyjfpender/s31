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
The Zig regression checks all four coordinates, including the one-row
coordinate-zero path and the two-row paths for the other coordinates.

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

`EqRows.lean` models the equality component, which has no independent
arithmetic polynomial: its two Gate lookups use the same committed trace
value. Under exact Gate balance and one produced value per address, the two
addressed inputs must agree. For a short final packed word, S31 emits
`difference = left - right`, then `masked = difference .* activeMask`, then
an equality lookup between `masked` and zero. The row theorem proves this
accepts precisely when active coordinates match. For example, with two
active lanes, `(2, 3, 71, 99)` equals `(2, 3, 5, 6)` because the masked
difference is `(0, 0, 0, 0)`. Changing the second active value to `4` gives
masked difference `(0, p-1, 0, 0)`, so lookup closure rejects it.
Separate nonempty Eq-event controls accept two addresses that both produce
`5` and reject a trace that reads `5` from an address producing `6`.
`packedEqRows_iff` repeats the joined full-word or short-word relation over
any number of packed words and proves it equivalent to equality of every
active source lane, regardless of unused padding.
A Zig regression confirms the short-word compiler path uses two arithmetic
rows and one Eq row, accepts differing inactive padding, and rejects a
changed active lane.

`GateChallenge.lean` proves the six-element Gate tuple compressor used by
`combineTerm`. For tuple `t`, it evaluates
`H_t(α) = t₀ + t₁α + t₂α² + t₃α³ + t₄α⁴ + t₅α⁵`, then subtracts `z` to
form the lookup denominator. Coefficient extraction proves different tuples
give different polynomials. A nonzero degree-at-most-five difference can
vanish at no more than five choices of `α`. The proof maps canonical Gate
events to the actual tuple order: relation id `378353459`, address, then
four M31 limbs embedded in QM31. It also proves the challenge field has
`2147483647⁴` elements, giving at most `5 / 2147483647⁴` of uniform `α`
choices for a collision between two distinct canonical events. For example,
events `(7, (5,0,0,0))` and `(7, (4,0,0,0))` differ by `α²`, so only
`α = 0` collides. For fixed `α` and tuple, exactly one `z` makes its
denominator zero.

`LogUpNumerator.lean` formalizes the next lookup equation after tuple
compression. Let the distinct compressed values be `a₁,…,aₛ` and let
`w(a)` be uses minus yields, counted in QM31. For a verifier challenge `z`
outside this set, the checked sum is

```text
R(z) = Σₐ w(a)/(z-a).
```

Multiplying by `D(z) = ∏ₐ(z-a)` gives a polynomial

```text
N(z) = Σₐ w(a) ∏_{b≠a}(z-b).
```

At `z=a`, every term but one vanishes and
`N(a)=w(a)∏_{b≠a}(a-b)`. Distinctness makes the product nonzero, so any
nonzero weight makes `N` a nonzero polynomial of degree at most `s-1`.
Consequently, an unbalanced fixed lookup can pass `R(z)=0` at no more
than `s-1` eligible challenges. The Lean theorems prove each equality,
the degree bound, and the root count without an assumed polynomial identity.

`LogUpCount.lean` relates those weights to actual event lists. If the two
lists are unequal as multisets and each has fewer than `p=2147483647`
elements, some count differs after conversion to QM31. It proves
`Σₐ w(a)/(z-a)` equals the difference between summing the two lists of
reciprocals, including repeated events. The explicit length bound prevents
field-characteristic wraparound: `p` copies of one tuple contribute weight
zero. `characteristic_wrap_example` is a kernel-checked symbolic control
for that failure mode; it never materializes a billion-element list.
The sharper `unequal_lists_have_nonzero_weight_of_counts` only requires
each distinct compressed event's count to be below `p`. Many different
events can make the total trace longer than `p` without this wraparound.

`GateLogUpBridge.lean` composes these results for the actual Gate tuple
layout. Given fixed event lists, it enumerates distinct event pairs and
maps each to its two six-element tuples. Canonical addresses make the tuple
map injective. At most `5s²` choices of `alpha` collide one of the pairs,
where `s` counts distinct events across both lists. For every other
`alpha`, an unequal pair of event multisets stays unequal after
compression. If each original list length is below `p`, the weighted
reciprocal polynomial then bounds the bad `z` choices by `t-1`, where `t`
counts distinct compressed values. Another `t` choices are excluded because
they zero a denominator. `fixed_gate_multiset_sound` packages these
cardinality bounds and proves that all other challenges distinguish the
two sums using Zig's sign convention `1/(H(tuple)-z)`.
`GateLocalCounts.lean` transfers each original event count through
collision-free compression, so
`fixed_gate_multiset_sound_of_counts` needs no total-length bound. It keeps
the same `5s²` and `t+(t-1)` exceptional-set bounds.
`GateChallengePairs.lean` forms the combined bad set in `QM31²`. If the
two fixed canonical lists differ and every event count is below `p`, the
bad set has at most `(5s²+2s)·p⁴` pairs out of `p⁸`, where `s` is the
number of distinct events. `uniform_pair_failure_rate_le` proves the
corresponding rate bound `(5s²+2s)/p⁴` for independent uniform field
challenges. `reciprocal_closure_implies_bad_pair` proves any accidental
closure lies in the named set. The transcript and commitment system still
need their own soundness argument.
`GateChallengeClosure.lean` filters the full challenge-pair space by the
actual modeled row-plus-external reciprocal equation. Every closing pair
is in `badPairs`. If the fixed use and yield event lists differ, canonical
addresses and per-event count bounds give the same `(5s²+2s)·p⁴` upper
bound directly for row-equation closure. This is conditional on a fixed
pre-challenge witness and does not identify the native committed columns
with these modeled rows.
`GateAddressCounts.lean` further proves that an individual event cannot
occur more often than its address occurs in the integer histogram.
Consequently, per-address histogram bounds below `p` suffice for the
per-event premise. This is the closest formal condition to the native
preprocessed builder's checked use counters; the builder now rejects a
counter increment that would reach `p` rather than allowing field wrap.

This is a theorem about **fixed lists and field challenges**, not the
production STARK. The remaining obligations are to connect committed Gate
columns and the interaction AIR to those lists and sums, prove their
compiler-side address and event-count premises, and justify the transcript's
challenge distribution after commitments.

`LogUpInteraction.lean` separately models the interaction AIR. For one
lookup term with numerator `n` and denominator `d`, its residual is
`Δ·d-n`. For a pair `(n₀,d₀),(n₁,d₁)`, the residual is
`Δ·d₀·d₁-(n₁·d₀+n₀·d₁)`. If the denominators are nonzero, zero residual
means `Δ=n/d` or `Δ=n₀/d₀+n₁/d₁` respectively. The theorem covers both
the odd final singleton and paired terms in `finalizeLogupInPairs`.

Within a row, every non-final secure column adds its term pair to the
preceding column. The final column also subtracts its previous-row value
and adds `claimed_sum / n_rows`. Summing this final equation over all
rows cancels the running column against its predecessor permutation;
the shift adds back `claimed_sum`. The checked theorem concludes that
the claimed sum is exactly the total of the row fractions. It proves
`n_rows=2^log_size` remains nonzero in QM31. A concrete control proves
the pair residual vanishes for **any** `Δ` when both denominators are
zero, even with numerators one. Thus the bad-`z` exclusion above is
necessary.

This interaction theorem is a mathematical model of Zig's formulas and
column schedule. Its premises still need a machine-checked correspondence
to the committed columns, the circle-domain predecessor relation, and
the actual verifier's AIR evaluation on those columns.

`Qm31GateInteraction.lean` instantiates the interaction proof for the
actual `qm31_ops` lookup order. Every row has three Gate terms: input 0,
input 1, then `-multiplicity` times its output. The input pair's secure
column is checked by the paired residual; the final secure column is
checked by the singleton residual with the previous-row subtraction and
claimed-sum shift. Assuming these residuals vanish and their denominators
are nonzero, `qm31_ops_claimed_sum` proves that the component claim equals
the sum of `rowContribution` over all `2^log_size` rows. This is a local
semantic theorem for the exact column schedule, including padding rows;
it still relies on a source-to-AIR correspondence for the real Zig
evaluator and committed trace.

`qm31_ops_closed_gate_balanced` combines this component-level result with
the modeled external Gate terms and a closed verifier claim to derive exact
multiset balance. The other components' claimed sums must still be shown to
match those external terms in the production verifier.

`EqGateInteraction.lean` models `assert_eq`'s two Gate uses as one paired
term per row. The paired residual and cyclic last-column shift force the
Eq component's claim to equal the sum of those two read reciprocals across
all rows. `qm31_and_eq_closed_gate_balanced` adds this checked claim to the
checked `qm31_ops` claim, keeps other Gate users as explicit event lists,
and derives exact shared Gate balance. Under a unique producer per address,
`eq_row_sound_of_shared_gate` turns that balance into equality of the
values produced at the row's two input addresses. The Eq component has no
local arithmetic equation that could enforce this by itself.

As a one-row hand calculation, suppose the two input denominators are `2`
and `3`, the output denominator is `5`, and its multiplicity is `1`.
The first secure column must hold `1/2+1/3=5/6`. The final singleton is
`-1/5`, so the row contributes `5/6-1/5=19/30`. With one row, the final
column's previous-row value is itself and the shift is the claimed sum.
Its AIR equation reads `0 - 5/6 + claimed = -1/5`, which forces
`claimed=19/30` in QM31. These fractions mean field inverses; the
calculation is valid because `2`, `3`, and `5` are nonzero modulo `p`.

For an Eq row, suppose the two address lookup denominators are `2` and
`3`. Its only secure column has `current - previous + claimed`, because
the row count is one. The previous value equals the current value, so
the paired equation forces `claimed = 1/2 + 1/3 = 5/6`. This only accounts
for the row's two reads. The shared Gate closure must match both reads to
their producer events; when each address has one produced value, the Eq
row's common trace word forces those two produced values to be equal.

`GateContributions.lean` relates the ideal `GateLookup.Row` event lists to
the production sign and multiplicity convention. A row reading two wires
and yielding one result `m` times contributes

```text
1/H(input₀) + 1/H(input₁) - m/H(output).
```

The proof converts the list of `m` repeated output events into the single
field numerator `-m`, then sums row and external contributions over an
arbitrary trace. Under exact closure of this sum, canonical addresses,
both event-list lengths below `p`, and challenges outside the bounded bad
sets, `closed_gate_contribution_balanced` recovers the exact multiset
premise used by `GateLookup.addressed_row_sound`. The compiler's event
emission and the actual interaction AIR still need correspondence proofs
to supply that closure premise.

`closed_gate_contribution_balanced_of_counts` replaces the total-length
condition with an upper bound on each individual event count.
`closed_gate_contribution_balanced_of_address_counts` consumes integer
address-histogram bounds directly.

`GateCounter.lean` proves a checked-count implementation of those bounds.
Its `checkedIncrement(current, increment)` has Zig's `increment < p` and
`current < p - increment` guards. A successful fold over address/increment
pairs computes each address's exact integer total and keeps it below `p`.
For a list of Gate events, mapping each event to one increment produces
the `addressCount` histogram. The theorem then feeds these proved counts
to the fixed-list LogUp soundness result. This models the arithmetic of
Zig's counter; matching its actual component traversal to the event list
remains a compiler/source correspondence task.

`GateCounterCircuit.lean` connects the compact output count to the
repeated events of `GateLookup.Row.yields`. For an output at address `9`
used three times, the modeled counter takes one step `(9,3)`, while the ideal
multiset contains three `(9,output)` events; both have address count `3`
at address `9` and `0` elsewhere. `compressed_yields_match_events` proves
this for arbitrary row lists and external yields. The
`closed_gate_of_checked_counters` theorem uses successful modeled checked
input and compact output counts to discharge the bounds in whole-Gate
closure. Native permutation scratch counts remain a separate obligation.

`GateProducerCheck.lean` models the declared-variable producer scan: it
rejects outputs outside `n_vars` and repeated declared addresses.
`scan_sound` proves a successful scan has no repeated addresses. The
permutation lowering intentionally reuses a scratch address for multiple
rows, so the theorem partitions declared yields from scratch yields.
`addressed_declared_row_sound` proves ordinary rows whose input addresses
are below `n_vars` still read their sole producer values when scratch
addresses are at or above `n_vars`. The actual output partition remains
a source-to-model correspondence obligation.

`GateUseTraversal.lean` models the preprocessed builder's special use
increments. If there are four permutation input/output rows, Zig adds `4`
to the zero-wire counter once; the ideal Gate list has four `(0, zero)`
reads. Each private SHA boundary address contributes one further use.
`compressed_uses_match_events` proves the compressed increments and
expanded reads have the same address histogram for arbitrary ordinary
uses, row counts, and boundary lists. A successful modeled checked walk
then bounds that histogram below `p` at every address.
`closed_gate_of_compressed_counters` plugs both modeled compact walks into
the Gate closure theorem. Zig's declared-variable counter does not walk
permutation scratch reads, so the native scratch count and event-list
correspondence remain separate obligations.

`PermutationScratch.lean` handles the intentionally shared scratch
address. One permutation pair emits two arithmetic rows and contributes
one scratch read and one scratch yield. Thus a checked increment by the
total permutation row count bounds each scratch list's length, and every
scratch address count is at most that length. `full_bounds_with_permutation_scratch`
combines those bounds with declared-variable counts using the disjoint
address ranges. It requires the stated row/event lengths and range
partition; proving them for the native emitted trace remains open.
`closed_gate_of_partitioned_scratch` carries the two bounded histograms
through the fixed-list LogUp theorem. It accepts permutations of the
declared/scratch event partitions, matching lookup's multiset meaning.

For two permutation pairs, let the input values be `[5, 7]` and the
output values be `[7, 5]`. The first two rows yield `(scratch, 5)` and
`(scratch, 7)` at the same scratch address. The next two rows read
`(scratch, 7)` and `(scratch, 5)`. Gate checks the two multisets, so the
order may change. The zero-wire increment is `4` for these four rows;
each scratch read/yield list has length `2`, below that checked count.
Requiring one value per scratch address would incorrectly reject this
valid permutation.

`PermutationRows.lean` proves the exact local two-row schedule. The first
zero-add row copies each input value to the shared scratch address; the
second copies each scratch read to its output. The global Gate multiset
is filtered by the chosen scratch address to recover that gate's
scratch-only balance, even when other permutation gates are present.
`permutation_sound_of_global_gate` concludes that output values permute
input values. The converse constructs honest row witnesses for every
permutation. Kernel-checked two-word controls accept the swap above and
reject replacing `7` with `8`.

`GateFinal.lean` composes that conditional multiset theorem with the
arithmetic row theorem. If each addressed input has a unique producer, a
locally accepted row can only output the operation applied to those
producer values. `addressed_row_sound_of_closed_gate_counts` handles
relations with more than `p` total events under per-event count bounds.
Two concrete controls make the statement testable: the honest row reading
`5` and `3` from addresses 7 and 8, producing `8` at
address 9, has a zero Gate contribution for every `alpha,z` in field
arithmetic; the forged row reading `4` from address 7 cannot close outside
the explicit bad-challenge sets even though its local equation `4+3=7`
is valid.

The fixed-list algebraic theorems establish a bounded-error reduction from
closed Gate reciprocals to exact multiset balance. The address-join theorem
still needs unique producers, and the reduction still needs correspondence
between Zig's committed columns, emitted Gate events, verifier equations,
and the Lean model. The transcript's challenge distribution and the STARK
verifier's cryptographic soundness are separate obligations.
