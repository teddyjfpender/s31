# S31 normalized semantics and local constraint proofs

This package gives executable Lean semantics for **all 43 operations in S31
relation IR v1** and proves the local constraint models sound and complete.
It reuses `RiscvRefinement.Field.M31` and the existing
`RiscvRefinement.Recursion.CompactPoseidon` S-box proofs through a local Lake
dependency. The [contract](../../design/s31/language/FORMAL_SEMANTICS.md) fixes
the boundary and evidence requirements.

The normalized typed relation is the language boundary. The model covers
metadata validation, shapes, canonical input values, public/private
assignments, arithmetic failures, assertions and claimed public outputs.
Public input words precede output words and the statement is zero-padded to
eight words. Fixed widths and order are part of the source-bound statement;
padding alone cannot distinguish a trailing zero from a changed width.
Transparent and blinded proof modes have identical value semantics. That
theorem does not establish zero knowledge.

## Organization and reuse

| Location | Responsibility |
| --- | --- |
| `S31/Semantics/Types`, `Validation`, `Node`, `Program`, `Json` | Typed IR, complete operation dispatch, validation, assignment and public ABI. `Json` is an executable adapter, not a parser-correctness proof. |
| `S31/Semantics/Words`, `Integers`, `Bitcoin` | Little-endian limbs, five signed/unsigned widths, checked/wrapping operations, compact target and block work. |
| `S31/Semantics/Graph`, `Poseidon2`, `Blake2s`, `Sha256` | Explicit straight-line gate schedules and exact hash encodings. No uninterpreted hash callback is used. |
| `S31/Semantics/Functional` | Intrinsically typed field and fixed-length field-array `let`/lambda/application core, static specialization into first-order field polynomials, and an arbitrary-witness local constraint relation. |
| `S31/Gadgets/` | Primitive residual proofs, arbitrary auxiliary witnesses, constructive completeness and composition. |
| [`S31/Gadgets/Air/`](S31/Gadgets/Air/README.md) | The nine QM31 operation AIR row polynomials, opcode soundness, arbitrary-length packed arithmetic and conditional bridges, and an exact Gate multiset model. |
| [`S31/Gadgets/Functional/`](S31/Gadgets/Functional/README.md) | Typed source specialization, strict graphs, assertions, conditionals, effects, arrays and agreement with executable normalized relation nodes. |
| `S31/Gadgets/U16Selection` | Pointwise bit-constrained selection of u16-backed vectors, including proof that selected limbs inherit the input range bound. |
| `S31/Evidence/` | Checked operation coverage, non-vacuity/invalid-boundary theorems and live axiom enumeration. |
| `coverage.json` | Reviewed mapping of every operation to semantics, local gadget theorems and production source functions. |
| `source-bindings.json`, `proof-inventory.json` | Generated exact source identities and the complete theorem inventory, including the reused modules and three source-derived proof declarations. |
| `scripts/s31_formal.py`, `scripts/s31_formal_lib/` | Regeneration, escape/inventory checks, independent parity and adversarial proof controls. |

The package pins Lean **4.29.0** and Mathlib revision
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. The committed Lake manifest pins
transitive dependencies. Generated hash constants come directly from the
repository's Poseidon2, SHA-256, BLAKE2s and genesis assets. S31 uses the
existing canonical M31 implementation rather than copying field arithmetic;
`Gadgets/Field` proves its bridge to `ZMod 2147483647` and kernel-checks
primality with Mathlib's Lucas–Lehmer certificate for `2^31-1`. The generic
`norm_num` primality proof for a 31-bit number can exceed the kernel's
recursion limit on some hosts.

## Proven local obligations

### Typed functional core

`Functional.Expr Γ τ` can be constructed only with well-typed variables,
field addition/multiplication, `let`, lambdas and application. `Meaning` gives
these expressions their ordinary field/function meaning. `specialize` maps
field values to polynomial expressions and functions to compile-time Lean
functions, so the residual `Poly` syntax has only inputs, literals, adds and
multiplies. `specialize_correct` proves by induction that specialization
preserves meaning for **all** well-typed core expressions, environments and
input assignments. `program_correct` specializes the theorem to first-order
field inputs and output.

`Poly.Accepts` independently checks local add/multiply residuals and
existential intermediate values. `Poly.accepts_sound_complete` proves that
every satisfying witness yields exactly the polynomial evaluation, and that
an honest witness exists. `program_accepts_iff` composes this with the source
theorem. `specialize_beta` proves that static function application has the
same residual result as binding the argument in a `let`.

The hand-written `capturedSquare` term models
`let saved = x in let f = fun(y : m31) -> m31 => y * y + saved in f(saved)`.
`capturedSquare_zero_cost` reduces its residual tree to `x*x+x`, and
`capturedSquare_accepts` proves its local constraints accept exactly that
value for every M31 input. `Functional/Graph` lowers every residual polynomial
through the generic graph builder. `Poly.emit_valid` proves by induction that
emission preserves a valid builder, keeps the input prefix fixed, returns a
live wire, and never removes gates. `Poly.emit_prefix` proves emitted gates
append to the old graph, and `Poly.emit_value` proves the returned wire
evaluates to the polynomial on every input assignment. Thus `Poly.code_valid`
proves every emitted graph has valid wire indices and arities, while
`Poly.code_eval` proves its output value equals polynomial evaluation.
`Poly.code_accepts` applies the independent strict graph constraint theorem
to arbitrary intermediate witnesses. `program_graph_accepts` composes these
results with typed source specialization: for **every** program in the small
total field/function core, strict graph acceptance is equivalent to its
source result. For the worked example, the checked circuit is:

| Wire | Meaning | Local equation |
| --- | --- | --- |
| `0` | input `x` | supplied graph input |
| `1` | `x*x` | `w₁ - x*x = 0` |
| `2` | `w₁+x` | `w₂ - (w₁+x) = 0` |

The graph output is wire `2`. `capturedSquareCode_shape` proves the executable
lowering produces exactly those two gates; `capturedSquareCode_valid` proves
well-formed indices and arities. `capturedSquareCode_accepts` proves strict
acceptance is equivalent to the source result for **every** intermediate
witness.

`Functional/Outputs` extends this argument from one result to any list of
first-order field results. It emits all residual trees into one graph,
proves every returned wire is live, and proves that arbitrary satisfying gate
witnesses bind **every** output to its own source expression. In the worked
two-output circuit, `capturedSquarePair = [x*x+x, x]`, the graph still has only
two gates; its output indices are `[2, 0]`. The second result aliases the input
wire without adding a gate. `capturedSquarePair_rejects_forged_second` proves
that changing this second claimed value causes strict acceptance to fail.
These are kernel-checked statements about the small formal core. The Python
parser, S31's wider type set, library calls, partial operations, and
production AIR lowering are outside these theorems. The formal source
identity inventory now includes the Python
syntax, parser, elaborator, specializer and libraries so changes there force a reviewed
binding update; the source digests themselves do not prove compiler correspondence.

`Functional/Arrays` extends the typed source core with `[m31; N]` values,
pointwise addition and multiplication, static splats, indexed reads and
statically bounded `take`, `drop` and `concat` views.
Length is part of the type: indexing needs a `Fin N`, so the formal term
cannot address a missing lane. Residual arrays are `Fin N → Poly inputs`;
the closure and `let` constructors still disappear during specialization.
`arrayCode_accepts` proves that every satisfying gate witness binds every
output lane to the source value for **any** typed array-to-array term in this
core. Its converse constructs honest witnesses.

The hand-written `capturedArrayDouble` models `let saved = x in let double =
fun y => y + saved in double saved` for four lanes. Lean reduces its residual
expression to four pointwise additions and proves that the strict graph has
four add gates, outputs `[4,5,6,7]`, and accepts exactly
`[a+a,b+b,c+c,d+d]`. `rotateAndSaltCode_accepts` also proves the exact
prehash array view in the production example: `[a,b,c,d]` becomes
`[c+7,d+7,a+7,b+7]`. These are scalar gate models of source semantics;
production SIMD packing and AIR geometry are checked separately. Hashes and
the Python implementation are not covered by this theorem.

`Functional/ArrayNodes` takes the next step from the abstract graph to actual
normalized relation nodes. It proves `array_concat`, `array_get`, and
`array_slice` evaluate to the same values as the typed source views. For
`take<k>`, the slice starts at zero; for `drop<k>`, it starts at `k` and keeps
`N-k` lanes. Each theorem includes the normalized node's shape and bounds
checks. `rotateFourView_code_shape` proves that
`concat(drop<2>(x), take<2>(x))` emits **zero arithmetic gates** in the formal
field graph and exposes input wires `[2,3,0,1]`; its strict acceptance theorem
binds the four output lanes to `[c,d,a,b]` for input `[a,b,c,d]`. These proofs
do not establish that Python emits the matching nodes or that Zig performs
the same wiring without extra AIR rows.

`Functional/ArithmeticNodes.arithmetic_graph_iff_node` makes the same
source-to-normalized-value comparison for pointwise M31 `+` and `.*`. The
normalized evaluator's `add` and `mul` nodes zip equal-length operand arrays;
Lean proves the zipped list is exactly the source's indexed pointwise result.
The strict graph side includes arbitrary intermediate gate witnesses, so this
is an equivalence of acceptance, not merely an honest-value example. Python
emission and production AIR correspondence remain outside the proof.

`Gadgets/Air/Qm31Ops` formalizes all nine residuals of the production circuit
AIR's QM31 operation row: one one-hot equation, four Boolean flag equations,
and four output-limb equations. `accepts_iff` proves that **every** accepted
row has exactly one of the add, subtract, QM31 multiply, or pointwise multiply
flags and the corresponding output. `honest_row` constructs an accepted row;
`all_flags_zero_rejected` and `two_flags_rejected` check malformed flag
patterns. `s31_row_iff` specializes the add and pointwise multiply opcodes to
four M31 lanes using the proved M31-to-ZMod map.
`row_iff_normalized_node` then proves the row model accepts precisely the
outputs of the executable normalized `add` and `mul` relation nodes for one
full four-lane chunk. The proof models the production equations and the
`simd.mul` opcode choice; source hashes pin the reviewed Zig files.

`SimdChunks.partial_row_iff_normalized_node` extends the same result to final
chunks with zero to four active lanes. `SimdChunks.packedRows_iff` covers
arrays of any length, showing that exactly `ceil(n/4)` row witnesses bind all
active lanes, including positions on both sides of a four-lane boundary.
These results quantify over arbitrary M31 values in unused input positions
and existentially construct the unused output limbs; only active output lanes
appear in the normalized array result.

`FunctionalBridge.array_graph_iff_air_row` composes the typed functional
array expression, its strict scalar graph, the normalized arithmetic node,
and one packed AIR row model for the final operation. It applies to arbitrary
source operand expressions in the formal total core, for either pointwise
operation and any result length at most four. The stronger
`array_graph_iff_packed_rows` covers any result length and every packed row
of the final operation. Both theorems evaluate operand subexpressions through
the source graph model; they do not supply AIR rows for those operand
computations.
`SelectRows` models the direct array conditional's one shared complement row
and three arithmetic rows per packed word. With an explicit Boolean selector
premise, all packed rows agree
with the source conditional, strict graph relation and executable normalized
`select` node for any array length. A kernel-checked selector-`2` control
demonstrates that the Boolean premise cannot be dropped.
`QuadField` proves the AIR's four-coordinate multiplication is the field
product in a two-stage quadratic tower. Its checked nonsquare lemmas for
`-1` and `5` imply that an arbitrary QM31 self-product selector wire is
canonical zero or one; no base-encoding assumption is needed.
`untrusted_self_product_select_iff_evaluateNode` composes that row with the
source M31 selector coordinate binding and the full direct selection row
schedule.
`BooleanRows` proves the compiler's five scalar Boolean row schedules for
base-field encoded bit operands, including all OR, XOR and select
intermediates. Arbitrary satisfying row witnesses have exactly the Boolean
result; the converse constructs honest witnesses.
`BitRows` proves the ordinary `checkedBitWord` path: an arbitrary anchor
self-loop enforces a zero arithmetic value, and multiply/subtract/zero rows
enforce `q² = q` for every QM31 witness. The tower proof therefore gives a
canonical bit even when the input witness hint is untrusted. A concrete
selector `2` is rejected.
`ZeroRows` proves the full `isZeroWord` arithmetic row schedule sound and
complete over arbitrary QM31 witnesses, including both zero-assertion
self-loops and the unconstrained inverse value when the input is zero.
`base_zero_test_iff_evaluateNode` connects its canonical scalar restriction
to the executable normalized `is_zero` operation. A forged zero indicator
is rejected by a kernel-checked control.
`InverseRows` proves the direct inversion row topology for each packed word
and for every array length. Its `packedInverseRows_iff` gives the exact
nonzero precondition and M31 inverse result for every active lane, even with
arbitrary padding in the final source word. A zero active lane cannot satisfy
the rows.
`UnpackRows` proves the one- or two-row SIMD lane extraction used when a
packed scalar enters a zero test, Boolean operation, or array selection.
For any active array index, the extracted base-field word is exactly that
lane, independently of padding in the packed source word.
`MixRows` composes the sum projection, broadcast multiplication, and packed
addition used by four-lane `mix4`. Its result is proved equivalent to the
executable `mix4` step inside normalized repeat bodies.
`SumRows` proves that the direct `sum_lanes` mask, pairwise reduction, and
projection rows accept exactly the normalized node's M31 result for every
nonempty array length. The theorem permits arbitrary unused coordinates in
the final input word and models the one-lane alias separately.
The [AIR model README](S31/Gadgets/Air/README.md) works through a two-lane
example.

These theorems do not prove that Zig emits the modeled rows or that the Gate
lookup connects row operands and outputs to the compiled circuit. Short-chunk
emission, preprocessed address/multiplicity construction, correspondence
to production lookup/LogUp columns, whole-trace AIR, and the STARK verifier
remain separate obligations.

`GateLookup.addressed_row_sound` adds a conditional address join: if the
positive input events and multiplicity-weighted output events balance as an
**exact multiset**, and every address has one produced value, each row's
operands equal the values produced at its preprocessed addresses. The local
AIR theorem then fixes the row output. `forged_input_rejected` rules out a
row that computes correctly from an input value different from its claimed
producer. The exact-multiset premise is stronger than the production LogUp
check; the full probabilistic multiset reduction, interaction trace, compiler producer
uniqueness, and public boundary are not proved here.
The checked nonempty example includes a balanced honest row and a locally
valid forged row whose public output claim has been changed consistently;
the forged row still fails exact Gate balance at its input address.
`unique_produced_of_nodup_outputs` proves the needed uniqueness from distinct
row output addresses and disjoint, consistent external producers. The
`indexed_outputs_nodup` lemma handles the abstract `start + gate_index`
layout. Matching this premise to all production Zig allocation paths remains
an open compiler-correctness step.

`EqRows` models the equality component's two Gate uses, which carry one
shared trace word. Under exact Gate balance and one produced value per
address, `eq_row_sound` forces the values at both source addresses to agree.
For a short final SIMD word, the compiler subtracts the two packed words,
masks unused lanes with a pointwise multiplication, and compares the result
with zero. `partial_eq_sound_of_lookup` composes those arithmetic rows with
the equality lookup and proves every active lane agrees.
`packedEqRows_iff` extends this post-lookup relation to arrays of every
length, including lengths divisible by four and arbitrary unused padding.
The converse constructs local rows when all active lanes agree; concrete
accepted and forged two-lane examples are kernel checked.

`GateChallenge` proves a quantitative part of lookup compression soundness.
The six-element Gate tuple is encoded by the same Horner polynomial and
relation id as Zig. Two distinct canonical Gate events collide for at most
five of the `2147483647⁴` QM31 choices of `alpha`; fixed `alpha` and tuple
have exactly one bad `z` that zeros the denominator. This is a pairwise
challenge bound. `collisionUnion_card_le` extends it to a list of distinct
tuple pairs: at most five bad `alpha` choices per pair. For a fixed `alpha`,
at most one `z` per tuple zeros a denominator.

`LogUpNumerator` proves the algebraic second half of the lookup reduction.
For distinct compressed values `a` with net field multiplicities `w(a)`, it
forms the numerator of `Σ w(a)/(z-a)`. If one weight is nonzero, that
numerator is nonzero and has degree at most `support size - 1`; thus the
reciprocal sum can hide the discrepancy for at most that many eligible `z`
values. `LogUpCount` proves that an unequal pair of compressed event lists
has a nonzero field weight when **each list length is below M31's modulus**.
It also proves that its weighted reciprocal sum equals the difference of
the two actual list sums. The length premise matters: at least `p` copies
of one event have zero field multiplicity in characteristic `p`.
`LogUpCount.unequal_lists_have_nonzero_weight_of_counts` proves the sharper
condition: each individual compressed event occurs fewer than `p` times
on both sides. The total relation may contain more than `p` events.

`GateLogUpBridge.fixed_gate_multiset_sound` composes the two bounds for
**fixed canonical Gate event lists**. If the lists differ as multisets and
each has fewer than `p` events, an exceptional set of at most `5s²`
`alpha` values can collide distinct tuples, where `s` is the number of
distinct Gate events. For every other `alpha`, an exceptional set of at
most `t + (t - 1)` `z` values covers zero denominators and accidental
reciprocal-sum cancellation, where `t` is the number of distinct compressed
values. Outside those sets, the two sums of production-order
`1/(H(tuple) - z)` terms differ. This is the algebraic reduction needed
by Gate LogUp; it handles repeated events and the characteristic bound.
`GateLocalCounts.fixed_gate_multiset_sound_of_counts` transfers the sharper
per-event count premise through collision-free tuple compression, retaining
the same exceptional-set bounds for arbitrarily large total event lists.
`GateAddressCounts` proves a practical sufficient condition: if the integer
use and yield histograms are below `p` at every address, every event count
is below `p`. The Zig preprocessed builder now rejects a multiplicity as
soon as an increment would reach `p`, including permutation and private
SHA boundary uses. A native boundary test checks the `p-1` and `p` cases.
The exact correspondence between those Zig counters and the modeled
Gate event lists remains a separate proof obligation.

`GateCounter` now models Zig's checked increment rule and proves the
successful result equals the integer sum of all increments at each
address while remaining below `p`. For unit increments over a supplied
Gate event list, it proves the resulting counts equal that list's address
histogram and discharges the histogram premise of the fixed-list LogUp
theorem. The `p−1` count is accepted, while incrementing it to `p` and
adding `p` at once are rejected. Connecting the actual Zig traversal of
every circuit component to those exact modeled event lists is still open.

`GateCounterCircuit` proves the compact yield representation used by the
circuit agrees with that expanded event histogram: a row output at address
`a` with multiplicity `m` contributes one checked increment `(a,m)`, while
the ideal Gate list contains `m` copies of its output event. The theorem
holds for every address and arbitrary rows and external yields. Successful
checked use and compressed-yield walks, together with closed Gate fractions
and good challenges, now imply exact circuit Gate balance without assuming
the address histogram bounds separately.

`LogUpInteraction` models the other side of the reduction. Its single and
paired residuals use the formulas in the Zig verifier. Given nonzero
denominators, a vanishing residual fixes the exact reciprocal term or
pair sum. It models the non-final interaction columns as cumulative sums
within each row and the last column as a shifted running sum across rows.
`claimed_sum_of_checked_power_two_interaction` proves that these row
constraints force the claimed sum to equal the sum of all row fractions
for any power-of-two row count and any permutation of predecessor rows.
The proof establishes that the row-count cast is nonzero in QM31. A
kernel-checked zero-denominator control shows why the nonzero premise is
essential: a pair constraint can vanish for any running-sum difference
when both denominators are zero.

`Qm31GateInteraction.qm31_ops_claimed_sum` specializes that argument to
the circuit's `qm31_ops` component: each row contributes exactly three
Gate lookups, with the two input uses paired in the first secure column
and the multiplicity-weighted output yield as the final singleton. Under
the two AIR residual equations and nonzero denominators, the component's
claimed sum is exactly the sum of the `rowContribution`
values. This discharges the component-level fraction algebra, while the
actual column emission and verifier evaluation still need correspondence.

`qm31_ops_closed_gate_balanced` adds the verifier's closed global claim and
modeled external Gate terms, then derives exact Gate multiset balance from
those checked `qm31_ops` residuals under canonical-address, histogram, and
good-challenge premises.

`EqGateInteraction` does the same for `assert_eq`'s two Gate reads, which
form a single paired interaction column. `eq_claimed_sum_eq_event_sum`
derives its exact component claim from its AIR residuals. The
`qm31_and_eq_closed_gate_balanced` theorem combines the arithmetic and
equality claims with the remaining modeled Gate events and the global
closed claim to recover exact multiset balance. With a unique producer
per address, `eq_row_sound_of_shared_gate` then proves the two produced
values read by an equality row are equal. Other components and the actual
Zig-to-Lean column correspondence remain open.

`GateContributions` connects the exact Gate event lists to the row terms.
For each arithmetic row it proves that two input uses contribute two
positive reciprocals and an output repeated `multiplicity` times contributes
the negative field multiplicity times its reciprocal. It aggregates those
terms over all rows and external Gate uses/yields. Consequently,
`closed_gate_contribution_balanced` proves that a closed reciprocal sum
forces exact Gate multiset balance under the canonical-address, event-count,
and good-challenge premises above. This is a conditional composition
theorem; its closed-sum premise is not yet discharged from the compiled
interaction columns.

`closed_gate_contribution_balanced_of_counts` uses the per-event version,
so the proof has no artificial total-trace-length limit.
`closed_gate_contribution_balanced_of_address_counts` accepts the modeled
address histogram bounds directly.

`GateFinal.lean`'s `addressed_row_sound_of_closed_gate` composes this conditional
closure with `GateLookup.addressed_row_sound`: every addressed row operand
equals its unique producer value, and the arithmetic AIR fixes the result.
`addressed_row_sound_of_closed_gate_counts` carries the stronger per-event
count premise through the same conclusion.
The honest 5+3=8 fragment closes for every field challenge. The locally
valid forged 4+3=7 fragment, which falsely reads an address that produced
5, cannot close for challenges outside the bounded exceptional sets.

The theorem concerns fixed event lists. Proving that the production
interaction columns and their verifier expressions correspond to the
Lean model over every row and component, proving the compiler emits the
modeled events with canonical addresses and bounded per-event counts, and showing
Fiat–Shamir challenges follow commitments remain open. The core STARK
verifier's cryptographic soundness is separate.

`Functional/Assertions` adds a separate source contract with any number of
`assert_eq` pairs. It compiles each side to an output wire and checks the
paired values for equality. `Contract.accepts_iff` proves that strict graph
acceptance plus these equality checks is equivalent to all claimed outputs
matching their source expressions **and** every assertion holding. The
modeled example corresponds to this one-lane S31 program:

```s31
use std@1;
circuit square_fixed(public x: [m31; 1]) -> public [m31; 1] {
    assert_eq(x .* x, x);
    x
}
```

Its formal graph has one multiplication gate and graph outputs
`[0, 1, 0]`: output `x`, then the two asserted sides `x*x` and `x`.
`squareFixedPoint_rejects_nonfixed` rules out every input where `x*x ≠ x`.
The equality check is part of the formal acceptance relation here; a proof
that the production compiler emits the corresponding AIR assertion remains
an explicit obligation.

`Functional/Conditional.if_accepts_iff` composes three total functional
expressions (selector, true arm, false arm) in one strict graph with the
independent polynomial select relation. It proves that every satisfying
auxiliary witness has a selector of exactly `0` or `1` and an output equal
to the matching source arm; honest witnesses exist for both values. The
selector is represented by an M31 expression in this small model and its
bitness is imposed by the select constraint. The theorem does not verify
the Python effect checker or the production `select` AIR emission.

`Functional/ArrayConditional.array_if_accepts_iff` extends that statement to
any fixed array length. It emits the selector and both complete branches into
one strict graph. The separate selection relation constrains the shared
selector to zero or one and every output lane to the matching branch. The
theorem quantifies over arbitrary intermediate gate and selection witnesses;
its converse supplies honest witnesses. `chooseOrSeven_accepts` instantiates
the theorem with a two-word input `[bit, value]`: both output lanes must be
seven when `bit=0`, or `value` when `bit=1`. As with scalar conditionals, the
production compiler and AIR correspondence remain separate obligations.
`array_select_iff_evaluateNode` proves the pointwise selector predicate is
equivalent to the executable normalized `evaluateNode` result for a concrete
`select` node with equally shaped M31-array operands. It covers both the
canonical `selector ≤ 1` check and the exact false/true operand order;
selectors outside the bit range are rejected. `array_if_accepts_iff_evaluateNode`
composes that result with source specialization and the strict graph theorem.
It does not prove that Python emits that normalized node or that Zig emits its
modeled AIR constraints.

`Functional/Effects` makes the totality premise concrete in a smaller
expression language with checked inversion. Its computable `isTotal` check
accepts inputs, literals, addition and multiplication, and rejects every
inverse. `total_has_value` proves that an accepted expression produces a
value for every input. `total_to_poly` lowers exactly those accepted
expressions into the existing residual polynomial core, and
`total_graph_accepts` composes that lowering with arbitrary-witness strict
graph soundness. `eager_if_iff_lazy_if` proves that evaluating both
arms and constraining the selector agrees with ordinary conditional
evaluation whenever both arms pass this check. `eager_graph_iff_lazy_if`
places the two emitted arms in one strict graph, then joins their witnessed
outputs with the select equation and proves the same equivalence. The counterexample
`if false then inverse(0) else x` evaluates to `x` lazily but has no eager
witness. This formal check models the rule's rationale; the Python effect
pass, higher-order call analysis and all builtin classifications still need
a verified connection to this model.

`U16Selection.u16_vector_select_iff` lifts the field selector equation to
every limb of a fixed-width vector. Its output is exactly the selected input
vector for either Boolean value, including an explicit selector constraint
for the mathematical zero-length case. The production-shaped
`u16_wire_vector_select_iff` also treats the complement, two products, and
sum as arbitrary intermediate witnesses; it proves that those four
operations and the Boolean selector give the same result. Both versions prove
that canonical u16 input limbs yield output limbs below 65,536. This supports
source-level byte and wide nominal selectors without adding a fresh range
witness. It remains a local constraint theorem until correspondence with each
production Zig profile is proved.

For one limb with false input 7 and true input 9, the witnessed equations are
`c + s = 1`, `l = c·7`, `r = s·9`, and `out = l + r`:

| Selector `s` | Complement `c` | Left product `l` | Right product `r` | Output |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 1 | 7 | 0 | 7 |
| 1 | 0 | 0 | 9 | 9 |

The separate Boolean equation `s² = s` rules out every other field value.
`u16_value_valid_iff` derives the range premises from normalized relation
values, and `u16_wire_vector_matches_source` proves that the selected value
uses the same canonical zero test and arm order as relation IR's `select`
evaluator. This still does not prove that the Zig compiler emits the modeled
constraints or that the Stwo AIR enforces every builder operation.

Soundness quantifies over every satisfying auxiliary witness. Completeness
constructs witnesses for every input within the stated range and shape
premises. Honest-witness evaluation alone is insufficient for soundness.

| Gadget family | Main results |
| --- | --- |
| Field arithmetic and zero anchors | Residual equations iff addition, multiplication, equality or zero; canonical M31/ZMod bridge and inversion iff nonzero. |
| Boolean operations and selection | Bit equation iff 0 or 1; NOT, AND, OR, XOR, scalar/Boolean selection; zero indicator sound for every inverse witness, including the unconstrained inverse at zero. |
| Range and packing | Byte range via scaled u16; 16 Boolean bits iff u16; byte-pair packing, endian round trips and canonical digest reduction, including quotient 2. |
| Carry/borrow arithmetic | Local field equations imply integer equations; whole chains iff checked or wrapping arithmetic; reversed subtraction iff ≤ or <. |
| Signed arithmetic | Sign extraction, most-significant-limb sign, two's-complement interpretation, signed comparison, overflow predicates, composed signed checked addition/subtraction iff mathematical results. |
| Packed M31 lanes | QM31 basis multiplication, coordinate extraction, active masks, scalar multiplication, production sum projection/dual literals, `mix4`, active-lane inversion. |
| Static repeats | Pointwise primitive constraints, sum witnesses, bodies and arbitrary finite repeat counts iff the executable recurrence. |
| Hashes | Arbitrary intermediate gate witnesses iff the full Poseidon2 leaf/pair, personalized terminal BLAKE2s and header double SHA-256 results, including packing and digest reduction. |
| Bitcoin target | One-hot exponent range, byte placement, nonzero byte-sum inverse and high-zero bytes iff a positive target within mainnet's `2^224-1` limit. |
| Bitcoin division/work | Nontruncated schoolbook product, terminal carry, strict remainder, unique quotient/remainder and the exact block-work formula. |
| Wires and public bindings | Constant/alias/get/concat/slice identities, assertion residuals, fixed-width segment/padding binding, proof-mode independence; a successful evaluator returns exactly the declared claim **and every declared output equals its computed value**, including kind and width. Changing only a private witness cannot change the claim. |
| Graph wiring | `Code.WellFormedFor` requires that every gate reads an input or earlier wire, every output index exists, and each primitive has its exact operand count. `Code.check_sound` proves that the executable checker implies this proposition; `strict_code_sound_complete` combines it with arbitrary-witness primitive soundness. |
| Builder composition | `emit_valid` and `build_valid` prove that valid emitted gates and live outputs produce a valid circuit. The actual Poseidon2 fifth-power, SHA sigma and complete SHA compression-round builders preserve this invariant. Their strict circuit relations are proved equivalent to the computed outputs; fifth power and sigma are also reduced to explicit mathematical formulas. |

Range premises are explicit. A modular equation alone cannot imply an integer
equation: the bridge needs both sides below M31. For the Bitcoin multiplication
columns, the maximum is `32*255² + 255 + 65535 = 2,146,590 < 2³¹-1`.
High product digits and the terminal carry are retained, so the multiplication
proof cannot accept truncation of a 512-bit product.

The hash relation checks each primitive gate and existential intermediate
wire; its definition does not call the hash interpreter. `Graph.Accepts`
proves generic straight-line composition. Word gadgets use canonical
`BitVec 32` values, per-bit polynomial equations and an integer word-add carry
equation; the range/limb lemmas separately justify those encodings. Fixed
hash schedules are marked `irreducible` to keep elaboration from repeatedly
expanding thousands of gates; they remain explicit, executable definitions
and introduce no axiom.

`Graph.Accepts` on its own has the historical `getD` fallback for malformed
indices or missing primitive operands. Use `Code.strictAccepts` when making a
statement about a valid circuit: its `WellFormedFor` premise rules out these
fallbacks. The formal package proves the generic rule and small valid/invalid
schedule examples. The CI gate runs `s31-check --schedule-check` over 57
generated hash profiles: Poseidon2 pair and four leaf sizes, SHA-256
compression, and BLAKE2s word counts 0–16 with three personalization values.
It also demands rejection of an invalid wire and a missing operand. Lean proves
that a `true` checker result implies `WellFormedFor`. The 57 executable results
are **regression evidence, not kernel-checked proofs that every parameterized
hash schedule is valid**. Fixed schedule certificates for all parameters and
the correspondence to production AIR emission remain obligations.

### Kernel-certified hash subcircuits

The builder proof works gate by gate, so Lean does not need to normalize a
whole hash permutation. For the Poseidon2 fifth-power routine, input `x` is
wire 0 and the generated circuit is:

| New wire | Constraint |
| --- | --- |
| 1 | `w₁ = x · x` |
| 2 | `w₂ = w₁ · w₁` |
| 3 | `w₃ = x · w₂` |

`Poseidon2.fifth_valid` proves that these gates preserve valid wiring in any
already-valid builder state. `Poseidon2.fifthCircuit_valid` proves the complete
one-input circuit is well formed. `Poseidon2.fifthCircuit_correct` then proves,
for **every** satisfying intermediate witness, that the only accepted output
is the canonical M31 value of `x⁵`.

For SHA sigma, the one-input circuit emits `rotr(x,a)`, `rotr(x,b)`, their XOR,
then either `shr(x,c)` or `rotr(x,c)`, then one final XOR. The
`Sha256.sigmaCircuit_correct` theorem covers either choice and arbitrary shift
amounts. `Sha256.round_valid` then proves that the **actual SHA-256 round
builder** preserves valid wiring for any live eight-word state and message
wire. Its 27 gates include `Ch`, `Maj`, both capital sigma functions, the
round constant and the output additions. `Sha256.rounds_valid` inducts over
the actual `foldlM` of round/message pairs: for any list of live message
wires, the state remains eight live words and the builder adds exactly
`27 × rounds` gates. `Sha256.roundCircuit_valid` proves
that a complete nine-input circuit generated by that builder is well formed;
`roundCircuit_strict_sound_complete` says every accepted auxiliary witness
has exactly the computed eight-word round output. The circuit proof holds for
every round constant, not merely the 64 standard constants.

`Sha256.roundsCircuit_valid` and `roundsCircuit_strict_sound_complete` lift this
to a complete parameterized circuit for any list of `(message wire, constant)`
pairs. The first eight inputs are the initial state. Each message wire must
name one of the circuit inputs, so a 64-round instance can take all 64
expanded words as inputs. The theorem covers every satisfying witness for
those rounds. It does not yet certify that the 48 expanded message words are
the correct SHA-256 schedule of a 16-word block.

`Sha256.sha64Circuit_valid` specializes this to the generated table of 64
SHA-256 round constants. Its 72 inputs are eight state words followed by 64
already-expanded message words. `sha64Circuit_strict_sound_complete` proves
that the 64-round core accepts exactly the circuit's computed eight-word
state for every input and every auxiliary witness. The round invariant gives
`64 × 27 = 1728` gates in this core; it excludes message expansion and the
final eight feed-forward additions.

These are proofs of generated subcircuits used by the hash schedules. The
complete Poseidon2, SHA-256 and BLAKE2s schedules still need compositional
builder invariants for message expansion, state indexing and final
feed-forward. The one-round theorem
relates acceptance to the generated circuit evaluator; a separate
formula-level refinement theorem for the entire compression function is not
yet present.

## Scope of the claim

**The local mathematical constraint models are proved. Production compiler
correctness is not proved.** Source hashes and the operation map make a
manual correspondence review inspectable; they cannot establish that every
Zig lowering emits exactly those constraints. In particular, raw text/JSON
parsing and specialization, general compiler lowering, chip/direct/sparse
AIR correspondence, lookup/LogUp composition over arbitrary traces, Zig
machine code, STARK soundness and zero knowledge remain separate obligations.
The typed model constrains private values mathematically; visibility affects
the public ABI and does not itself imply witness privacy.
The public binding theorems concern accepted executions under the *same declared*
public inputs and outputs. They prove agreement for every output, including
the second output of a two-output example, but do not assert that private
inputs are hidden or that a circuit is bound to the claim: production AIR correspondence remains
an explicit separate obligation. Lean also checks one honest private binding,
a changed private witness, and a forged public output claim.

The Python parity corpus is regression evidence for the executable semantics,
not a proof of compiler or cryptographic correctness. Hash parity includes
Python `hashlib` and the existing independent Poseidon2 implementation.
The source inventory includes both reused Lean modules, whose theorems are
also included in the live axiom audit. Only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms are approved. Proof sources reject
`sorry`, `admit`, custom `axiom`, `unsafe` and `native_decide`.

## Reproduce the gate

Run from the repository root with the pinned Lean toolchain available:

```sh
python3 scripts/s31_formal.py
python3 -m unittest scripts.tests.test_s31_formal
mkdir -p zig-out/s31/formal
cd formal/s31
lake exe cache get Mathlib.Data.ZMod.Basic Mathlib.Tactic Mathlib.NumberTheory.LucasLehmer
lake build S31 S31.Evidence.AxiomAudit s31-check
lake env lean S31/Evidence/AxiomAudit.lean > ../../zig-out/s31/formal/axioms.log
LEAN_NUM_THREADS=1 lake env leanchecker -v S31 S31.Evidence.AxiomAudit RiscvRefinement.Field.M31 RiscvRefinement.Recursion.CompactPoseidon > ../../zig-out/s31/formal/kernel.log
cd ../..
python3 scripts/s31_formal.py \
  --audit zig-out/s31/formal/axioms.log \
  --kernel-log zig-out/s31/formal/kernel.log \
  --parity formal/s31/.lake/build/bin/s31-check \
  --controls --report zig-out/s31/formal/evidence.json

# The same executable can run the schedule gate by itself:
formal/s31/.lake/build/bin/s31-check --schedule-check
```

`leanchecker` replays declarations with Lean's kernel; it is not a separate
proof assistant. One worker bounds memory without reducing its checks. The
gate requires exact replay and theorem inventories, builds every `S31.*`
source, rejects missing evidence, and compiles valid controls before requiring
invalid controls to fail. It also alters actual byte-range, carry-base and
signed-overflow definitions and requires their original proofs to fail.
Temporary mutations never alter repository sources.
The mutation set includes polynomial addition and graph emission in the
functional core; changing either addition to multiplication must make the new
proofs fail to compile.

The dedicated [CI workflow](../../.github/workflows/s31-formal.yml) runs these
steps without a skip path and preserves live evidence. Caches, binaries and
raw logs are ignored build artifacts. After a reviewed semantics/source
change, regenerate with `python3 scripts/s31_formal.py --write`, inspect the
diff and rerun the full gate. Regeneration updates identities; it does not
prove a new correspondence obligation. Formal checking adds no constraints
or work to the production prover.
