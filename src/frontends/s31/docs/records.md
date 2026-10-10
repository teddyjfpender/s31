# Nominal records: names for values, zero proof work for grouping

S31's `struct` is a **static record type**. It gives names to fields that
already hold circuit values. Inside a program, specialization removes the
record before the arithmetic relation is built. When a circuit returns a
public record, relation v2 also carries its nominal layout and field paths
to the native verifier. That metadata adds no arithmetic gate or AIR row.

## A complete example

The executable [record source](../examples/arithmetic/record_square_sum.s31)
contains this program:

```s31
struct Powers {
    square: [m31; 4],
    doubled: [m31; 4],
}

fn powers(x: [m31; 4]) -> Powers {
    Powers { doubled: x + x, square: x .* x }
}

circuit record_square_sum(private x: [m31; 4]) -> public [m31; 4] {
    let p = powers(x);
    let result = p.square + p.doubled;
    result
}
```

The literal writes `doubled` first, but the declaration fixes evaluation order:
`square`, then `doubled`. The compiler checks that both fields appear exactly
once and have `[m31; 4]` type. A second struct with the same field names and
types would still be a different nominal type.

For the [handwritten assignment](../examples/arithmetic/record_square_sum.valid.json),
each array entry is an independent M31 lane. Here are all four calculations:

| Array position | Private `x` | `p.square = x²` | `p.doubled = x+x` | Public `result` |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 0 | 0 | 0 | 0 |
| 1 | 1 | 1 | 2 | 3 |
| 2 | 2 | 4 | 4 | 8 |
| 3 | 7 | 49 | 14 | 63 |

All arithmetic is modulo $p=2^{31}-1$; these small values happen not to wrap.
The normalized relation contains exactly three computation nodes:

```text
square  = mul(x, x)
doubled = add(x, x)
result  = add(square, doubled)
```

The circuit builder gives each operation wires and arithmetic gate events.
For one array position, the arithmetic residuals are conceptually

$$s-x^2=0,\qquad d-(x+x)=0,\qquad r-(s+d)=0\pmod p.$$

The generated circuit also has input/output binding and wire-connection
constraints. Those bind the public `result` to the arithmetic chain. At
`x=7`, a claimed `result=64` leaves the last residual equal to 1, so the
independent relation evaluator rejects it and a sound native proof cannot
verify it. The [positional tuple version](../examples/arithmetic/record_square_sum_manual.s31)
produces **byte-for-byte identical normalized relation JSON**. The generated
cost reports also match in canonical IR, component profile, raw and padded
AIR rows, preprocessing, and FRI settings. Both have 314 raw arithmetic rows,
512 padded rows, and 4,096 preprocessing cells under `direct-gate`. The
[native cost record](../../../../design/s31/measurements/language/record-zero-cost-2026-10-10.json)
pins the exact comparison and successful generated-verifier proof. The records themselves add zero
circuit gates and zero AIR rows; the three field computations remain.

The same helper can be consumed with a named pattern:

```s31
let Powers { square, doubled } = powers(x);
let result = square + doubled;
```

The [destructuring source](../examples/arithmetic/record_square_sum_destructure.s31)
compiles to the **same normalized relation** as both the field-access version
and the positional tuple version. A pattern can bind only the fields needed
by its caller; construction still evaluates every field. The pattern checks
the struct's nominal type before projecting, so a same-shaped struct with a
different name cannot match it. Named patterns also nest inside tuple patterns
and work in expression-level `let … in` bindings.

## What is checked before proving

The parser requires a struct declaration before use, 1–64 uniquely named
fields, and every constructor field exactly once. A field type can be a
first-order S31 type, an earlier struct, or a tuple of those. It rejects
function-valued fields and recursive layouts. Layouts are bounded to 32
levels and 1,024 flattened first-order fields. The type checker checks every
function body, even unused ones, and enforces nominal type identity at calls
and returns. Named `p.field` access is permitted only on a record with that
field; numeric `.0` remains tuple projection.

Construction evaluates **every** field in declaration order, even if a
later expression reads only one. This matters for partial operations:
`Pair { kept: x, ignored: std::math::inv(x) }.kept` can still fail at `x=0`.
The totality checker carries that failure through field projection, so it
rejects this expression in either arm of a witness-dependent `if`. The
record does not hide proof obligations in an unused field.

Records may be passed to and returned from pure `fn` helpers and stored in
`let` bindings. Circuit parameters may also be nominal records with M31
leaves. A circuit may return either a public record or a first-order M31
value under the `direct-gate` v2 profile. The native verifier accepts one
canonical typed v2 statement with named input and output paths. Other leaf
types remain outside this boundary.
Whole-record `if` and `assert_eq` now traverse first-order leaves in declared
field order. A record `if` evaluates both branches and emits exactly the
selectors that a handwritten fieldwise program emits. A record assertion
emits exactly the corresponding leaf assertions. Nested tuples and records
work the same way. The conditional is accepted only when all leaves have
constrained selectors and neither branch can fail when inactive. Struct
identity is nominal, so equal field layouts under different type names cannot
be compared or selected as one value. The proof relation still has only
first-order wires.

### Selection by hand

The [complete program](../examples/control/record_choice.s31) defines
`Pair { first: [m31; 1], nested: ([m31; 1], [m31; 1]) }`. It computes
`b = is_zero(x)`, `a = (2x, x, y)`, `c = (2y, y, x)`, and returns
`if b then a else c`. For `x=0, y=7`, the prover computes `b=1` and the
public result `(0, 0, 7)`. For `x=3, y=7`, it computes `b=0` and the result
`(14, 7, 3)`. Each tuple entry here is one M31 word, reduced modulo
`p=2³¹−1`.

The residual relation has six nodes: one `is_zero`, two `add`, and three
`select`. For each field `j`, the selector enforces the value equation
`r_j = c_j + b·(a_j−c_j)` over M31, together with the circuit's bit
constraint for `b`. The proof also binds all three result words to the
typed public record paths. The
[handwritten fieldwise source](../examples/control/record_choice_manual.s31)
has byte-for-byte equal normalized relation JSON; it chooses each leaf
explicitly. No record node, field tag, or product-specific AIR row is emitted.
The fixture passes source lowering, strict public ABI flattening, and the
independent value oracle. The native direct-gate acceptance gate builds both
forms and compares the complete reported circuit/AIR geometry: each has 299
raw QM31 rows, 512 padded rows, and zero rows in the other AIR components.
It proves both selector values under the typed record ABI; the native verifier
accepts the honest statements and rejects changed public claims. This checks
the implemented lowering for this example; the separate Lean product theorem
proves the per-leaf selector rule as a model, and full compiler correspondence
remains open.

## A fixed-width integer use

The [division example](../examples/math/division/record_i32_division.s31)
wraps the quotient and remainder of one `std::int::div_rem` operation in a
`DivResult` record. Accessing `.quotient` returns the existing `i32` value;
it does not repeat the division gadget. The quotient may be the only public
output, while the remainder and strict remainder bound remain inside the
proved relation. This is a useful way to make math-library APIs readable
without changing the generated AIR. The record and positional versions each
have one division node, 1,847 raw arithmetic rows, 2,048 padded rows, and
16,384 preprocessing cells under `direct-gate`; their canonical IR hashes
match exactly. The generated native verifier accepted the record proof and
rejected a changed quotient claim.

## Formal status and inspection

The [Lean record model](../../../../formal/s31/S31/Gadgets/Functional/RecordValues.lean)
models named construction, projection, and pattern desugaring as typed product
operations and proves specialization has the same residual polynomial as the
direct three-operation program. A separate generic `Except` theorem proves
that failure in an unused field survives projection and the first declared
failure wins if both fields fail. The executable source-to-source comparison checks
the current Python compiler erases the example to the same normalized
relation as a tuple. Native verification checks the resulting proof and
changed-public-statement rejection. As with the rest of S31, a machine-checked
refinement of the entire Python parser and Zig AIR emitter remains open.
The separate [public boundary model](../../../../formal/s31/S31/Gadgets/Functional/RecordBoundary.lean)
proves typed flatten/reconstruct, distinct tagged positions, alias equality,
and that private input roots contribute no public statement words. It models
the validated layout and does not claim to verify the production parsers.

Run `s31 lower`, `s31 explain`, and `s31 equations` on the source to inspect
the exact normalized nodes, gate spans, AIR geometry, and source positions.
The [source-to-AIR guide](reference/LANGUAGE_AND_AIR.md) explains how the
generic circuit gates become AIR constraints and trace polynomials.

## Inspect the source layout

Run this without building a proof package:

```sh
python3 src/frontends/s31/python/s31.py source-layout \
  src/frontends/s31/examples/arithmetic/record_square_sum_destructure.s31
```

The JSON report lists each nominal declaration, its field types, and the
ordered first-order leaves. For `Powers`, the leaves are `square` and
`doubled`, each an `m31` relation value of length four. Nested records use
path arrays such as `["nested", "value"]`; tuple positions are numeric path
segments. The report also gives the source SHA-256 and the SHA-256 of the
exact normalized relation JSON. The record, destructuring, and positional
versions all report normalized relation digest
`2c363f623e918c1f53d5988eabe29e4a074f6245505d28c8419cfa8f91b90467`.
This digest identifies the source-stage relation; the package's canonical IR
digest is a separate value computed after Zig lowering.

## A public record result

```s31
struct Pair { square: [m31; 1], again: [m31; 1] }
circuit pair(public x: [m31; 1]) -> public Pair {
    let square = x .* x;
    Pair { square: square, again: square }
}
```

For `x=7`, the relation has one `mul(x, x)` node and one distinct public
result wire, `square=49`. The two named result fields point to that same
wire. The proof binds two public words: input `x=7` and output `square=49`.
The v2 statement shows the alias explicitly:

| Layer | What it carries | Cost or check |
| --- | --- | --- |
| Arithmetic relation | `square = mul(x, x)` | One multiplication; no copy for `again` |
| Public ABI v2 | `Pair`, field order, and both field paths pointing to `square` | Hashed into the relation identity and sealed key |
| Typed statement | `x=7`, `square=49`, `again=49` | Verifier checks both alias claims agree |
| Proof word vector | `[7, 49, 0, 0, 0, 0, 0, 0]` | Two distinct public words |
| AIR | Direct-gate constraints for the same arithmetic graph as the flat form | Zero added arithmetic rows for record grouping |

```json
{"abi_sha256":"<digest of the validated layout>","leaves":[
  {"path":[{"root":"x"}],"words":[7]},
  {"path":[{"root":"result"},{"field":"square"}],"words":[49]},
  {"path":[{"root":"result"},{"field":"again"}],"words":[49]}
],"version":2}
```

The displayed JSON is line-broken for reading. An actual statement is one
canonical line with sorted keys and a final newline. The native verifier
rebuilds the paths from the sealed relation, checks the ABI digest in the
sealed key, and requires both `square` and `again` to claim `49`. Changing
either name or one aliased value rejects verification. The relation's `mul`
gate contributes the same AIR rows as a hand-flattened `x .* x` circuit;
record metadata changes the relation/key/statement bytes instead.

The [boundary implementation contract](../../../../design/s31/language/RECORD_PUBLIC_ABI_V2_IMPLEMENTATION.md)
and [canonical codec](../python/abi/binding_v2.py) specify tagged paths,
nominal layouts, alias checks, and the eight-word proof budget. The
[native acceptance control](../tests/acceptance/acceptance_public_record_v2.py)
compares AIR geometry with a flat relation and mutates field paths, aliases,
digest, JSON encoding, and M31 words.

## A record input and scalar result

The executable [record-input source](../examples/arithmetic/record_input_sum.s31)
and [typed assignment](../examples/arithmetic/record_input_sum.valid.json)
are:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit record_input_sum(public request: Pair, private mask: Pair) -> public [m31; 1] {
    request.left + request.right + mask.left + mask.right
}
```

For `request={left:[3], right:[4]}` and `mask={left:[5], right:[6]}`,
the result is `[18]` in M31. A strict typed prover assignment is:

```json
{"version":2,"public_inputs":{"request":{"left":[3],"right":[4]}},
 "private_inputs":{"mask":{"left":[5],"right":[6]}},"result":[18]}
```

The source grouping erases into four distinct first-order input wires. The
relation and sealed key bind each wire to its nominal root, tagged field
path, and visibility. The verifier's canonical statement contains three
leaves: `request.left=3`, `request.right=4`, and `result=18`. It has no
`mask` leaf. Its proof word vector has those same three values followed by
five zeros. The private mask values enter the circuit computation; absence
from the public statement does not make this transparent proof zero
knowledge.

For this scalar example, the arithmetic graph has three add nodes. Write
the four flattened inputs as $a,b,c,d$. Its witnesses $t_0,t_1,t_2$ must
satisfy $t_0-a-b=0$, $t_1-t_0-c=0$, and $t_2-t_1-d=0$ in M31. The public
result claim binds $t_2=18$. The named record paths select which existing
input wires supply $a,b,c,d$; they do not create another polynomial
constraint or a copy gate. A manually flattened circuit has the same
arithmetic equations and AIR geometry.

The [record-input native acceptance](../tests/acceptance/acceptance_record_inputs_v2.py)
uses a deeper nested record and tuple. It compares the exact direct-gate AIR
geometry with an equivalent manually flattened relation, proves both, and
checks that the native verifier rejects changed field paths and values. The
typed assignment adapter rejects missing or extra fields, wrong tuple arity,
duplicate JSON keys, and noncanonical M31 words before proving.
