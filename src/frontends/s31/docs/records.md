# Nominal records: names for values, zero proof work for grouping

S31's `struct` is a **static record type**. It gives names to fields that
already hold circuit values. The frontend checks the names and types, then
specialization removes the record before the normalized relation is built.
No record object, field label, record row, or record polynomial reaches the
prover or native verifier.

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
`let` bindings. Circuit parameters and the public result still have the
existing first-order ABI. To prove a statement about several fields, declare
the first-order inputs and output, group them into a record inside the
circuit, then assert or return the required first-order fields. Whole-record
`if` and `assert_eq` are not part of this version; select or assert the
individual circuit fields explicitly.

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
models named construction and projection as typed product operations and
proves specialization has the same residual polynomial as the direct
three-operation program. The executable source-to-source comparison checks
the current Python compiler erases the example to the same normalized
relation as a tuple. Native verification checks the resulting proof and
changed-public-statement rejection. As with the rest of S31, a machine-checked
refinement of the entire Python parser and Zig AIR emitter remains open.

Run `s31 lower`, `s31 explain`, and `s31 equations` on the source to inspect
the exact normalized nodes, gate spans, AIR geometry, and source positions.
The [source-to-AIR guide](reference/LANGUAGE_AND_AIR.md) explains how the
generic circuit gates become AIR constraints and trace polynomials.
