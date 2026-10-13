# Static tuple erasure in the checked M31 fragment

Status: bounded compiler correspondence. The exact source bytes, complete
normalized relation, canonical certificate, public ABI, and the normalized
`Program.evaluate` semantics are checked for the grammar below. Native Gate
cost equality is tested against an equivalent scalar program. The native AIR
row/authentication and PCS/FRI theorems are separate open obligations.

## Handwritten program

```s31
circuit tuple_case(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let p = (x, y);
    let out = p.0 + p.1;
    out
}
```

`p` is a source-only pair. Its type is `([m31; 2], [m31; 2])` and its value is
the two existing circuit references `x` and `y`. `p.0` means exactly `x` and
`p.1` means exactly `y`. There is no prover-supplied tuple tag or index.
The independent checker assigns input IDs `x=0`, `y=1`, and the sole computed
wire `out=2`. Its complete normalized relation is:

```json
{
  "version": 1,
  "name": "tuple_case",
  "inputs": [
    {"name": "x", "kind": "m31", "length": 2, "visibility": "public"},
    {"name": "y", "kind": "m31", "length": 2, "visibility": "private"}
  ],
  "nodes": [{"name": "out", "op": "add", "lhs": "x", "rhs": "y"}],
  "assertions": [],
  "public_outputs": ["out"]
}
```

The certificate contains the indexed SSA node `out := add 0 1` and selects
the `linear-ssa-m31-effects-v1` profile. That profile is used even without
assertions because its independent Lean byte parser understands tuple syntax.
The pure-profile parser has a narrower source grammar.

For `x=[1,2]` and `y=[3,4]`, the witness must have `out=[4,6]` in M31. The
one arithmetic constraint for each active lane is

\[
  w_{\mathrm{out}}[i] - w_x[i] - w_y[i] = 0,\quad i\in\{0,1\}.
\]

The public statement contains `x` and `out`; `y` remains a private input to
the source relation. The tuple itself contributes no public ABI word and no
Gate row. The exact-byte Lean check reconstructs the producer IDs from the
source, matches the certificate and relation, then runs the actual normalized
interpreter on a typed assignment. `project_product_exact` proves the local
index selection rule; `checked_example_program_evaluate` applies the generic
byte-run theorem to the written program. The checker sees the supplied
private assignment, so this audit does not provide private-witness secrecy.
The native proof is not bound to that particular assignment by this theorem.

## Measured native equality

The live acceptance script builds the program above and the scalar spelling
`let out = x + y; out` with the same direct-Gate lowering. It checks exact
normalized relation byte equality and equality of the **entire** native cost
report, then checks Lean static/assignment admission, a changed-projection
rejection, and both native proofs. In the local run on 2026-10-13, both
packages had 288 raw `qm31_ops` rows and 56,140-byte accepted proofs. These
numbers depend on the pinned engine and build options; the script recomputes
them rather than treating the recorded values as a security guarantee.

```sh
cd formal/s31 && lake build s31-general-linear-effects-package-check && cd ../..
python3 -B src/frontends/s31/tests/acceptance/compiler_correspondence/static_tuple_erasure.py
```

## Exact admitted grammar and gaps

The independently checked product consists of 2–4 existing equal-length M31
array wires. A field is a direct earlier wire name or a projection from an
earlier product. A product may be named, aliased, and projected with a
canonical decimal index `.0` through `.3` within bounds. The source parser
checks construction, projection, and arithmetic operand types before
lowering. Projection through assertions and the result is also admitted.
There must still be at least one arithmetic node, and all existing input,
lane, token, source-byte, node, assertion, and eight-word ABI limits apply.

Nested products, dynamic indices, tuple-valued results, grouped tuple
expressions, and static helpers combined with products are rejected by this
profile. Records have a separate bounded v2 source checker and do not inherit
this tuple-to-interpreter theorem. The source-byte parsers are independent
implementations, but a full proof that the production parser agrees on every
accepted or rejected program is still open. The native row comparison is a
live differential test, not a universal native AIR refinement theorem.
