# Effectful S31 source bytes to modeled AIR

This bridge starts with the actual ASCII bytes of a bounded `.s31` circuit
and the canonical JSON certificate emitted by the compiler. Lean lexes and
parses the source itself, constructs its indexed SSA graph, decodes the
certificate independently, and requires the graphs to be exactly equal.
The result is a theorem about the source that was parsed, including its
private inputs, constant arithmetic, and live assertions.

The checked production fixture is:

```s31
use std@1;
circuit affine_guard(public x: [m31; 3], private y: [m31; 3]) -> public [m31; 3] {
    let shifted = x + splat<3>(7_m31);
    let scaled = shifted .* splat<3>(9_m31);
    assert_eq(y, scaled);
    let out = y - x;
    out
}
```

The parser assigns `x=0`, `y=1`, `shifted=2`, `scaled=3`, and `out=4`.
It sees the assertion between `y` and `scaled`; both operands exist at
that point. The full certificate must contain the same input visibility,
names, ordered instructions, constants, assertion pair `(1,3)`, and output
ID 4. A source edit that reverses the final subtraction or removes the
assertion fails this comparison even if the package digests are rewritten.

Static bindings do not create an arithmetic row. For example, this equivalent
spelling still emits the same five wire IDs and three arithmetic nodes:

```s31
let bias = splat<3>(7_m31);
let input_copy = x;
let shifted = input_copy + bias;
let scaled = shifted .* splat<3>(9_m31);
let expected = scaled;
assert_eq(y, expected);
let out = y - input_copy;
let selected = out;
selected
```

Here `bias` is the static field constant 7, while `input_copy`, `expected`,
and `selected` are aliases. The parser resolves each name to its producer
before assigning an SSA ID. An assertion through `expected` still checks
the `scaled` row; returning `selected` still selects `out`. The production
source fragment and the Lean parser agree on this erasure for the bounded
syntax above.

For each lane `i=0,1,2`, the modeled rows and assertion require:

| Row or effect | Zero residual over M31 |
| --- | --- |
| `shifted` | `w₂[i] − x[i] − 7 = 0` |
| `scaled` | `w₃[i] − 9·w₂[i] = 0` |
| `assert_eq` | `y[i] − w₃[i] = 0` |
| `out` | `w₄[i] − y[i] + x[i] = 0` |
| public claim | `claimed[i] = w₄[i]` |

For `x=[1,2,3]`, the rows force `shifted=[8,9,10]` and
`scaled=[72,81,90]`. The assertion permits exactly
`y=[72,81,90]`, and then the claimed output is `[71,79,87]`.
If, say, `y[1]=82`, its assertion residual is `1`, so no accepted modeled
trace exists for that input. Packed rows may have an inactive fourth lane;
the theorem constrains the three active lanes.

`checked_source_air_sound` quantifies over **every** input assignment and
every complete modeled trace. Once the source/certificate checker accepts,
if all arithmetic rows, the final output selection, and every equality
assertion hold, the public claim satisfies the independently parsed source
meaning. The proof is not a finite test of the example values.

The source parser accepts one circuit, up to eight distinct and used static
helpers with one or two M31 array parameters and a single binary body, 1–4 distinct named inputs, 1–8
equal-length M31 lanes subject to the eight-word public ABI budget, up to
32 `let` statements including aliases and named constants, 1–16 binary or
constant arithmetic nodes, and up to 16 assertions. It accepts an
optional `use std@1;` line, canonical `splat<N>(k_m31)` values below the
M31 modulus, and a selected named or statically projected output. Flat
2–4 field tuples of existing M31 array wires are source-only values;
constant-index projection selects exactly one existing producer. The
`project_product_exact` theorem checks that local erasure, and the existing
exact-byte `Program.evaluate` theorem applies to any tuple source admitted
by this parser. Helper calls bind named wires, may reuse or reorder operands,
and introduce exactly one arithmetic SSA node each. The parser rejects
duplicate or unused helpers, calls with the wrong arity, grouped expressions,
scalar types, other operations, and non-ASCII syntax. It caps source at
16 KiB and certificate at 65 KiB.

For example, two calls share the same rule rather than requiring two
specialized proofs:

```s31
fn delta(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
fn square(v: [m31; 2]) -> [m31; 2] { v .* v }
circuit chain(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let d = delta(x, y); // SSA id 2, d = x - y
    let out = square(d); // SSA id 3, out = d * d lane by lane
    assert_eq(x, x);
    out
}
```

The normalized graph is `sub(0,1)` then `mul(2,2)`; the assertion reads
input id 0 twice. On `x=[5,6]`, `y=[2,4]`, the result is `[9,4]`. Every
accepted modeled row must satisfy `dᵢ−xᵢ+yᵢ=0` and
`outᵢ−dᵢ²=0` modulo 2³¹−1. The general byte-run theorem applies to any
helper chain accepted by the parser, within the same interpreter and AIR
premises as the rest of this fragment.

This theorem does **not** recompute SHA-256 or bind the spelling of the circuit
name by itself. `parseSourceName` exposes the name from the same validated
source bytes for the public ABI relation join. It does not prove that Zig emits
these modeled rows, establish native public-word
or private-witness pinning, or derive its row-satisfaction premise from a
Stwo PCS/FRI verifier result. Those remain distinct correspondence and
soundness obligations. In particular, a private input is an input to the
mathematical source relation here; the theorem does not assert that the
native proof keeps it hidden or binds it correctly.

Run the byte-level controls from `formal/s31`:

```sh
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes \
  s31-general-linear-effects-source-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsSourceBytes
python3 tests/audit/general_linear_effects_source_check.py
```

The source-byte controls admit five source/certificate pairs and reject fourteen mutations,
including bad field literals, a forward assertion, a duplicate assertion,
changed subtraction order, changed constants, a removed assertion, alias
forward references, and a 33rd let. A
separate accepted control replaces both digest fields with arbitrary valid
hex strings. It makes the Lean checker's digest boundary visible in CI;
the package verifier must reject that replacement before accepting a proof.
`tests/audit/multi_helper_effects_package.py` separately compares 16 generated
one-to-eight-helper programs with the production compiler and independent
Python parser, runs Lean's exact-byte statement checker on each, and rejects
re-sealed wrong relation and certificate bytes. This is differential evidence,
not a Python/Lean parser equivalence theorem.
