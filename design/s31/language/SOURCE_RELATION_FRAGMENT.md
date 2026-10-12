# Bounded source-to-relation fragment

Status: executable independent Python check, **`source-to-relation-only`**.
This is a development and audit capability, not a package-admission
certificate or a proof that the generated circuit/AIR implements the source.
The existing public-only [direct-gate certificate](DIRECT_GATE_CORRESPONDENCE_CERTIFICATE.md)
remains the separate package-admission path.

## Example and claim

```s31
circuit checked(public x: [m31; 4], private y: [m31; 4]) -> public [m31; 4] {
    let bias = splat<4>(7_m31);
    let twice = x + x;
    assert_eq(y, twice);
    let product = y .* x;
    let result = product + bias;
    result
}
```

For every canonical four-lane assignment, the source meaning is:

* `twice[i] = x[i] + x[i] (mod 2³¹ − 1)`;
* the assertion requires `y[i] = twice[i]` for each lane;
* `product[i] = y[i] × x[i] (mod 2³¹ − 1)`;
* the public result is `product[i] + 7 (mod 2³¹ − 1)`.

The checker independently reads the exact UTF-8 text bytes and requires the
normalized relation to contain precisely these ordered inputs, arithmetic
nodes, assertion, and output:

```json
{
  "assertions": [{"lhs": "y", "rhs": "twice"}],
  "inputs": [
    {"kind": "m31", "length": 4, "name": "x", "visibility": "public"},
    {"kind": "m31", "length": 4, "name": "y", "visibility": "private"}
  ],
  "name": "checked",
  "nodes": [
    {"lhs": "x", "name": "twice", "op": "add", "rhs": "x"},
    {"lhs": "y", "name": "product", "op": "mul", "rhs": "x"},
    {"constant": 7, "lhs": "product", "name": "result", "op": "add_const"}
  ],
  "public_outputs": ["result"],
  "version": 1
}
```

The static `bias` binding emits no relation node. Alias bindings similarly
refer to their producer's original name. The output ABI has one public input
vector `x` followed by one public output vector `result`, each of four
canonical M31 words. The private `y` is absent from the public ABI.

## Exact accepted syntax

One circuit declaration with one to four `[m31; 4]` inputs, each marked
`public` or `private`, a public `[m31; 4]` result, up to 32 `let` statements,
up to 16 arithmetic nodes, up to 16 `assert_eq(name, name);` statements, and
one returned wire name. At most one input may be public, because the result
uses four of the eight available public words. The body must contain at least
one arithmetic node. A let right hand side may be an earlier name,
`splat<4>(N_m31)` with `0 ≤ N < 2³¹−1` and canonical decimal spelling, or one
`+` / `.*` operation over two such atoms. Constants may occur on either side
of an operation; both operands cannot be constants. Parentheses may wrap
atoms or whole let expressions; assertion operands and the returned wire are
plain names. Whitespace and `//` to end-of-line comments are
ignored. The lexer bounds input at 16,384 bytes and 512 tokens. Identifiers
are ASCII and at most 128 characters.

The checker rejects functions, imports, nested binary expressions, array
indexing, other types, calls other than the exact `splat<4>` atom, undeclared
names, duplicate local/input names, repeated assertions, noncanonical M31 literals, trailing
source tokens, duplicate JSON keys, extra relation fields, JSON booleans or
floating-point numbers in integer fields, and noncanonical JSON
serialization. The finite grammar is intentional: a new frontend
feature cannot silently expand this capability.

## API, independent evidence, and limits

`package.source_relation_fragment.check_source_relation(source_bytes,
relation_bytes)` returns exact source/relation SHA-256 digests and the
`source-to-relation-only` capability after a full structural comparison.
`check_package_source_relation(package_path)` additionally compares the
direct-gate public ABI and relevant package manifest identities and artifact
hashes, including source and relation bytes. It does **not** authenticate a
publisher: a forger can recompute these hashes. The independent structural
check is why a re-sealed wrong operation, constant, assertion, visibility, or
order still fails.

The production compiler is imported only in differential **tests**, not in
the checker. The tests compare honest source lowering and mutate complete
relation/ABI/manifest test fixtures with all affected hashes recomputed.
Passing this check does not validate the compiler's optimizer, circuit row
schedule, private-input gate allocation, public input binding inside the
native verifier, AIR constraints, lookup closure, or PCS/FRI soundness. It is
not wired into `verify-release` and does not promote private circuits to the
existing direct-gate certificate. A formal theorem and independent checks of
those later boundaries remain open.
