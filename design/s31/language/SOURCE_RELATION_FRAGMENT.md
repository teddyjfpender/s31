# Bounded source-to-relation fragment

Status: independently replayed, production-emitted package certificate for
the **`source-to-relation-only`** boundary. It is not a proof that the
generated circuit/AIR implements the source.
The existing public-only [direct-gate certificate](DIRECT_GATE_CORRESPONDENCE_CERTIFICATE.md)
remains the separate source-to-native-row package-admission path.

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

For a conservatively compiled text package in this accepted grammar, the builder now emits
`source-relation-certificate.json`. Package verification reparses the source
bytes independently, compares the *entire* normalized relation, and
reconstructs the exact certificate. The artifact has `schema`, `capability`,
source/relation SHA-256 identities and an indexed `ssa` object. Every input
and node has a stable integer ID. Its node operands and assertion pairs use
those IDs, and `output` names the returned ID. For this example, the relevant
SSA projection is:

```json
{
  "lane_count": 4,
  "inputs": [{"id": 0, "name": "x", "visibility": "public"},
             {"id": 1, "name": "y", "visibility": "private"}],
  "nodes": [
    {"id": 2, "name": "twice", "op": "add", "lhs": 0, "rhs": 0},
    {"id": 3, "name": "product", "op": "mul", "lhs": 1, "rhs": 0},
    {"id": 4, "name": "result", "op": "add_const", "lhs": 3, "constant": 7}
  ],
  "assertions": [[1, 2]],
  "output": 4
}
```

This certificate records `lean_semantic_profile:
"linear-ssa-m31-effects-v1"` and `unmodeled_features: []`. That profile
includes `add_const`, `mul_const`, and equality assertions, so the source
meaning is a partial relation: an accepted witness must satisfy every
assertion. A program with only add/sub/mul nodes and no assertions keeps
the pure `linear-ssa-m31-v1` profile. The profile marks which Lean semantic
checker can apply; SHA-256 digests alone do not prove parser correctness.
The [five-lane fixture](../../../formal/s31/fixtures/correspondence/source_relation_ssa_v1.json)
has exact source and normalized-relation siblings. A test regenerates all
three identities and the complete certificate; the Lean checker can parse
the same serialized bytes. The Lean runtime gate requires the canonical JSON
serialization and a handwritten source term for this fixture. The pure Lean
theorem checks the emitted indexed add/sub/mul graph against that supplied
term and proves its modeled packed AIR rows compute the term for every lane
assignment and every accepted witness. The effects profile uses a separate
Lean checker for constants and assertions; its accepted-witness statement
requires the modeled row and assertion constraints. The package's independent
Python parser remains the trusted source-byte admission step.

The checker also accepts this bounded functional spelling:

```s31
fn difference(x: [m31; 5], y: [m31; 5]) -> [m31; 5] { x - y }
circuit subtract5(private a: [m31; 5], private b: [m31; 5]) -> public [m31; 5] {
    let out = difference(a, b);
    out
}
```

It independently resolves the helper's two parameters and emits exactly one
`sub` relation node with `lhs = a` and `rhs = b`. Reversing the helper body to
`y - x` reverses those operands. Both forms use two packed native subtraction
rows for five active lanes; this checker establishes the text-to-relation
mapping, while the separate Lean packed-row proof and native trial address
the local AIR relation and one generated proof.

## Exact accepted syntax

One circuit declaration with one to four equal-length `[m31; N]` inputs for
`1 ≤ N ≤ 8`, each marked `public` or `private`, a public `[m31; N]` result,
up to 32 `let` statements,
up to 16 arithmetic nodes, up to 16 `assert_eq(name, name);` statements, and
one returned wire name. The sum of all public input and output words must be
at most eight. The body must contain at least
one arithmetic node. A let right hand side may be an earlier name,
`splat<N>(C_m31)` with `0 ≤ C < 2³¹−1` and canonical decimal spelling, or one
`+`, `-`, or `.*` operation over two such atoms. A dynamic value minus a
constant becomes one `add_const` node with the canonical negated constant.
Constant-left subtraction is outside this fragment. For addition and
multiplication, constants may occur on either side; both operands cannot be
constants. Parentheses may wrap
atoms or whole let expressions; assertion operands and the returned wire are
plain names. Whitespace and `//` to end-of-line comments are
ignored. The lexer bounds input at 16,384 bytes and 512 tokens. Identifiers
are ASCII and at most 128 characters.

Up to eight preceding `fn` declarations may each take one or two distinct
`[m31; N]` parameters and return `[m31; N]`. Each pure body must apply one
`+`, `-`, or `.*` to its parameters. One or more lets may call a helper with
the corresponding number of previously named wires; the checker substitutes those wires in the declared
operand order and compares the exact residual relation. Each helper must be
used, and circuit/input/local names may not shadow a helper. Function values,
captures, recursion, nested helper calls, and effects are outside this bounded
grammar.

A leading `use std@1;` is accepted as version-pinned source metadata. The
accepted expression grammar cannot call a standard-library function, so the
import adds no relation operation here; package verification checks the
separate standard-library lock.

The checker rejects imports, nested binary expressions, array
indexing, other types, calls other than the exact `splat<N>` atom or declared
bounded helper, undeclared
names, duplicate local/input names, repeated assertions, noncanonical M31 literals, trailing
source tokens, duplicate JSON keys, extra relation fields, JSON booleans or
floating-point numbers in integer fields, and noncanonical JSON
serialization. The finite grammar is intentional: a new frontend
feature cannot silently expand this capability.

## API, independent evidence, and limits

`package.source_relation_fragment.check_source_relation(source_bytes,
relation_bytes)` returns exact source/relation SHA-256 digests and the
`source-to-relation-only` capability after a full structural comparison.
`make_source_relation_certificate` builds the indexed artifact, and
`check_source_relation_certificate` reproduces and compares it from raw bytes.
All conservative text packages whose source is inside this grammar must carry
that artifact; a missing, extra, or re-sealed but false artifact is rejected
by ordinary package verification. Other source programs remain outside this
certificate and do not silently gain its status. The explicit optimized
direct-gate mode has its own correspondence certificate and does not claim
this conservative translation.
`check_package_source_relation(package_path)` additionally compares the
direct-gate public ABI, including the exact `[m31; N]` word count, and relevant
package manifest identities and artifact
hashes, including source and relation bytes. It does **not** authenticate a
publisher: a forger can recompute these hashes. The independent structural
check is why a re-sealed wrong operation, constant, assertion, visibility, or
order still fails.

The production compiler is imported only in differential **tests**, not in
the checker. The tests compare honest source lowering and mutate complete
relation/ABI/manifest test fixtures with all affected hashes recomputed.
Passing this check alone does not validate the compiler's optimizer, circuit
row schedule, private-input gate allocation, public input binding inside the
native verifier, AIR constraints, lookup closure, or PCS/FRI soundness. For
one-public-input, pure 1–3 lane direct-Gate packages, the separate
`pure-native-rows-certificate.json` adds exact fixed-row admission as described
in the general correspondence matrix. It does not promote private circuits
to that profile. A formal theorem and independent checks of the remaining
boundaries are open.
