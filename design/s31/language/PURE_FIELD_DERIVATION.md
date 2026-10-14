# Compositional pure-field source derivation

`pure-field-derivation.json` is a versioned, replayed source-to-normalized-
relation certificate. Its claim is narrow: a parser independent of production
lowering reads the exact `.s31` bytes, types every named let in order, resolves aliases, and
reconstructs the **entire** normalized relation. The package verifier reruns
the derivation and compares every certificate field. It is available on
conservative text packages when the source fits this fragment.
The verifier also replays the certificate's typed steps as a separate pass,
without reading source tokens, and reconstructs the normalized relation from
that rule list. Both passes must agree on every node and output.

The Python checker reuses the existing independent `source_relation_fragment` lexer
and the strict JSON shape comparator from `package.correspondence`; those
shared Python helpers are part of the executable checker boundary. It does
not call the production `compile_text` parser or normalizer.

## The admitted source language

The fragment accepts 1–8 M31 inputs, each `[m31; 1]` through `[m31; 8]`,
public or private. Public inputs plus the public output must fit the eight-word
v1 ABI. It has at most 64 straight-line `let` statements and 64 emitted nodes.
The only expressions are a prior name, `a + b`, `a - b`, `a .* b`,
`std::math::inv(a)`, `std::field::is_zero(a)`, and `select(bit, a, b)` (also
`std::field::select`). `inv` and `is_zero` require `use std@1;`.

Every binary operation needs equal M31 array shapes. `is_zero` needs one M31
word and produces a bit. A select's selector must come from an earlier zero
test or its alias; its two M31 arms must have the same length. The result is
an M31 array. This source certificate currently requires at least one
`inv`, `is_zero`, or `select`, because the existing linear SSA certificate
already covers plain arithmetic. Calls with nested expressions, field
constants, assertion effects, public bit inputs, and a repeated inverse of the
same wire are outside this profile. The production builder shares a repeated
inverse, which needs a separate optimization rule.

For example:

```s31
use std@1;
circuit choose(public x: [m31; 1], private a: [m31; 4],
               private b: [m31; 4]) -> public [m31; 4] {
    let squared = a .* a;
    let zero = std::field::is_zero(x);
    let selected = select(zero, squared, b);
    let result = std::math::inv(selected);
    result
}
```

The derivation rules run left to right:

| Source let | Rule and typed operands | Normalized node | Source meaning |
| --- | --- | --- | --- |
| `squared` | `mul(a[4], a[4])` | `mul(a, a)` | Four field squares. |
| `zero` | `is_zero(x[1])` | `is_zero(x)` | One constrained bit: 1 iff `x=0`. |
| `selected` | `select(zero[bit], squared[4], b[4])` | `select(squared, b, selector=zero)` | `squared` if 0, `b` if 1. |
| `result` | `inv(selected[4])` | `inv(selected)` | Per-lane inverse; a zero lane makes evaluation fail. |

An alias let records an `alias` rule and emits **no** relation node. For each
emitting let, the certificate records the source operand names, resolved wire
names, result kind and length, and its positional node index. The checker
compares the derived input declarations, ordered nodes, assertions, and output
with the normalized relation JSON. It also binds exact source and relation
bytes by SHA-256 and requires canonical JSON encoding.

## What the Lean theorem says

[`PureFieldDerivation.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/PureFieldDerivation.lean)
defines source rules and normalized rules with separate evaluators. Inversion
fails on any zero lane; selection accepts only a scalar 0 or 1 selector;
`is_zero` produces exactly one Boolean word. `lower_rule_eval` proves each
emitting rule keeps its partial value. `lower_run` proves by induction that
**any list** of those rules has the same final state or the same failure after
lowering. Source aliases are resolved by the executable checker before this
Lean sequence is formed.
`lower_output` carries that result to the selected public output.

[`PureFieldDerivationBytes.lean`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/PureFieldDerivationBytes.lean)
now lexes the exact `.s31` bytes independently in Lean. It constructs every
typed rule and the complete normalized relation, separately replays all rules
from the certificate JSON, and compares both with the canonical relation JSON.
`checked_bytes_lower_output` connects those checked bytes to `lower_output`
for every initial field state. The associated CLI rejects malformed source,
typed rules, noncanonical or duplicate-key JSON, and wrong relation nodes.

The Lean byte lexer deliberately accepts a **conservative ASCII subset** of
the Python source lexer: ASCII code, six ASCII whitespace bytes, and `//`
comments containing ASCII only. This is fail-closed for non-ASCII comments,
even if Python admits them. The Lean checker bounds source to 16,384 bytes,
512 tokens, 8 inputs, 64 lets/nodes, certificate JSON to 131,072 bytes, and
relation JSON to 65,536 bytes. The package verifier owns SHA-256 byte binding;
Lean checks digest spelling but does not compute the digests. The ordinary
package verifier currently runs its Python derivation checker, while the Lean
CLI is a separate auditable gate.

This theorem composes semantic rules and independently admitted bytes. It does
not prove the production optimizer preserves
the normalized relation, that native AIR rows implement every node, or that
the proof verifier authenticates those rows through PCS/FRI. The separate
scalar [`is_zero` row certificate](SCALAR_ZERO_TEST_CORRESPONDENCE.md) supplies
a local native fixed-row check for one small program, not for this general
compositional class.

Run the focused checks:

```sh
PYTHONPATH=src/frontends/s31/python python3 -B -m unittest \
  src.frontends.s31.tests.python.security.test_pure_field_derivation -q
cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.PureFieldDerivation
cd ../.. && python3 scripts/formal/check_pure_field_lean_bytes.py
```
