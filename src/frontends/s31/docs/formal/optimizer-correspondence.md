# Pure-field optimizer correspondence

The native `inspect-optimizer` command checks a versioned slice of the
normalized S31 relation against the **actual canonical graph** that the
compiler uses. It accepts M31 inputs and straight-line `constant`,
`cast_m31`, `add`, `sub`, `mul`, `add_const`, `mul_const`, `inv`, scalar
`is_zero`, and `select` nodes in a transparent version 1 relation. Other
operations return `UnsupportedOptimizerCorrespondenceFragment`; no receipt
is issued for them.

The checker independently replays six rules: constant arithmetic modulo
`p = 2,147,483,647`, commutative operand ordering for addition and
multiplication, identity aliases (`cast_m31`, `+ 0`, `× 1`), `× 0` folding,
scalar constant zero tests, and reuse of the first identical expression. It
includes the selector ID in CSE keys and compares every emitted node,
source-name ID, assertion, and public output. Subtraction retains its operand
order. It returns an error if even one edge or folded constant differs.

For example, consider these normalized scalar nodes (the same arithmetic
runs independently on each lane of an M31 array):

```text
private x = 9, y = 2
seven = constant(7)
ten   = add_const(seven, 3)
sum   = add(x, y)
same  = add(y, x)
diff  = sub(sum, ten)
again = mul_const(diff, 1)
zero  = mul_const(again, 0)
assert sum == same
public diff, zero
```

The canonical nodes are:

| ID | Node | Value at the shown input |
|---:|---|---:|
| 0 | input `x` | 9 |
| 1 | input `y` | 2 |
| 2 | constant `7` | 7 |
| 3 | constant `10` | 10 |
| 4 | add `(0, 1)` | 11 |
| 5 | sub `(4, 3)` | 1 |
| 6 | constant `0` | 0 |

`same` maps to ID 4 and `again` maps to ID 5. Thus seven source nodes
produce five canonical nodes after the two inputs, with two aliases. The
command emits `s31-optimizer-correspondence-pure-field-v2` plus these counts.
Swapping ID 5's subtraction operands would give `10 - 11 = p - 1`; the
checker rejects that altered graph even though swapping ID 4's addition is
semantically harmless, because the canonical graph has a defined order.

The byte-checked source fragment now overlaps this optimizer profile. For
example, the checked-in integration test builds this text program:

```s31
use std@1;
circuit optimizer_control(public x: [m31; 1], private a: [m31; 4],
                          private b: [m31; 4]) -> public [m31; 4] {
    let square = a .* a;
    let z = std::field::is_zero(x);
    let picked = std::field::select(z, square, b);
    let result = std::math::inv(picked);
    result
}
```

The independent byte derivation checks exact source bytes against the
normalized nodes `mul(a,a)`, `is_zero(x)`, `select(z,square,b)`, and
`inv(picked)`. The native optimizer checker independently rebuilds their
canonical IDs, including `picked`'s selector ID, then recomputes the
selector-aware IR digest. The Lean control model calls the same partial
normalized operation semantics as the byte-derivation theorem, including
inverse failure at zero and rejection of non-Boolean selectors. The
package test sends the *same sealed source and normalized relation* through
both checks. It also changes the receipt IR digest while updating its
manifest artifact hash; package admission rejects the mismatch.

The Lean module `Correspondence/Optimizer.lean` proves the listed arithmetic
rewrite rules preserve field values for **any** number of input names and
lanes, and that a checked source-name mapping preserves each mapped output.
Its control model shares `PureFieldDerivation`'s partial normalized operation
semantics and proves scalar zero-test folding. Lean does not prove the native
optimizer's complete DAG rewrite or source-map implementation.
The existing `CanonicalDagOptimization` theorem covers bounded add/mul CSE.
The Zig checker ties those semantic rules to actual native optimizer nodes.
It does not establish that native circuit gates, AIR columns, or PCS/FRI
verification implement the canonical graph; those are separate obligations.

For admitted new packages, the build runs this command once and stores
`optimizer-correspondence.json`. The receipt contains the exact normalized
source SHA-256 and a SHA-256 recomputed by the checker from its verified
legacy or selector-aware canonical IR serialization. Package admission compares those values
with the source artifact, manifest and verification key. Existing packages
without this opt-in receipt remain readable. Existing v1 receipts remain
admissible only for the old arithmetic fragment; v2 covers control nodes.
Absence of the receipt is not a
claim that the optimizer was audited. The checker does not run on each proof
generation or native proof verification.
