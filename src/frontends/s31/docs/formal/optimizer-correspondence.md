# Pure-field optimizer correspondence

The native `inspect-optimizer` command checks a versioned slice of the
normalized S31 relation against the **actual canonical graph** that the
compiler uses. It accepts M31 inputs and straight-line `constant`,
`cast_m31`, `add`, `sub`, `mul`, `add_const`, and `mul_const` nodes. Other
operations return `UnsupportedOptimizerCorrespondenceFragment`; no receipt
is issued for them.

The checker independently replays six rules: constant arithmetic modulo
`p = 2,147,483,647`, commutative operand ordering for addition and
multiplication, identity aliases (`cast_m31`, `+ 0`, `× 1`), `× 0` folding,
and reuse of the first identical expression. It compares every emitted node,
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
command emits `s31-optimizer-correspondence-pure-field-v1` plus these counts.
Swapping ID 5's subtraction operands would give `10 - 11 = p - 1`; the
checker rejects that altered graph even though swapping ID 4's addition is
semantically harmless, because the canonical graph has a defined order.

The Lean module `Correspondence/Optimizer.lean` proves the listed local
rewrite rules preserve field values for **any** number of input names and
lanes, and that a checked source-name mapping preserves each mapped output.
The existing `CanonicalDagOptimization` theorem covers bounded add/mul CSE.
The Zig checker ties those semantic rules to actual native optimizer nodes.
It does not establish that native circuit gates, AIR columns, or PCS/FRI
verification implement the canonical graph; those are separate obligations.

The command is used at package construction or in an audit. It does not run
on each proof generation or native proof verification.
