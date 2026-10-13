# Full value evaluation for bounded record v2

The [previous value proof](GeneralRecordV2ValueCorrespondence.md) relates
source arithmetic nodes to typed nodes, but left input assignment alignment
and the final public claim as assumptions. This module supplies an executable
checker and a Lean theorem for those steps.

`checkSourceAssignment` takes an exact-source `Static` package and a typed
assignment. It reads each public or private singleton M31 input in source
declaration order. Then it checks:

1. The loaded typed input environment equals the source-ordered input words.
   Private input names and values are checked separately from public ones.
2. Node names are unique and fresh relative to the input environment.
3. The independent scalar source graph executes, and every record result
   selector resolves.
4. Each **distinct** normalized public output claim equals its scalar source
   value. The actual `claimedWords` decoder accepts the public inputs and
   output names, including its eight-word padding rule.

The checker does not call `Program.environment` or `Program.evaluate`.
`checked_source_assignment_evaluate` proves that when it returns a result,
the independently evaluated source record has exactly the returned ordered
field values **and** the actual normalized `Program.evaluate` returns exactly
the returned public claim words. This theorem quantifies over any `Static`
package admitted from exact source bytes and any assignment that passes these
checks. Failure remains a rejection; completeness for every syntactically
valid record assignment is not claimed.

For the two-field example from the prior file:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit combine(public visible: Pair, private secret: Pair) -> public Pair {
    let sum = visible.left + secret.left;
    let product = sum .* visible.right;
    Pair { left: product, right: sum }
}
```

With `visible=(2,3)` and `secret=(4,5)`, the source result is `(18,6)`.
The normalized claim is `[2,3,18,6,0,0,0,0]`. The private words `4,5`
affect the result but do not appear in the claim. If the second result field
also selects `product`, the source record becomes `(18,18)` while the
normalized output list contains `product` only once. Its claim is
`[2,3,18,0,0,0,0,0]`. The Lean examples check both forms, reject a swapped
private assignment, and reject an extra output name for the alias form.

This proof covers the bounded record-v2 source grammar's M31 add/mul value
semantics and its typed public claim. It does not establish that native AIR
cells match `Program.evaluate`, or that PCS/FRI authenticates those cells.
