# Why dead source work can disappear from the AIR

For source-only enum choices and static powers, S31 evaluates expressions
eagerly, then removes an unused computation only when it is a reviewed,
total field operation. The text compiler checks
every changed relation with an independent pruning certificate before the
relation reaches Zig. This check runs during compilation and adds no circuit
node or AIR row.

Consider this source program:

```s31
enum Choice { Left: [m31; 1], Right: [m31; 1] }

circuit twice(private x: [m31; 1]) -> public [m31; 1] {
    let unused = Choice::Left(x .* x);
    let answer = x + x;
    answer
}
```

The source evaluator creates these nodes in order:

| ID | Node | Reads | Kept? | Reason |
| --- | --- | --- | --- | --- |
| `_s31_0` | `mul(x, x)` inside `unused` | `x` | No | Total and not observed |
| `answer` | `add(x, x)` | `x` | Yes | Public result |

The AIR contains the `add` relation for `answer`; it does not allocate a
multiply relation for `unused`. At `x = 3`, the prover supplies a value of
`6` for `answer`, and the verifier checks the addition constraint against
the public result `6`.

The certificate checker compares the complete relation before and after
pruning. It requires:

1. Inputs, public outputs, assertions, public ABI, and every other non-node
   relation field to be identical.
2. The retained nodes to be an exact, ordered subsequence. Their operations,
   operands, constants, and names cannot change.
3. Each removed node to have the exact reviewed shape of a total field
   constant, add, subtract, or multiply operation.
4. Every retained node to read only an input or an earlier retained node.
   Public outputs, assertion operands, and public ABI leaves must still name
   retained wires or inputs.
5. Source locations to correspond exactly to the retained nodes.

For contrast, an unused `std::math::inv(x)` remains in the relation. Inverse
is partial: when `x = 0`, the original program has no valid witness. Erasing
that node would make a previously unprovable input provable. The certificate
therefore rejects a candidate relation that drops it, even when the public
result does not read the inverse.

The [Lean conservative dead-code model](../../../../../formal/s31/S31/Gadgets/Functional/Correspondence/ConservativeDeadCode.md)
proves that any retained-node mask satisfying these root and dependency
conditions preserves modeled values and failures. The Python checker is an
executable guard over the emitted JSON relation; it is not itself a Lean proof
of the parser, the checker implementation, Zig lowering, or STARK soundness.
