# Functional language proofs

These modules connect the intrinsically typed [source core](../../Semantics/Functional.lean)
to strict field graphs and selected executable normalized relation nodes.
Lean module names follow the directory, for example
`S31.Gadgets.Functional.ArrayNodes`; theorem names remain in
`S31.Functional`.

| Module | Proof boundary |
| --- | --- |
| `Graph.lean` | Residual field polynomial emission, valid wires, strict graph soundness and completeness. |
| `Outputs.lean` | One graph binds every claimed field output, including aliases. |
| `Arrays.lean` | Shape-indexed arrays and every output lane in a strict graph. |
| `ArithmeticNodes.lean` | Pointwise array `add`/`mul` agree with concrete normalized evaluator nodes. |
| `ArrayNodes.lean` | `get`, `concat`, `take` and `drop` agree with normalized array nodes and bounds. |
| `Assertions.lean` | Source equality assertions checked against independently witnessed graph outputs. |
| `Conditional.lean` | Total scalar branches share a graph and a bit-constrained selector. |
| `ArrayConditional.lean` | Total array branches share a graph; the selected value agrees with a normalized `select` node. |
| `Effects.lean` | A conservative totality rule and the inactive partial-branch counterexample. |

The dependency order starts with `Graph`, then `Outputs`, then `Arrays`.
Arithmetic and array-node bridges depend on `Arrays`; conditionals depend on
`Outputs` or `Arrays`. `Effects` builds on scalar conditionals. The package
entry point `S31.Gadgets` imports every module, so the theorem inventory,
axiom audit and kernel replay include all of them.

These are proofs about a formal typed source core, strict graph constraints,
and concrete normalized evaluator nodes. The Python parser and specializer,
production Zig AIR generation, STARK soundness and zero knowledge are separate
obligations. The [package README](../../../README.md) records the current
evidence and exact audit commands.
