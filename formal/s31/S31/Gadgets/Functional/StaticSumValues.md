# Static sum and match correspondence

The typed Lean source core now has `Ty.sum`, `Expr.inl`, `Expr.inr`, and
`Expr.matchSum`. A sum carries a constructor tag during source evaluation and
specialization. The `Related` relation requires the source and specialized
tags to agree; `specialize_correct` proves this for every typed expression,
including free variables, closures, and nested matches. The residual field
polynomial and the straight-line graph have no sum operation.

For the modeled circuit:

```s31
enum Choice { Square: [m31; 4], Double: [m31; 4] }

circuit selected(public x: [m31; 4]) -> public [m31; 4] {
  let choice = Choice::Square(x);
  match choice {
    Choice::Square(y) => y .* y,
    Choice::Double(y) => y + y,
  }
}
```

`matchedSquare4` represents the source expression after nominal names are
resolved. Its tag is statically `Square`, while its payload is the arbitrary
four-word input. Specialization selects `y .* y` and emits exactly this graph:

```text
input wires: x₀=0  x₁=1  x₂=2  x₃=3
gate 4: x₀ × x₀
gate 5: x₁ × x₁
gate 6: x₂ × x₂
gate 7: x₃ × x₃
outputs: [4, 5, 6, 7]
```

`matched_square4_same_graph` proves equality with the direct square graph;
`matched_square4_graph_shape` proves the four gate IDs above. The inactive
`Double` body contributes no gate. `matched_square4_graph_iff_air` uses the
existing four-lane local AIR correspondence to prove that arbitrary satisfying
graph witnesses and packed multiplication rows agree on the claim.
`matched_square4_rejects_forged` rules out a changed result under those local
constraints.

The total Lean core does not model partial library calls or the Python
effect checker. A separate `Except` model proves that a failing constructor
payload propagates its error and that a failure in the inactive arm is ignored.
The `selectedEffect` model then composes a known static tag with the dynamic
conditional effect theorem: if the selected arm and the other dynamic branch
are total, the strict graph and selector accept exactly the lazy result,
regardless of the unselected enum arm. Selecting an inverse-of-zero arm
instead has no eager witness even when the dynamic bit chooses the other
branch. These theorems justify the staging rule; they do not verify the
production Python effect pass or native verifier.
The frontend must still check both arm types, account for effects and reject
witness-dependent sum tags when a static branch is needed.
The theorem also does not establish that Python emits this graph, that Zig
installs the expected AIR, or that a native STARK proof authenticates its rows.

Check the module with:

```sh
cd formal/s31
lake build S31.Gadgets.Functional.StaticSumValues
lake env leanchecker S31.Gadgets.Functional.StaticSumValues
```
