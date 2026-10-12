# Optimized source bytes to direct AIR rows

[`OptimizedSourceAirRows.lean`](OptimizedSourceAirRows.lean) joins two existing
proofs that previously stopped at different layers:

1. `OptimizedTextBytes.checkBytes` accepts the exact source, normalized JSON,
   and compact canonical IR bytes. Its optimizer proof handles reversed
   operands and repeated add or pointwise multiply expressions.
2. `SSANativePolynomialRows` proves that local direct-Gate operation equations
   propagate one coherent packed four-lane M31 input through positional SSA.

The new `optimized_source_projected_air_sound` theorem uses the **same compact
certificate** in both layers. It assumes observed source cells equal
`expectedCells compact (compiledAddRows compact)`, that each such cell satisfies
its local polynomial relation on a coherent wire map, and that the existing
public input packing boundary holds. It concludes that the selected circuit
wire at address `22 + compact.output` is the packed result of the original
source spelling. `optimized_source_claim_sound` adds a selected output pin and
concludes the source result equals the claimed four-lane value.
`optimized_source_public_output_sound` derives that pin from the existing
eleven output mask, inverse, and copy rows plus four scalar public pins.

## By hand: reversed operands and one shared expression

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
  let a = x + x;
  let b = x .* x;
  let c = a + b;
  let d = b + a;
  d
}
```

For `x = [1, 2, 3, 4]`, `a = [2, 4, 6, 8]`,
`b = [1, 4, 9, 16]`, and `c = d = [3, 8, 15, 24]`.
Canonical operand ordering maps `d` to the already produced `c`. The
kernel-checked `reversed_and_repeated_compact_air_rows` theorem derives this
compact schedule:

| Source value | Circuit wire | Physical AIR row | Local polynomial | Selector `(add, pointwiseMul)` |
| --- | ---: | ---: | --- | --- |
| `a` | 23 | 3 | `a = x + x` | `(1, 0)` |
| `b` | 24 | 503 | `b = x .* x` | `(0, 1)` |
| `c` and `d` | 25 | 4 | `c = a + b` | `(1, 0)` |

Rows are physically grouped by operation, so row 503 precedes row 4 in source
evaluation order. The logical circuit addresses still follow the compact SSA
order. The last source `let` creates no separate circuit wire or AIR operation
row; its public output selects wire 25. The displayed equations abbreviate
the nine modeled QM31 residuals in `Qm31Ops.accepts`. `.*` means independent
M31 multiplication in each of the four packed coordinates.

## Boundary of this proof

The theorem does not show that production Zig emits these modeled cells for
every optimized source, that committed fixed columns match `observedCells`,
that Gate lookup authenticates the coherent wire values, or that PCS/FRI
authenticates an accepted proof. The optimized v3 package path also remains
opt in. These are separate correspondence and proof-system obligations.

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.OptimizedSourceAirRows
lake env leanchecker S31.Gadgets.Functional.Correspondence.OptimizedSourceAirRows
```
