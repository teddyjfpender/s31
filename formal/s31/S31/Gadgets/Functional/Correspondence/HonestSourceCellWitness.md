# Honest source-cell witness

`HonestSourceCellWitness.lean` proves a constructive result for **every**
byte-admitted bounded direct-Gate program and **every** four-lane M31 input.
It also covers canonical alias programs, where aliases and redundant
parentheses erase to the same producer graph. The source grammar admits up to
16 additions or pointwise multiplications.

Given exact source and normalized bytes accepted by `checkRelation`, the
theorem `checked_direct_source_cells_satisfiable` constructs:

1. A final SSA value array computed by the checked interpreter.
2. One `wireOfFinal` function assigning a packed QM31 value to every native
   source wire address `22 + id`.
3. A value for the selected output equal to the parsed source denotation.

For every instruction, the theorem locates its cell in the source-derived
`expectedCells` roster at `compiledAddRows certificate`, checks its exact
opcode selector and operand/output addresses, and proves that the selected
add or pointwise-multiply arithmetic polynomial accepts the three values
from **the same wire function**. Earlier wire values stay fixed because the
interpreter only appends new outputs. This also covers dead source rows: the
arithmetic equation is satisfied even when their output multiplicity is zero.
The companion theorem `checked_canonical_alias_source_cells_satisfiable`
proves the identical property from accepted source, normalized, and canonical
IR bytes for the alias grammar.

For example, the accepted program

```s31
circuit Square(public x: [m31; 4]) -> public [m31; 4] {
  let y = x .* x;
  y
}
```

has source wire 0 at address 22 and wire 1 at address 23. For input
`[0, 1, 2, 7]`, the constructed wire assignment is
`22 ↦ [0, 1, 2, 7]` and `23 ↦ [0, 1, 4, 49]`. Its source cell selects
pointwise multiplication with input addresses `(22, 22)` and output
address `23`; its local arithmetic equation holds lane by lane. The general
proof works for any accepted instruction chain and any input, without a
finite test corpus or a caller-supplied wire map.

This is a **source-cell circuit witness**, not yet a complete 512-row
physical AIR trace. The source-independent constant, basis, packing, public
copy and padding rows are not constructed here. Their fixed/main cell values,
Gate use/yield multiset balance, interaction columns, and proof-system
authentication remain separate. The concrete `PinnedNativeSquare4Witness`
checks one full physical base trace and ideal Gate balance; a general
full-trace existence theorem is still open.

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.HonestSourceCellWitness)
(cd formal/s31 && lake env leanchecker -v S31.Gadgets.Functional.Correspondence.HonestSourceCellWitness)
```
