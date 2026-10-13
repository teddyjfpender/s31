# Complete runtime reshape and flatten

`functional.s31` groups six private M31 elements into three rows of two,
flattens the rows in their original order, then publishes element 3. The
independent value calculation is `x[3] = 7` for `valid.json`.

The rows are compile-time views. `flatten` verifies that every row refers to
the **same** source array, that the intervals are `[0,2)`, `[2,4)`, and
`[4,6)` in order, and that together they cover the entire source. It then
returns the original reference. Consequently `functional.s31` and
`direct.s31` emit byte-identical normalized relations and canonical IRs. The
native AIR has the same raw and padded gates, preprocessed cells, and FRI
settings. `expanded.s31` spells out the prior eager slices and concatenations
for a measured comparison; it is equivalent in value but its shifted views
require extra constrained unpack/pack gates.

The [Lean array-view lemmas](../../../../../../formal/s31/S31/Gadgets/Functional/ArrayNodes.lean)
prove that consecutive fixed-width windows rejoin to the original array and
that the erased field graph accepts exactly that value. The acceptance gate
checks this particular Python-to-Zig implementation; it does not turn the
whole frontend into a formally verified compiler.

The pinned `direct-gate` acceptance run measured **291 raw QM31 rows** for
both functional and direct spellings, against **332 raw rows** for the
expanded spelling. All three pad to 512 QM31 rows and 4096 preprocessed
cells, so this example shows a real reduction in unpadded circuit work while
the rounded proof geometry stays the same.

Reordered, repeated, incomplete, or separately consumed rows still emit
ordinary `array_slice`/`array_concat` nodes. The native circuit constrains
those views; no witness-supplied alias is accepted. This optimization covers
complete ordered `flatten(reshape<R>(x))` for runtime M31 and u16 arrays,
with `1 <= R <= 16` and exact divisibility. It does not optimize arbitrary
permutations or concatenations of slices.

Run the cost and proof acceptance gate:

```sh
python3 src/frontends/s31/tests/acceptance/functional/reshape_flatten.py
```
