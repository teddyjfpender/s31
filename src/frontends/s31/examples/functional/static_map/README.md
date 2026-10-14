# Static `map` with no relation overhead

[`map.s31`](map.s31) applies one named function to each value in a source-only
array. `std::array::map` evaluates its function expression and all array
elements once, then specializes one call per element in source order. Its
result is a static array of circuit values. The map itself has no relation
node, runtime tag, or witness column.

```text
fn square(v: [m31; 4]) -> [m31; 4] { v .* v }

let out = std::array::flatten(std::array::map(square, [x, y]));
```

[`manual.s31`](manual.s31) writes the two calls explicitly. Both lower to
the same normalized relation: two four-lane `mul` nodes followed by one
`array_concat` node for the requested flat output. The concat belongs to
both versions; it joins the two four-word results into eight output words.
The complete AIR geometry and native proof are checked by the
[static-map acceptance](../../../tests/acceptance/functional/static_map.py).
On the pinned `direct-gate` profile, both programs have 321 raw QM31 rows,
512 padded QM31 rows, and 4,096 preprocessed cells. The mapped program's
native proof verifies, and changing one claimed output is rejected. Those
counts include the package's circuit machinery, not just the three visible
source nodes.

`map` accepts 1–64 source-only array elements of one first-order circuit
type and a unary `Fn` that returns a first-order circuit type. The function
may be named or a captured closure. It cannot iterate over a runtime array
without an explicit source-level view, and partial effects in the mapped
function remain visible to witness-dependent conditionals. This static
combinator provides higher-order source syntax without claiming a new
runtime array operation or a general compiler correspondence theorem.
