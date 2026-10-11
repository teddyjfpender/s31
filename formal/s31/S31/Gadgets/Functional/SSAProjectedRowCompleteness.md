# Why the source-to-AIR row projection cannot omit a step

The bounded direct-gate compiler first makes an SSA instruction list. It
places addition gates in the AIR's add partition and pointwise products in a
later partition. The Lean model `expectedRows` computes those positions. The
fixed-column model `expectedCells` then **zips** the instruction and row lists.
A zip takes only the shorter list, so a length mistake would silently omit a
source instruction from the formal projection. `expected_rows_length` and
`expected_cells_length` prove both lists have exactly the instruction count.

Here is a handwritten example. Let `x` be a four-lane M31 input. Compute

```text
let doubled = x + x;
let square = doubled .* doubled;
square
```

The SSA rows are `1: add(0,0)` and `2: pointwise_mul(1,1)`. Circuit wire
addresses start at `22`, so their outputs are at `23` and `24`. In the
512-row native profile for this two-step source, the add partition has 475
rows. Three input-pack additions come first; the source add is therefore
at trace row `3`. One sub and 27 ordinary multiplication rows follow the
add partition. The source product is at `475 + 1 + 27 = 503`. The eight
four output-mask pointwise rows use indices `504` through `507`; four
input-self pointwise rows use `508` through `511`.

| Source instruction | Circuit operation | AIR trace index | Fixed selector |
| --- | --- | ---: | --- |
| `doubled = x + x` | `22 + 22 → 23` | 3 | add = 1 |
| `square = doubled .* doubled` | `23 .* 23 → 24` | 503 | pointwise = 1 |

The native partition equation is
`totalAddRows + 1 + 27 + sourceProducts + 8 = 512`; in this example it is
`475 + 1 + 27 + 1 + 8 = 512`. `expected_rows_trace_nodup` proves that all
source rows have distinct trace indices for up to 16 instructions, even if
additions and products are interleaved or some instruction result is unused.
`expected_rows_within_native_trace` additionally proves that every source
index is below 504 when the partition equation holds. The corresponding
theorems transfer both facts to fixed-column cells and to an observed list
that equals that projection. A repeated observed trace index is rejected.

These theorems concern the **modeled** row schedule. They assume the
16-instruction bound and, for the range result, the partition equation.
`SSAGeneralDecodedTraceBridge.lean` separately proves that successful Lean
byte admission supplies the instruction bound. The package checker checks
the partition equation against the native export, but this module does not
prove that the exported count is authenticated by the verifier. Zig emitter
fidelity, the preprocessed commitment opening, Gate lookup, and PCS/FRI
verifier soundness also remain outside this theorem.
