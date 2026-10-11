# Mixed boundary native base trace fixture

`trace_correspondence.zig` checks the exact `N=1` and `N=8` square/add chain
used by the [typed boundary correspondence fixture](../../acceptance/mixed_boundary/typed_boundary_correspondence.py).

Run the focused test from the S31 repository root:

```sh
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-correspondence -j1
```

The test compiles the pinned source and witness, then calls the **same native
base trace writers** as `direct_mixed_general_arithmetic.proveSourceBound`.
It independently calculates each field recurrence and checks:

1. The source-derived endpoint addresses, including the exact allocation for
   this chain family; all eight Gate endpoint words per call are read from the
   native bridge base columns.
2. Every bridge endpoint column contains its expected word on all 16 rows,
   and the native Gate tuple has the expected relation, address, and word.
3. Every one of the 16 chip steps has the expected input and output words in
   the chip's bit-reversed base trace storage; native tagged start and finish
   tuples match the boundary words.
4. The circuit base trace's eight public output words match an independent
   calculation of the final `sum` and `product` nodes.

This is a concrete witness construction check for two source fixtures. It
does not inspect committed proof bytes, prove that the AIR authenticates the
base trace, or establish compiler correspondence for arbitrary programs.
