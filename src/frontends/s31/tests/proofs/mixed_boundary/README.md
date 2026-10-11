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
5. The production mixed package proves these exact source bytes, and its
   embedded-source native verifier accepts the serialized proof with the eight
   independently calculated public words. The proof header carries the same
   source digest, generated registry manifest digest, and circuit identity as
   the reconstructed schedule.
6. Changing any one of those three header digests, the interaction nonce, a
   claimed-sum byte, a proof-body byte, a public word, or the embedded source
   causes native verification to reject the proof.

This joins a concrete base-trace construction check to a serialized proof and
native verifier for two fixtures. It does not extract committed polynomial
values from the proof, establish AIR soundness independently of the Stwo
engine, or prove compiler correspondence for arbitrary programs.
