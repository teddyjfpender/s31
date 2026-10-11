# Independent review: mixed public closure versus emitted Gate tail

**Finding: the new `TailRow` premise does not describe a Gate row emitted by
the current compiler for the reviewed N1/N8 mixed source family.** The Lean
theorem is a valid conditional statement, but its eight required `TailRow`
witnesses cannot presently be supplied from the native circuit. This blocks
using it as a compiler-correspondence or native-proof soundness theorem.

## Concrete divergence

`SourceMixedPublicClosure.lean` defines `TailRow` as one selected row with

```text
in0 = last chip scalar output address
in1 = initial scalar input address
out = reserved public output address (3..10)
op = add for sum, pointwiseMul for product
```

For the source tail `sum = r_last + x; product = r_last * x`, the actual
compiler does three stages:

1. [`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig)
   lowers `.add`/`.mul` through `simd.add`/`simd.mul` (lines 664–665).
   [`simd.zig`](../../../deps/stwo-zig/src/frontends/circuit/builder/simd.zig)
   emits one operation on the **packed QM31 wires** (lines 105–125). Its row
   output is a fresh packed variable, not a reserved public address.
2. `relation_compiler.zig` calls `outputWord` for each of the eight public
   lanes (lines 889–928, 1038–1040). `simd.unpackIdx` emits a pointwise
   multiplication by a lane basis vector; lanes 1–3 then emit a second QM31
   multiplication by the inverse basis vector (`simd.zig`, lines 193–200).
   The resulting scalar wire is the binding input.
3. `ctx.setOutputs` runs after extraction (`relation_compiler.zig`, line 930).
   [`context.zig`](../../../deps/stwo-zig/src/frontends/circuit/builder/context.zig)
   emits a separate **add** row `scalar_wire + 0 = reserved` for each public
   address 3–10 (lines 275–286). That row's second input address is zero,
   not any of the initial input addresses 11–14. Product public addresses
   also have add flags, not pointwise multiplication flags.

The reviewed address fixture puts the first private input scalars at 11–14,
the first chip result scalars at 23–26, and the eighth chip result scalars at
93–96. The packed input is at 22. The N1 last packed result is at 32, so the
source add/product rows output fresh packed wires 33/34. For N8, the last
packed result is at 102 and these two packed arithmetic rows output 103/104.
The source result extraction then allocates further scalar wires before the
reserved binding rows output 3–10. These address calculations follow the
existing exact endpoint schedule and the builder's fresh-variable order;
the core contradiction does not depend on their precise later extraction
addresses.

Hence the only rows outputting public address 3–10 are binding additions
with `in1Address = 0`. They cannot satisfy either `hadd` or `hmul` as written.
The multiplicity and local `accepts` assumptions in `TailRow` do not repair
the topology mismatch.

## Formal and test implications

The theorem's internal use of exact joint balance and unique produced values
is appropriate *given* selected rows. The missing step is more than proving
those premises: the selected rows themselves have the wrong shape. A valid
replacement should model the packed arithmetic row, each lane's extraction
path, and the final public binding row, then use Gate balance, unique
producers, local row equations, and fixed basis constants to derive each
public M31 word. In particular, lanes 1–3 need their second extension-field
multiplication row. The compiler-to-row correspondence must then establish
that these concrete rows and addresses are present in the source-pinned
compiled circuit.

The existing `typed_boundary_correspondence.py` statically checks N1–N8 chip
endpoints against a hand-derived schedule and public words with an independent
arithmetic oracle; its default native fixture runs N1/N8. It **does not read
the circuit Gate rows**, so it cannot discharge `TailRow`. Native N1/N8
positive proofs and the N1/N3/N8 semantic
source-reseal controls remain valid executable checks; they do not turn this
conditional Lean theorem into an end-to-end proof.

Reproduction from source:

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/typed_boundary_correspondence.py
rg -n 'TailRow|hadd|hmul' formal/s31/S31/Gadgets/Air/SourceMixedPublicClosure.lean
rg -n 'outputWord|setOutputs|\.add =>|\.mul =>' src/frontends/s31/language/relation_compiler.zig
rg -n 'pub fn unpackIdx|pub fn setOutputs' deps/stwo-zig/src/frontends/circuit/builder/{simd,context}.zig
```

This finding concerns a hidden formal instantiation premise. It is not a
demonstrated false-proof admission in the native verifier.
