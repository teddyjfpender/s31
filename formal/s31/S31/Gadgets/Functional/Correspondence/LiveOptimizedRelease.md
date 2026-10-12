# Exact optimized release example

[`LiveOptimizedRelease.lean`](LiveOptimizedRelease.lean) kernel-checks the
exact byte streams of the [checked-in source](../../../../../../src/frontends/s31/examples/functional/release_optimized4/functional.s31),
its production normalized JSON, and its compact canonical IR. A Python unit
test compares all three Lean literals with the current production frontend,
so changing either implementation makes the binding fail.

```s31
circuit reverse_share(public x: [m31; 4]) -> public [m31; 4] {
    let a = x + x;
    let b = x .* x;
    let c = a + b;
    let d = b + a;
    let e = c + d;
    e
}
```

The source has five arithmetic lets. Its normalized relation keeps all five
nodes and outputs `e`. The canonical circuit sorts the operands of `d`,
recognizes the same addition as `c`, and gives both names circuit wire 25.
The final addition reads that wire twice. This is live sharing: both source
values contribute to the output.

| Value | Formula per M31 lane | Circuit wire | Physical operation row |
| --- | --- | ---: | ---: |
| input `x` | public input | 22 | input packing |
| `a` | `2x` | 23 | 3 |
| `b` | `x²` | 24 | 503 |
| `c`, `d` | `2x + x²` | 25 | 4 |
| `e` | `c + d = 4x + 2x²` | 26 | 5 |

The multiplication is physically at row 503 because the Gate trace groups
operations by type. Wire addresses still follow the circuit dependency order.
For `x = [0, 1, 2, 7]`, the output is `[0, 6, 16, 126]` modulo
`2³¹ − 1`.

The Lean theorem `exact_source_normalized_and_canonical_bytes` checks the
three exact streams; `five_live_lets_share_four_producers` checks the node
count; `exact_compact_operation_rows` checks their modeled placement. The
`accepted_modeled_rows_bind_public_claim` theorem says that any coherent wire
map satisfying those four local operation cells and the modeled public input
and output boundaries has the source result. It quantifies over arbitrary
values in those modeled rows, rather than one honest trace.

The [native acceptance](../../../../../../src/frontends/s31/tests/acceptance/compiler_correspondence/optimized_release.py)
separately checks the actual compiler's fixed topology and AIR geometry,
proves the result, runs five-pin strict release verification, and rejects a
false public claim and certificate downgrades. Its observed geometry is 324
raw QM31 rows padded to 512, equal to the handwritten four-gate source.
The Lean theorem assumes the modeled rows and boundaries; it does not prove
that the native verifier authenticates them through Gate lookup or PCS/FRI.

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.LiveOptimizedRelease
lake env leanchecker S31.Gadgets.Functional.Correspondence.LiveOptimizedRelease
cd ../..
python3 -m unittest src.frontends.s31.tests.python.test_live_optimized_release_binding
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/optimized_release.py
```
