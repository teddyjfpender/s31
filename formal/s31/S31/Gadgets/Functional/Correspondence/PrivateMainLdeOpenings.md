# Private Gate main-tree openings: independent finite LDE audit

Run after setting up the Lean checker and pinned Stwo submodule:

```sh
python3 -B formal/s31/tests/audit/private_main_lde_openings.py
```

The test extends the [private committed-cell audit](StructuralPrivateCommittedAirJoin.md)
for this exact S31 program:

```s31
circuit private_square(public x: [m31; 4], private y: [m31; 4])
    -> public [m31; 4] {
    let pair = (x, y);
    let d = pair.0 - pair.1;
    let z = d .* d;
    z
}
```

The assignment has public `x = [5,8,13,21]`, private
`y = [1,3,5,8]`, and public `z = [16,25,64,169]`. The preceding audit
checks the source-to-graph path, all 12 main base columns with 512 cells
each against the direct-Gate writer, both commitment roots, the native
verifier's acceptance of the exact proof, and rejection of private-row
inspection by production package commands.

## What the extension check computes

The main-tree PCS first interpolates each 512-row base column as a circle
polynomial, then evaluates it on a 1024-point canonical circle domain.
The committed and opened values use **bit-reversed physical indices**. For
each natural base-domain index `i` in `0..255`, the physical entries at
`reverse9(i)` and `reverse9(i+256)` are adjacent. Their circle points are
`(xᵢ, yᵢ)` and `(xᵢ, −yᵢ)`. The test explicitly checks that ordering, that
every `yᵢ` is nonzero, and that the 256 `xᵢ` values are distinct.

A polynomial of this degree profile can be written as `a(x) + y b(x)`,
where `a` and `b` each have degree below 256. For pair values `u` and `v`,
the test recovers their samples directly in M31:

```text
a(xᵢ) = (u + v) / 2
b(xᵢ) = (u − v) / (2 yᵢ)
```

For example, if one pair has values `u = 5` and `v = 3`, its samples are
`a(xᵢ) = 4` and `b(xᵢ) = 1/yᵢ`. Evaluating `4 + yᵢ(1/yᵢ)` gives 5 at the
first point; evaluating `4 − yᵢ(1/yᵢ)` gives 3 at its conjugate.

The audit computes ordinary barycentric Lagrange weights from the 256
distinct `xᵢ` values. At a queried extension point `(X,Y)`, it evaluates
the two interpolants and combines them:

```text
λᵢ(X) = [1 / ∏_{j≠i}(xᵢ−xⱼ)] / (X−xᵢ)
a(X) = ∑ᵢ λᵢ(X)a(xᵢ) / ∑ᵢ λᵢ(X)
b(X) = ∑ᵢ λᵢ(X)b(xᵢ) / ∑ᵢ λᵢ(X)
opening(X,Y) = a(X) + Y b(X)
```

Circle points come from a separate M31 generator exponentiation in the
Python audit. This interpolation shares neither the prover's FFT nor its
column-preparation implementation. The native verifier supplies its sampled
query indices through an existing diagnostic environment flag for this
test; the audit decodes the 12 main-tree opening vectors from the exact
accepted postcard proof. The current fixture yields **66 unique sampled
positions and 792 equalities** across all 12 columns. A changed decoded
opening value and a changed query position each fail the same comparison.
The preceding audit also changes an encoded main-tree opening in the proof
and requires the native verifier to reject it at `RootMismatch`.

This is a finite honest-proof differential check for the stated source,
assignment, trace geometry, proof bytes, and sampled positions. It does
not prove all-input circle interpolation, cryptographic Merkle binding,
query randomness, FRI soundness, or a general compiler correspondence
theorem. `private` excludes `y` from the public claim; this proof mode is
**transparent and does not promise zero knowledge**. No production private
row or witness export is introduced.
