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

## Fresh native proof join for this program

The opt-in native regression builds this exact source, attaches the v3
correspondence certificate, and checks its full exported 8-column × 512-row
fixed roster against the independent source schedule. It independently checks
that the four source arithmetic lets map to compact IDs `[1, 2, 3, 3]`, with
three native arithmetic gates and no fourth gate for `d`.

For public input `[0, 1, 2, 7]`, the handwritten public output is
`[0, 3, 8, 63]`. The regression proves that statement, asks the generated
native verifier to accept the exact proof, recommits all 4,096 exported fixed
cells through the native PCS preparation path, and requires that root to equal
both the sealed key root and proof commitment 0. It also hashes the 6,144
exported main cells, checks the native main-root diagnostic against those
bytes, and requires its root to equal proof commitment 1. A changed fixed
selector changes the recommitted root. Changes to either root byte in the
proof and to the public result must be rejected by the generated verifier.
The earlier resealed source-map mutation remains part of the same regression.
On the pinned 2026-10-12 build, the fixed root was
`f08f6d98c79316b827950a3a5af5f812d21e54c11a45a683d8207fc0a46f1c56`,
the main root was
`7187f0aabef67d4d5a0629256e016d9ea897fa10b614e15537d9c26de1c9beb2`,
and the accepted proof was 55,386 bytes. These are observed regression bytes,
not a guarantee across compiler changes.

```sh
PYTHONPATH=src/frontends/s31/python \
  python3 src/frontends/s31/tests/python/check_optimized_native_package.py
# Add --work /tmp/s31-optimized-evidence to retain the package and proof.
```

This is one honest-prover, public-only native test under the pinned compiler
and Stwo dependency. The v3 certificate is opt-in. The separate
[`optimized_release.py`](../../../../../../src/frontends/s31/tests/acceptance/compiler_correspondence/optimized_release.py)
uses the v3 package build and strict release path for a live-output CSE case.
The equality of inspected rows and proof
commitments is an executable implementation check; it does not prove native
emitter refinement for every optimized source, arbitrary PCS opening
authentication, or FRI soundness.

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
