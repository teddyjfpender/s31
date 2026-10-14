# Where a folded `7` comes from

[StructuralNativeFixedConstant.lean](StructuralNativeFixedConstant.lean) proves a
bounded but useful nonzero constant case: after `x * 0` folds to the native
zero wire, `zero + 7` may fold to a broadcast-seven wire. Admission checks the
exact native finalization gates that produce that wire. The result works for
one to four active M31 lanes and composes with arbitrary other admitted source
steps. Only literal `7` is admitted by this extension.

```s31
circuit folded(public x: [m31; 2], private y: [m31; 2])
    -> public [m31; 2] {
    let zero = x .* splat<2>(0_m31);
    let z = zero + splat<2>(7_m31);
    assert_eq(z, y);
    z
}
```

For `x = [p−1, 3]` and `y = [7, 7]`, a fresh Zig export maps `zero` to
physical wire `0` and `z` to wire `18`. A separate private input also contains
`[7, 7]`; its equal sampled value does not make it the literal's owner.

## The native path, by hand

The names below describe *physical circuit wires*, not source variables.
The numeric addresses are from this one export; the checker takes and verifies
an address certificate so other sources can place intermediate wires
elsewhere.

| Result | Native gate | Forced packed value |
| --- | --- | --- |
| zero, wire `0` | `Add(0, 0, 0)` | `(0, 0, 0, 0)` |
| one, wire `1` | `Mul(2, 1, 2)` with public `u` at wire `2` | `(1, 0, 0, 0)` |
| base `2`, wire `26` | `Add(1, 1, 26)` | `(2, 0, 0, 0)` |
| base `3` through `7`, wires `27`–`31` | `Add(previous, 1, next)` | `(k, 0, 0, 0)` |
| `u²`, wire `281` | `Mul(2, 2, 281)` | `(2, 1, 0, 0)` |
| `i`, wire `13` | `Sub(281, 26, 13)` | `(0, 1, 0, 0)` |
| `i+1`, wire `20` | `Add(13, 1, 20)` | `(1, 1, 0, 0)` |
| `u+iu`, wire `282` | `Mul(20, 2, 282)` | `(0, 0, 1, 1)` |
| broadcast one, wire `283` | `Add(20, 282, 283)` | `(1, 1, 1, 1)` |
| broadcast seven, wire `18` | `Mul(31, 283, 18)` | `(7, 7, 7, 7)` |

`Mul` here is **QM31 extension multiplication**. It differs from source
`.*`, which is four independent M31 multiplications. For a QM31 packed value
`a+bi+(c+di)u`, the native `Mul(2,1,2)` equation is `u * one = u`. Since
`u = (0,0,1,0)` is a public circuit output, its four coordinate equations
force `one = (1,0,0,0)`: the remaining two unknown coefficients satisfy
`2c−d = 0` and `c+2d = 0`, hence `5c = 0`, so `c=d=0` in M31. The AIR rows
then force every later value in the table. The broadcast step is genuine
extension multiplication: `(7,0,0,0) * (1,1,1,1) = (7,7,7,7)`.

The Lean proof uses the source-extracted nine-residual native QM31 AIR relation
for each listed add, subtract, and multiply gate. Its checker reads the
source/certificate and the exact same exported graph bytes, projects the
native QM31 multiplication and output rosters, checks every path gate, and
requires the graph's first public output address to be `2`, and requires
`z`'s source-map address to be the final broadcast wire. It never
uses a sampled equality `z = 7` as the ownership proof.

## Adversarial controls and boundary

The [fixture](../../../../tests/audit/structural_native_fixed_constant.py)
accepts a fresh Zig export. Four mutations are each accepted by the older
value-only source checker and rejected by the fixed-chain checker: redirect
`z` to a different input wire also holding `[7,7]`, remove the final native
`Mul` gate, change the supplied public `u` cell, or replace its first public
output address.

The theorem assumes that supplied graph bytes and the native AIR rows are the
ones authenticated by an accepted proof. The runtime checker verifies
concrete gate equations and that wire `2` is first in the graph's public
output roster with the required `u` value; it does **not** authenticate that
roster or value to proof commitments. Installed Zig provenance, public output
packing, native cell authentication, and PCS/FRI soundness remain separate.
No proof-security bit estimate follows from this local correspondence proof.

Focused check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake build s31-structural-native-fixed-constant-check \
  s31-structural-native-trace-check
python3 tests/audit/structural_native_fixed_constant.py
```
