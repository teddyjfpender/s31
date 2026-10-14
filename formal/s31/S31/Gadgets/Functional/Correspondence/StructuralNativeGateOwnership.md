# Native Gate ownership for direct M31 steps

[StructuralNativeGateOwnership.lean](StructuralNativeGateOwnership.lean) checks
that every admitted **binary** source step names an actual native
add/sub/pointwise-mul gate with the source operands' wire addresses and the
step's output address. Add and pointwise multiplication may exchange operand
order; subtraction may not. Several source steps may reuse one gate after CSE.
Constant steps and other compiler erasures are deliberately rejected by this
checker until they have separate AIR-backed ownership rules.

## Hand example

```s31
circuit repeat(public x: [m31; 2], private y: [m31; 2])
    -> public [m31; 2] {
    let a = x + y;
    let b = y + x;
    let z = a .* b;
    assert_eq(z, z);
    z
}
```

For `x = [2, 3]` and `y = [4, 5]`, source values are `a = b = [6, 8]`
and `z = [36, 64]`. The Zig exporter maps `a` and `b` to one canonical wire.
Writing `wx`, `wy`, `wa`, and `wz` for its actual numeric wire addresses, the
relevant native roster is:

| Source step | Addressed native gate | Why accepted |
| --- | --- | --- |
| `a = x + y` | `Add(wx, wy, wa)` | Exact ordered gate |
| `b = y + x` | The same `Add(wx, wy, wa)` | Commutative operand swap and CSE |
| `z = a .* b` | `PointwiseMul(wa, wa, wz)` | Exact gate with aliased operands |

`checkOwnedStep` does **not** compare `wa` with `wx + wy` or `wz` with
`wa * wa`. `direct_owner_air_sound` derives those four-coordinate equations
from the owning gate's nine native AIR residuals. `checkOwnedSteps_air_sound`
then constructs the source trace for any number of admitted binary steps.
`checked_direct_owned_source_air_sound` joins independently parsed source
bytes, canonical SSA certificate bytes, decoded graph bytes, ports, output,
assertions, and these AIR-derived steps. Under its explicit `NativeAirRows`
premise, it proves the parsed source denotation for 1–4 active lanes.

The [runtime control](../../../Audit/StructuralNativeGateOwnershipCheck.lean)
accepts a real Zig export for this example. Removing its one source `Add`
gate leaves the stored values unchanged: the earlier value-only Lean checker
still accepts, while the ownership checker rejects. This is a concrete case
where checking values alone misses a source-to-AIR gate premise.
It also exports a one-lane subtraction with both inputs zero. Reversing its
native `Sub` operands keeps that assignment and every concrete gate equation
valid, so the value-only checker accepts; ownership rejects the reversed
address order. The mutation would compute a different result for other inputs.

## Boundary

The theorem's `NativeAirRows` premise says that the nine residuals vanish for
the **supplied** graph's gate roster. The runtime control checks concrete gate
equations but does not authenticate that graph, its source-map or its gate
cells to an accepted proof. Installed Zig export provenance, exact source-node
span ownership, public word packing, committed AIR cell authentication, and
PCS/FRI soundness remain separate. The theorem does not cover source constant
steps or optimizer erasures such as add-zero aliases and folded constants.

Focused check:

```sh
cd formal/s31
LEAN_NUM_THREADS=1 lake build s31-structural-native-gate-ownership-check \
  s31-structural-native-trace-check
python3 tests/audit/structural_native_gate_ownership.py
```
