# Structural M31 native gate certificate

`StructuralNativeGateCertificate.lean` connects a supplied native direct-Gate
address/value trace to the existing effectful SSA theorem. Its main theorem,
`checked_native_trace_sound`, is universal over the number of SSA steps and
over all M31 values in one to four packed lanes. It is conditional on the
certificate's addresses and values actually being the native graph/witness.

For example, consider this two-lane source fragment:

```s31
circuit difference(public x: [m31; 2], private y: [m31; 2])
    -> public [m31; 2] {
  let z = x - y;
  assert_eq(z, z);
  z
}
```

Suppose the native graph maps source IDs `x`, `y`, `z` to packed wire addresses
`20`, `21`, `22`. A certificate for the subtraction step contains the exact
record `Sub(in0=20, in1=21, out=22)`. `checkGates` checks all four physical
M31 coordinates of this row, so its active first two coordinates imply
`z[0] = x[0] - y[0]` and `z[1] = x[1] - y[1]`. The unused coordinates remain
physically checked by the gate but carry no source meaning. `checkInputPorts`
checks that the source input values match the packed wires, and
`checkOutputPort` checks that the selected source result and public claim
match wire 22. The native trace theorem transports these checks through every
SSA step to the source expression.

`native_air_row_satisfied` proves the same four-coordinate equation from the
actual nine `qm31_ops` polynomial residuals extracted from the native AIR.
It fixes the selector to the source operation, including ordered subtraction
and pointwise M31 multiplication. `native_air_rows_check` applies this to an
arbitrary supplied gate roster and discharges `checkGates` from local AIR
acceptance. This removes a separate arithmetic assumption at the local
polynomial-to-gate layer. The selector/address cells and witness values must
still be authenticated to the actual committed trace and proof.

For a short-lane equality assertion, Zig may lower `assert_eq(a, b)` as
`diff = a - b`, `masked = diff .* (1, 1, 0, 0)`, and `masked = 0`.
`masked_assertion_sound` proves from those three equations that both active
lanes of `a` equal `b`. `checkAssertions` checks the resulting equality for
every assertion, including an assertion on a node unused by the output.

The theorem does **not** establish that Zig emitted the addresses, gate lists,
or mask path given to it. The executable audit in
`formal/s31/scripts/general_structural_native_witness.py` compares the actual
Zig witness and witness-free graphs for one supplied program/assignment, but
does not authenticate committed AIR rows or the private witness in a proof.
The next correspondence step is to bind this generic certificate to those
native graph bytes and then to the committed direct-Gate AIR rows.
