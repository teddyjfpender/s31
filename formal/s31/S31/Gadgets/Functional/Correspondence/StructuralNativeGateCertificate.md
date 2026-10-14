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

## Inspect the exact native graph

Run the bounded audit on the seven compiler artifacts and an assignment:

```sh
python3 -B formal/s31/scripts/general_structural_native_witness.py \
  source.s31 typed-tree.json certificate.json relation.json \
  public-abi.json assignment.json statement.json \
  --graph-out native-graph.json
```

The runner accepts arbitrary sources admitted by the structural M31 byte
gate; the seven paths are snapshots of the same bytes that gate reads. The
`--graph-out` file contains the actual Zig compiler's complete arithmetic and
equality gate arrays, all four M31 coordinates of every variable, interned
constant addresses, source-to-canonical IDs, canonical-to-wire addresses,
node/assertion spans, and named public bindings. It is written only after the
Lean byte gate, Zig topology/witness parity audit, and independent bounded
Python replay all accept. The CLI reports its SHA-256 digest.

**Keep this artifact local:** its value table includes private witness and
private input values. The CLI creates a new file with mode `0600` and refuses
to overwrite an existing path. Do not publish or attach it to a PR.

The independent replay checks every exported arithmetic gate equation,
including full QM31 extension multiplication used by input packing; all
equality gates; canonical M31 values; each source expression's concrete gate
or a justified fold, identity erasure, or CSE alias; assertion spans; and the
ordered public output words. It rejects a witness-only extra gate through
the witness-free graph comparison and an unaccounted extra gate in the exported
artifact through the recorded span end. A gate added coherently to both
compiler modes and to the finalization span remains possible: independent
enumeration of the native constant-derivation/finalization roster is open.
These concrete checks
correspond to the address/value, gate, port, and assertion premises of
`checked_native_trace_sound` for **one supplied assignment**. The artifact is
an executable certificate, not a Lean proof term: a machine-checked decoder
from its JSON into `NativeTrace` is still needed to instantiate the theorem
inside Lean.

The theorem and artifact do **not** authenticate committed AIR rows or a
private witness inside a proof. The next join is the proof that the exported
gate roster produces the exact preprocessed QM31 operation, equality, and
lookup columns used by the prover, followed by binding those columns and
committed witness openings to the native verifier.
