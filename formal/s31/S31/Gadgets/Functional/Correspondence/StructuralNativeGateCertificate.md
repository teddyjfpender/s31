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
node/assertion spans, named public bindings, and a separate **padded** graph
with the actual QM31 and Eq preprocessed column rows. It is written only after the
Lean byte gate, Zig topology/witness parity audit, and independent bounded
Python replay all accept. The CLI reports its SHA-256 digest.

**Keep this artifact local:** its value table includes private witness and
private input values. The CLI creates a new file with mode `0600` and refuses
to overwrite an existing path. Do not publish or attach it to a PR.

The independent replay checks every exported arithmetic gate equation,
including full QM31 extension multiplication used by input packing; all
equality gates; canonical M31 values; each source expression's concrete gate
or a justified fold, identity erasure, or CSE alias; assertion spans; and the
ordered public output words. The finalization audit independently reconstructs
the default radix-256 constant pass: the plus-one chain, base decomposition,
QM31 basis, broadcast constants, and remaining QM31 constants. It checks the
exact appended gate order, variable addresses, and the final public M31 and
private packed guess yields. It also checks that every variable has exactly
one producing gate. A satisfiable gate added coherently to both compiler modes
and the finalization span is therefore rejected by the independent replay.
The audit is restricted to the admitted structural M31 direct-Gate fragment;
other compiler modes and constant-base choices need their own replay. The
replay pins the engine builder, constant pass, and S31 radix-selection source
bytes so changes to their algorithms require another review.
These concrete checks
correspond to the address/value, gate, port, and assertion premises of
`checked_native_trace_sound` for **one supplied assignment**. The artifact is
an executable certificate, not a Lean proof term: a machine-checked decoder
from its JSON into `NativeTrace` is still needed to instantiate the theorem
inside Lean.

## From native gates to preprocessed AIR rows

The prover pads each component to a power-of-two row count before building
the preprocessed circuit. The exporter repeats that exact `padContext` pass
in both value and topology modes, checks their complete padded gate rosters
match, and extracts the QM31 operation and Eq columns from
`PreprocessedCircuit.fromBuilderCircuit`. The independent checker confirms
that padding only appends the specified trivial gates, keeps all prior values
and gates in place, and fills every exported row from the padded graph.

The QM31 rows are ordered by operation: all additions, then subtractions,
full QM31 multiplications, and pointwise M31 multiplications. Each row has
four one-hot selector flags, input addresses, an output address, and the
number of times that output is used by the **whole padded circuit**. For
example, an addition gate `Add(in0=20, in1=21, out=22)` whose result has two
uses yields `[1, 0, 0, 0, 20, 21, 22, 2]`. An equality gate `Eq(24, 0)`
yields the separate two-cell Eq row `[24, 0]`. The checker recomputes those
addresses and use counts independently, then compares every cell against
the Zig preprocessor's output. For the three-input test, 293 arithmetic
gates pad to 512 QM31 rows and one equality pads to 16 Eq rows.

This closes the exported gate-to-preprocessed **QM31/Eq cell projection**
for one bounded assignment. It does not yet show that the package commits to
these exact preprocessed columns, that the native verifier authenticates the
corresponding value/lookup rows, or that the artifact decodes to a Lean
`NativeTrace` proof term. The independent finalization-roster replay above
checks the unpadded graph before this padded-row projection.

The theorem and artifact do **not** authenticate committed AIR rows or a
private witness inside a proof. The next join binds the checked QM31/Eq
preprocessed cells and committed witness openings to the native verifier,
including lookup columns and the preprocessed commitment root. The Python
finalization replay is differential evidence against the source-pinned Zig
builder; it is not a Lean operational refinement of that builder.
