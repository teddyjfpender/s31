# Bounded SSA to native source-gate schedule

`SSANativeTopologyCheck.lean` models one narrow part of the direct-gate
compiler correspondence check. It accepts a four-lane add or pointwise-multiply
SSA certificate and a list of **source arithmetic gates**. The checker starts
with input wire address `0`. For every instruction, it requires the native
gate to read the addresses of exactly the named prior wires, use the same
operation, and write an address not already assigned. It consumes both lists
completely.

For example, the source `let square = x .* x; let y = square .* square; y`
can use native addresses `0 → 37 → 83`:

| SSA step | Native gate | Address list afterward |
| --- | --- | --- |
| input `x` | public input at `0` | `[0]` |
| `square = x .* x` | pointwise multiply `(0, 0) → 37` | `[0, 37]` |
| `square .* square` | pointwise multiply `(37, 37) → 83` | `[0, 37, 83]` |

The executable `checkRows` rejects a changed operand, opcode, reused output
address, missing gate, or extra gate. `checkSourceRows` also runs the existing
source certificate checker, so a bad instruction ID or forward reference is
rejected. The module contains concrete rejection examples for each case.

## What the theorem establishes

`checked_source_rows_sound` says: if `checkSourceRows` accepts the complete
gate list, every row has authenticated operand values and satisfies the
modeled packed arithmetic AIR equations, and the final wire is claimed as
the public output, then that output equals the source expression on every
four-lane field input. `checked_rows_length` shows that accepted source gates
and instructions have equal length. `checked_rows_nodup` shows that the
resulting address list has no repeated producer address when the input list
starts unique.

The authentication premise is `AuthenticatedRows`. It relates row operands
to prior values **by native address**, not by trusting the instruction's
positional operands. `checkRows` proves that each selected operand address is
present at exactly the relevant SSA position. The existing `SSAAirRows`
theorems then convert all authenticated rows into a source-value result.

## Remaining proof obligations

This Lean model does **not** prove that the production Python checker has the
same behavior as `checkSourceRows`, or that Zig emitted the gate list it
reports. It models only the ordered source arithmetic gate projection. The
production checker additionally checks input packing, output extraction,
constant derivation, padding, column values and hashes, and package
serialization. Nor does this module prove that a verifier's preprocessed
commitment authenticates that list, or that Gate lookup, STARK AIR evaluation,
and PCS imply `AuthenticatedRows`. Those are explicit implementation and
cryptographic boundaries. A successful package-only Python check must not be
described as a theorem about the installed native verifier.

## Arbitrary source names

`SSAGeneralNamedTopology.lean` adds the bounded grammar's user-chosen names.
A name table has one public input name followed by one name per checked SSA
instruction. Its executable checker requires the exact normalized `Program`
encoding, a unique nonempty name for each wire, an output that is a let-bound
wire, and successful normalized `Program.validate`. It composes this check
with `checkSourceRows`; a renamed output or operand is rejected. For example,
`["input", "square", "fourth"]` corresponds to the same two native gates as
`["x", "w1", "w2"]`.

The Lean theorem establishes exact structural equality of the normalized
node list and source-value soundness under `AuthenticatedRows`. It does not
yet prove a universal equivalence of arbitrary-name `Program.evaluate` and
the positional SSA evaluator. A proof of that equivalence needs an induction
over the actual named environment and lookup behavior for the name table.
The Python lexical rule, source byte parser, JSON serialization, CSE rule,
canonical operand order, full gate list and verifier admission also remain
outside this Lean model. These are the next exact compiler-correspondence
obligations; the present modules do not establish a full compiler theorem.
