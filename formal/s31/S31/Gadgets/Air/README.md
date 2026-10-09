# Circuit AIR row models

`Qm31Ops.lean` models the nine local polynomial residuals emitted by the
production circuit AIR's `evaluateQm31Ops`. A row is accepted exactly when its
four flags encode one opcode and its output is that opcode's result for the
two packed QM31 operands. The theorem covers arbitrary field-valued flags and
output limbs, so malformed flag values and incorrect outputs are rejected.

`row_iff_normalized_node` composes the row theorem with S31's executable
normalized `add` and `mul` nodes for a full four-lane chunk. It uses the proved
M31-to-ZMod field map, so it relates the AIR's packed field values to native
M31 arithmetic. `honest_row`, `output_unique`, `all_flags_zero_rejected`, and
`two_flags_rejected` provide concrete non-vacuity and malformed-row controls.

S31 array addition uses the `add` opcode. S31 pointwise array multiplication
uses `pointwiseMul`; `mul` denotes multiplication in the QM31 extension field.

The preprocessed gate addresses and multiplicities, the Gate lookup relation,
trace-wide consistency, and the STARK verifier are outside this local row
theorem. See the [formal proof scope](../../../README.md) for the remaining
compiler and proof-system obligations.
