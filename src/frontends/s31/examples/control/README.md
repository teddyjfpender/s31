# Witness-dependent choices

[`total_if.s31`](total_if.s31) computes both total M31 branches and selects
one public result with a constrained bit. The
[manual form](total_if_manual.s31) uses `select` explicitly; the native gate
compares exact AIR cost and proves both selector values.

[`byte_choice.s31`](byte_choice.s31) selects one of two private `Bytes32`
values, reinterprets its sixteen u16 limbs as field words, and publishes
their sum. The [manual form](byte_choice_manual.s31) must emit identical
relation IR and AIR geometry. Both [choice one](byte_choice.valid.json) and
[choice zero](byte_choice.alternate.valid.json) have native proofs and changed
public claims are rejected by the generated verifier under
`sparse-wide-gate`. The M31-only `direct-gate` profile does not accept u16
inputs.

The source `if` eagerly emits both branches. Each arm must be total on every
well-typed witness. The compiler rejects partial checked operations in an
inactive arm; see the [functional guide](../../docs/functional-language.md#witness-dependent-conditionals).
