# Independent static review: arithmetic-fed mixed chip calls

Reviewed S31 commit `062b46e` with pinned stwo-zig engine
`7d544c6839497ca19b6c7ef9b982e464f10cfeed`. This is a read-only
source review of the experimental `direct-mixed-general` proof route. It
does not claim a formal compiler theorem, a native test run, or a complete
cryptographic soundness bound.

## Result

No concrete P1/P2 false-proof or wrong-public-statement admission route was
found in the arithmetic-produced input extension. The checked links are:

1. [`bounded_call_admission.zig`](../../../src/frontends/s31/language/bounded_call_admission.zig)
   restricts each chip predecessor to an input, a previous repeat, or a
   four-lane `add`, `mul`, `add_const`, or `mul_const` node. It assigns distinct
   canonical repeat IDs in source order and rejects dead calls, unsupported
   bodies, noncanonical calls, and direct exposure of a repeat as a public
   output. The admission plan itself is not proof authority.
2. [`relation_compiler.zig`](../../../src/frontends/s31/language/relation_compiler.zig)
   marks source-selected predecessor nodes before lowering. For a packed
   arithmetic result, it calls `simd.unpack` once at that node and records
   the resulting four scalar addresses. The engine's `simd.unpackIdx` uses
   constrained pointwise multiplication and, for nonzero coordinates, a
   constrained multiplication by the inverse basis element. A later chip
   call consumes those same scalar wires; a fork shares their addresses.
3. [`bounded_compiled_binding.zig`](../../../src/frontends/s31/runtime/bounded_compiled_binding.zig)
   independently compiles witness-free and value-carrying circuits, checks
   call IDs, source/input node IDs, exact eight endpoint addresses per call,
   circuit shape, and the preprocessed fixed root. The engine's
   `ManyBoundary.validate` requires exactly one genuine producer for each
   endpoint address. Its preprocessor adds one committed Gate use for **each
   occurrence**, including a shared input consumed by two calls.
4. The pinned engine's `tagged_pair_bridge` and `tagged_many_bridge` AIRs
   bind the eight endpoint values across their 16-row traces. They consume
   the corresponding Gate tuples and connect the chip's tagged step-zero
   and final-step tuples. The chip AIRs constrain every lane's
   `next = current² + constant`; call IDs and step indices occur in the
   lookup tuples. Gate and chip relations use distinct relation IDs.
5. [`general_package.zig`](../../../src/frontends/s31/runtime/mixed_boundary/general_package.zig)
   rebuilds the source schedule, typed registry manifest, compiled topology,
   fixed root, and PCS geometry before bounded postcard decoding. Its only
   public proof-byte verifier uses compile-time embedded source and official
   AIR. The pinned engine checks the fixed commitment, AIR program binding,
   ordered runtime handles, all eight canonical public words, active and
   unused claimed sums, LogUp closure, transcript order, PCS configuration,
   and the borrowed STARK proof. The exported engine adapter accepts a
   caller-supplied selection and must not be treated as a standalone proof
   admission API.

## Minimal controls to retain

- Prove and verify `add`, `mul`, `add_const`, and `mul_const` feeders with an
  independent M31 oracle. Mutate each public word and every claimed-sum slot.
- For a fork, assert identical input addresses for both consumers and a
  committed multiplicity of two at each shared producer. Rebind one address
  in a copied topology and require rejection.
- Rebuild a verifier from source bytes that differ only in whitespace, then
  reseal the visible statement and proof identity fields. The old proof must
  still fail because the authenticated transcript source changes.
- Keep wrong assignments, dead calls, cross-count replay, proof-tail changes,
  noncanonical M31 words, and compensated claimed-sum mutations in the
  black-box gate. The current
  [`arithmetic_chip_input.py`](../../../src/frontends/s31/tests/acceptance/mixed_boundary/arithmetic_chip_input.py)
  covers the arithmetic, fork, changed-source, wrong-assignment, dead-call,
  proof-tail, and claimed-sum controls. The general
  [`source_pinned_general.py`](../../../src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py)
  covers the base 1–8-call route. This review did not rerun either gate.

## Remaining obligations

The conclusion assumes the installed circuit and chip AIRs enforce their
sampled constraints over committed traces, the Gate and tagged-step LogUp
arguments have the claimed collision bound, and the PCS/FRI and Fiat–Shamir
implementation soundly binds the one transcript. The existing
[`lookup worksheet`](LOOKUP_COMPRESSION_BUDGET_2026-10-11.md) bounds only its
conditional algebraic term. A machine-checked source-to-native compiler
correspondence theorem and complete concrete soundness calculation remain
open. `private` means excluded from the public statement; this profile
does not promise witness confidentiality.
