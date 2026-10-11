# Public record ABI v2: whole-descriptor shape

[`RecordDescriptorValidationV2.lean`](RecordDescriptorValidationV2.lean)
extends the [per-root layout checker](RecordLayoutValidationV2.md) to one
descriptor with all input roots and one result root. It starts with an
already parsed named type tree. The checker is executable (`checkDescriptor`),
and `checkDescriptor_iff` states exactly what an accepted result means.

## A complete example

```s31
struct Pair { value: [m31; 1] }

circuit copy(public x: Pair) -> public Pair {
    Pair { value: x.value }
}
```

The abstract descriptor has an input root `x` and result root `result`.
Each root contains the nominal type `Pair` with one field `value` and one
`m31[1]` leaf. The whole checker accepts this descriptor. Its total leaf
count is **two** because the descriptor contains two paths, even though the
computation may use one underlying relation wire. The proof word vector and
alias handling are separate from this shape check.

The model stores a normalized type code for each occurrence of `Pair`:

```text
record Pair [ (value, leaf m31 1) ]
```

If the result instead declares `value: [m31; 2]`, the two occurrences of
`Pair` have different type codes and the descriptor is rejected. The Lean
fixtures also reject a private `bit[1]` input, duplicate input names, and an
input named `result`. A theorem rejects **any** descriptor whose sum of
input and result leaf counts exceeds 1,024.

## What acceptance gives downstream

For every input and for the result, the theorem derives `checkRoot = true`,
unique complete field paths (`WellTagged`), and the allowed leaf widths:
`m31` lengths 1–8 and `bit` length one. It derives that no leaf below a
private input has kind `bit`. Acceptance also records distinct input root
names, a result root named `result` that does not collide with an input,
the global leaf budget, and equal normalized type-token streams wherever the
same nominal record name appears. At least one root must be a record, matching
the native version-two boundary rule.

This closes descriptor-level *shape* premises for the abstract layout model.
The module does not separately prove that the token encoding is injective;
the formal nominal theorem states equality of its arity-tagged streams.
The model has no claim that the production parser yields this exact tree.
The [lexical layer](RecordDescriptorLexicalV2.md) now checks native identifier
spelling for the already parsed tree. Native JSON syntax, canonical descriptor bytes,
nominal-code equality with native JSON serialization, ordered leaf paths and
wire references, relation inputs and outputs, and proof authentication still
require separate refinement arguments. The public-bit value check and
canonical M31 word checks are also separate.
