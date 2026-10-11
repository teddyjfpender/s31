# Record ABI v2 identifier check

[`RecordDescriptorLexicalV2.lean`](RecordDescriptorLexicalV2.lean) adds the
identifier rule used by `src/frontends/s31/language/record_abi.zig::name` to
the already parsed [whole-descriptor shape checker](RecordDescriptorValidationV2.md).
It is a separate layer, so the original shape model can still be used for
pure type-tree arguments.

The native rule is defined **on UTF-8 bytes**:

```text
length:         1..128 bytes
first byte:     A..Z, a..z, or _
remaining:      A..Z, a..z, 0..9, or _
```

For example, `_Pair09` passes; `9Pair`, `bad-name`, the empty string, and
`é` fail. The `é` example matters because a Unicode letter is not an ASCII
byte accepted by the Zig validator. A name with exactly 128 allowed bytes
passes, and one with 129 fails. `checkNativeName_iff` proves that the Boolean
checker is equivalent to the explicit `NativeNameGrammar` proposition.

## A whole descriptor by hand

Consider the parsed descriptor for:

```s31
struct Pair { value: [m31; 1] }
circuit copy(public x: Pair) -> public Pair {
    Pair { value: x.value }
}
```

The identifier traversal is:

```text
input root x → nominal Pair → field value
result root result → nominal Pair → field value
```

`layoutNames` recursively visits nominal and field names inside records and
children of tuples. `descriptorNames` adds every input root name and the
result root name. `checkLexicalDescriptor` requires both the previous
`checkDescriptor` and successful validation of every enumerated name.
`checkLexicalDescriptor_iff` proves exactly this conjunction. The
`checked_input_root_name`, `checked_input_layout_name`,
`checked_result_root_name`, and `checked_result_layout_name` theorems expose
the grammar result for any named position. The list-membership lemmas show
that nominal names, field names, and names nested below record or tuple
children are included in the traversal.

The previous shape checker accepts a structurally valid record named
`bad-name`, because identifier spelling was outside its model. The new
checker rejects it. Kernel-checked examples also reject empty nominal and
field names while confirming that these examples still pass the original
shape checker. This makes the refinement boundary visible rather than
silently changing the meaning of `checkDescriptor`.

## Proof boundary

This module proves a property of an **already parsed `NamedLayout` tree**.
It does not prove that Zig's JSON parser constructs the same tree, that the
tree's ordered leaves bind the same relation wires, that the canonical
descriptor digest matches, or that a verifier accepts only this descriptor.
Those source-to-Lean and proof-authentication links remain separate.

Focused checks from `formal/s31`:

```sh
lake build S31.Gadgets.Functional.RecordDescriptorLexicalV2
LEAN_NUM_THREADS=1 lake env leanchecker -v S31.Gadgets.Functional.RecordDescriptorLexicalV2
```
