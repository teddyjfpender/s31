# Public record ABI v2: formal boundary increment

The Lean module [`RecordAbiV2.lean`](../../../formal/s31/S31/Gadgets/Functional/RecordAbiV2.lean)
models the first-order word boundary after a record type tree has been
validated. Each leaf is a block of M31 words with a checked width. The module
builds on `RecordBoundary.lean`, which proves that flattening and reconstructing
the product tree are inverses.

## Worked statement

Consider a public record `request` with `left: [m31; 2] = [3, 4]` and
`right: [m31; 1] = [5]`, a private one-word leaf containing `[7]`, and a
two-word result wire containing `[13, 14]`. Suppose the result names that
same wire twice, under two different field paths. The v2 statement has both
named result leaves, and each must claim `[13, 14]`. The native proof word
vector has one copy of that result wire:

```text
typed public leaves:  request.left=[3,4], request.right=[5]
private leaf:         [7] (excluded from the public statement)
result paths:         result.first=[13,14], result.again=[13,14]
proof words:          [3,4,5,13,14]
```

The fixture theorems establish that the typed projection and the native
first-order projection yield this five-word vector. The checked decoder
rejects a descriptor that changes the second input leaf width from one to
two. A concrete two-field path theorem proves that distinct field names
give distinct tagged paths.

## Precisely what the model assumes

- `WordBlock` contains canonical M31 words as an abstract element type. Lean
  checks the payload length against the declared width; it does not prove
  `0 ≤ word < 2³¹−1` for native `u32` words.
- A `ValidatedPaths` value carries injectivity as evidence. The module proves
  it for a concrete two-field layout with unequal names. It does not yet
  derive injectivity for every nested record/tuple layout from the production
  Zig `typeTree` walk.
- `InputRoot` visibility and result wire references are assumed to be the
  already validated relation descriptors. The theorem proves word-order
  agreement for those descriptors, not source parsing or key admission.
- The native projection is modeled as public relation inputs in declaration
  order, followed by first-appearance distinct result wires. This matches
  `record_abi.zig`'s `claimedWords` loop when `validate` has checked input and
  output order. The model does not prove correspondence to those Zig loops.

## Remaining refinement obligations

1. Model the complete n-ary record/tuple type tree, prove path injectivity
   from unique field names and tuple indices, and connect this to native
   `matchingPath` and `typeTree` acceptance.
2. Prove canonical statement parsing, SHA-256 ABI digest/key binding,
   duplicate-key rejection, M31 range checks, alias equality, and the
   eight-word limit against the production verifier.
3. Prove the Python compiler's typed flattening and source elaboration
   correspond to the validated native descriptor, including private root
   visibility and first-order wire order.
4. Compose this ABI theorem with opened AIR cells and the complete compiler
   correspondence theorem. This module alone is not a proof of STARK
   soundness, confidentiality, or full parser-to-proof correctness.
