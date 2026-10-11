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
give distinct tagged paths. `concatBlocks_length` proves that the word count
is the sum of checked leaf widths; the eight-word predicate therefore counts
aliased result wires once.

## General n-ary path uniqueness model

The new `NominalTree` model follows the shape of the ABI's path walk more
closely than the binary product used for flattening. A node has any finite
number of children. Each child contributes exactly one tagged segment:
`{ "field": name }` for a record or `{ "tuple": index }` for a tuple.
`namedRecord_wellTagged` derives local validity from distinct sibling field
names, and `indexedTuple_wellTagged` derives it from zero-based indices.
The raw tree stores no injectivity evidence; `WellTagged` states exactly the
local validation obligation. Neither local lemma assumes complete-path
injectivity.

For example, the nested layout

```text
request: { items: (m31, m31, m31), salt: m31 }
          |        |      |      |
          |        0      1      2
          +-- field "items" or field "salt"
```

has these paths:

```text
items[1] = [root "request", field "items", tuple 1]
items[2] = [root "request", field "items", tuple 2]
salt     = [root "request", field "salt"]
```

`nominalPath_injective` proves that any two positions in **any finite depth**
n-ary tree satisfying `WellTagged` have different tagged suffixes.
`rootedNominalPath_injective` prepends a fixed root and preserves that result;
`rootedNominalPath_distinct_roots` handles different root names. The worked
`nestedFixture` checks both a tuple-index difference and a record-field
difference. This is a theorem about the Lean type tree and path function,
not yet a theorem about the native parser's execution.

## Precisely what the model assumes

- `WordBlock` models M31 words using an abstract element type. Lean checks
  the payload length against the declared width; it does not prove
  `0 ≤ word < 2³¹−1` for native `u32` words, or that each declared leaf width
  lies in the production range `1..8`.
- `ValidatedPaths` for the earlier binary product model still carries
  injectivity as evidence. The separate n-ary `NominalTree` derives complete
  path injectivity from the separate local `WellTagged` predicate without
  assuming global injectivity.
  It has not been connected to the binary flattening model or proved to
  reflect every accepted production Zig `typeTree` walk.
- `InputRoot` visibility and result wire references are assumed to be the
  already validated relation descriptors. The theorem proves word-order
  agreement for those descriptors, not source parsing or key admission.
- The native projection is modeled as public relation inputs in declaration
  order, followed by first-appearance distinct result wires. This matches
  `record_abi.zig`'s `claimedWords` loop when `validate` has checked input and
  output order. The model does not prove correspondence to those Zig loops.

## Remaining refinement obligations

1. Connect the n-ary path theorem to the binary flattening order and prove
   that native `typeTree` and `matchingPath` acceptance instantiate exactly
   this model. The model does not enforce native node-size and depth limits,
   identifier syntax, canonical JSON, or first-order leaf widths.
2. Prove canonical statement parsing, SHA-256 ABI digest/key binding,
   duplicate-key rejection, M31 range checks, alias equality, and the
   eight-word limit against the production verifier.
3. Prove the Python compiler's typed flattening and source elaboration
   correspond to the validated native descriptor, including private root
   visibility and first-order wire order.
4. Compose this ABI theorem with opened AIR cells and the complete compiler
   correspondence theorem. This module alone is not a proof of STARK
   soundness, confidentiality, or full parser-to-proof correctness.
