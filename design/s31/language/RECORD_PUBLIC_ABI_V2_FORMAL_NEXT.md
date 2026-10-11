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

## Ordered n-ary walk to binary first-order layout

The native `typeTree` loop visits fields in descriptor order and tuple
elements from index zero upward. It appends one tagged segment before
descending into a child, checks the next leaf descriptor's complete path,
then advances the leaf cursor. The Python `binding_v2._leaves` and
`record_v2._flatten_value` loops use the same order. A focused three-element
tuple test compares the typed value encoder to the descriptor builder,
including a trailing record field, and checks that swapping two descriptors
is rejected.

`orderedPositions` now models that depth-first n-ary order. The path of each
position is computed by the existing `nominalPath`, rather than being supplied
independently. `orderedRootLeaves_paths` identifies the complete rooted paths
of the ordered leaves with those of the path-injectivity theorem.
`binaryChain` converts any nonempty ordered leaf list into a right-associated
binary product. `binaryChain_flatten` and
`binaryOfOrderedLeaves_flatten` prove that `RecordBoundary.flatten` returns
exactly the original leaf sequence. `orderedRootLeaves_binary_words` applies
this to width-checked M31 blocks, so concatenating the binary leaves gives
the same first-order word vector as concatenating the ordered n-ary leaves.
The binary grouping is a proof device: it preserves leaf and word order and
does not add circuit operations.

For `request: { items: (m31, m31, m31), salt: m31 }`, suppose the leaves
contain `[3]`, `[5]`, `[8]`, `[13]`. Both traversals yield:

```text
path                                   leaf block   first-order word offset
request.items.0                        [3]          0
request.items.1                        [5]          1
request.items.2                        [8]          2
request.salt                           [13]         3

binary grouping: (3, (5, (8, 13)))
flattened words: [3, 5, 8, 13]
```

This bridge is conditional on the accepted descriptor's tree and leaf values
being represented by the Lean `NominalTree` and `WordBlock` values. It does
not itself prove that Zig's JSON parser, `matchingPath`, and `typeTree`
instantiate the Lean model. In particular, the Lean tree has no native
1..64 child bound, depth-32 bound, 1..8 leaf-width bound, or identifier
grammar. Its binary conversion returns `none` for an empty leaf sequence;
native validation rejects empty record and tuple nodes. The Zig validator
checks nominal layout reuse, input wire order/visibility, result shapes,
output first-appearance order, and canonical descriptor hashing separately.

## Precisely what the model assumes

- `WordBlock` models M31 words using an abstract element type. Lean checks
  the payload length against the declared width; it does not prove
  `0 ≤ word < 2³¹−1` for native `u32` words, or that each declared leaf width
  lies in the production range `1..8`.
- `ValidatedPaths` for the earlier binary product model still carries
  injectivity as evidence. The separate n-ary `NominalTree` derives complete
  path injectivity from the separate local `WellTagged` predicate without
  assuming global injectivity.
  `orderedRootLeaves_binary_words` now connects ordered n-ary leaves to a
  binary flattening with identical first-order words. It has not been proved
  to reflect every accepted production Zig `typeTree` walk.
- `InputRoot` visibility and result wire references are assumed to be the
  already validated relation descriptors. The theorem proves word-order
  agreement for those descriptors, not source parsing or key admission.
- The native projection is modeled as public relation inputs in declaration
  order, followed by first-appearance distinct result wires. This matches
  `record_abi.zig`'s `claimedWords` loop when `validate` has checked input and
  output order. The model does not prove correspondence to those Zig loops.

## Remaining refinement obligations

1. Prove native `typeTree` and `matchingPath` acceptance instantiates the
   ordered n-ary model, including node-size and depth limits, identifier
   syntax, canonical JSON, first-order leaf widths, and descriptor cursor
   coverage. Prove `orderedPositions` contains each valid leaf position
   exactly once to carry path injectivity to the complete emitted list.
2. Prove canonical statement parsing, SHA-256 ABI digest/key binding,
   duplicate-key rejection, M31 range checks, alias equality, and the
   eight-word limit against the production verifier.
3. Prove the Python compiler's typed flattening and source elaboration
   correspond to the validated native descriptor, including private root
   visibility and first-order wire order.
4. Compose this ABI theorem with opened AIR cells and the complete compiler
   correspondence theorem. This module alone is not a proof of STARK
   soundness, confidentiality, or full parser-to-proof correctness.
