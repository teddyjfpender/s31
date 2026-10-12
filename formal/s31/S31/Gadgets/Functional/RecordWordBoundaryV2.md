# Public record ABI v2: from named leaves to public M31 words

The [Lean module](RecordWordBoundaryV2.lean) closes one semantic gap between
the nested ABI path walk and the flat verifier statement. A validated record
tree yields leaves in depth-first declaration order. Each leaf declares a
width. The module proves that these widths recover exactly one grouping of
the flat public words, consume the entire vector, and preserve canonical M31
range checks.

## Hand-written nested example

Imagine the result type below. `items.1` and `items.2` are different named
leaves that intentionally point at the same relation wire.

```text
record Result {
  items: ([M31; 2], M31, M31),
  salt: M31,
}

source path                  wire    named claim
result.items.0              0       [3, 4]
result.items.1              1       [5]
result.items.2              1       [5]
result.salt                 2       [6]
```

The four **path tags** are unique, even though two leaves share wire 1.
The output descriptor walks all four leaves, so its named claim sequence is
`[[3, 4], [5], [5], [6]]`. The verifier's proof-word vector includes each
result wire at first occurrence only: `[3, 4, 5, 6]`. Its distinct wire
widths are `[2, 1, 1]`. Parsing those four words by those three widths
recovers `[[3, 4], [5], [6]]` with no remainder. A changed second alias
claim such as `[7]` is rejected even though the proof word appears once.

The parser rejects a zero or greater-than-eight leaf width, an extra word,
a truncated final word, and any public word `>= 2147483647`. That number is
the M31 modulus, so the canonical representatives are `0` through
`2147483646`.

## What is proved

- `takeExactly_sound` and `decodeWidths_sound`: successful decoding neither
  invents nor loses words, and each block has its declared width.
- `width_boundaries_unique`: one width sequence and one flat vector have
  only one leaf grouping.
- `admitPublicWords_sound` and `admitPublicWords_complete`: executable exact
  decoding agrees with checked leaf blocks, enforces widths 1–8, and enforces
  canonical M31 words.
- `nested_paths_and_words_sound`: local uniqueness of sibling field tags
  gives unique complete paths, while width decoding returns leaf payloads in
  the same depth-first order for **any** finite nested record/tuple tree.
- `validated_nested_public_boundary`: combines unique rooted paths with
  executable exact decoding under explicit local-tag, width, and canonical
  word validation premises.
- `ordered_result_words_admit` and `ordered_claims_exact`: result proof words
  follow first wire occurrence, while every named leaf is checked against
  its own referenced wire.

The Lean input is an already validated nominal type tree, ordered leaf
widths, and wire references. This module does **not** prove that the Python
compiler or Zig JSON validator produces those inputs, that canonical JSON
bytes or the SHA-256 descriptor digest match this model, or that the native
verifier authenticates the decoded values. Those are separate refinement and
cryptographic soundness obligations. The [pinned Pair refinement](RecordPinnedPairAliasV2.lean)
tests one exact serialized descriptor; the present theorem is general over
nested tree shape but starts after parsing and validation. In particular,
tree validation separately rejects empty nodes and enforces depth/leaf-count
limits. Public `bit` leaves also need the 0/1 range check modeled by
`TaggedPublicBlock` in `RecordAbiV2.lean`; canonical M31 range alone is not
enough for a bit.
