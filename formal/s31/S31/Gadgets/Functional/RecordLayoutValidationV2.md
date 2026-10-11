# Public record ABI v2: checked layout shape

[`RecordLayoutValidationV2.lean`](RecordLayoutValidationV2.lean) models one
validated record or tuple type tree before a public statement is decoded.
The input is a `RawLayout`: a leaf has a kind and width, a record has ordered
named fields, and a tuple has ordered numeric positions. The tree contains no
pre-supplied path-uniqueness proof.

## Worked source and paths

One case in the [13-program corpus](../../../../../src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py)
has this shape:

```s31
struct Request { pair: ([m31; 2], [m31; 2]) }
struct Result { copy: [m31; 2], tail: [m31; 2] }

circuit nested(public req: Request) -> public Result {
    Result { copy: req.pair.0, tail: req.pair.1 }
}
```

The compiler's input descriptor contains a named `Request` root with one
field, followed by a two-element tuple. The independent walk and the Lean
fixture agree on these declaration-ordered leaves:

| Position | Complete path | Kind | Width |
| --- | --- | --- | ---: |
| first input leaf | `root req / field pair / tuple 0` | `m31` | 2 |
| second input leaf | `root req / field pair / tuple 1` | `m31` | 2 |
| first result leaf | `root result / field copy` | `m31` | 2 |
| second result leaf | `root result / field tail` | `m31` | 2 |

For input blocks `[3, 4]` and `[5, 6]`, the public input word vector is
`[3, 4, 5, 6]`. A statement must still name each leaf at its exact path.
The width sequence `[2, 2]` says where the flat vector is split. This layout
check does not itself prove that the circuit output equals the declared
result blocks; that is a separate relation and proof obligation.

## Executable checks and theorem

`checkLayout` recursively checks every record and tuple node has 1–64
children, record sibling names are distinct, no path has more than 32 node
edges, each `m31` leaf has width 1–8, and each `bit` leaf has width one.
`checkRoot` additionally checks that this root has at most 1,024 leaves.
`checkNativeRoot` rejects a tuple at the root, matching the native root
shape rule. Empty nodes, duplicate sibling names, invalid widths, an
oversized node, an overdeep tree, and a tuple root have explicit rejected
Lean fixtures.

`checkRoot_wellTagged` proves that acceptance supplies the local tagging
condition needed for unique complete paths. `checkRoot_leafValid` proves
each accepted position has an allowed kind and width.
`checked_ordered_widths` applies that result to the declaration-order walk
when each supplied word block has the checked leaf's width. Finally,
`checked_nested_public_boundary` combines these facts with the existing
word decoder: if the words are canonical M31 values, the ordered rooted
paths are distinct and exact-width decoding returns the supplied blocks.
Thus the two tree-shape premises of
[`validated_nested_public_boundary`](RecordWordBoundaryV2.lean) are derived
from an executable raw-tree check rather than supplied as assumptions.

The [generated Lean corpus](GeneratedRecordLayoutCorpusV2.lean) is pinned to
the 13 source programs. It checks 28 compiler-emitted roots, their ordered
paths, and their widths. The
[generator](../../../scripts/check_record_layout_corpus_v2.py) independently
walks the type tree instead of trusting emitted leaf paths. Four mutations
of those paths or leaf declarations are rejected before generation. Run its
default mode to compare the checked-in fixture against the compiler output;
`--write` is an explicit review operation. The separate
[`general_statement_refinement_v2.py`](../../../../../src/frontends/s31/tests/acceptance/record_abi/general_statement_refinement_v2.py)
can run a 91-case native statement-parser corpus, including 65 malformed
claims; the layout fixture does not rerun native Zig.

## Boundary of this result

These theorems start with an already parsed tree. They do not prove the Zig
JSON parser or `typeTree` creates the same `RawLayout`, validates identifier
syntax, or matches leaves to relation wires. `checkRoot`'s 1,024-leaf bound
is **per root**; Zig also checks 1,024 leaves across all roots. Native nominal
record-name consistency across roots and the private-input prohibition on
`bit` leaves remain separate checks. The theorem requires canonical M31
words as a premise and does not establish the tighter public-bit value range
`0..1` or canonical JSON encoding. It also does not establish ABI digest
binding, proof authentication, AIR acceptance, or polynomial commitment
soundness. The [statement refinement](RecordStatementV2.md) and
[word boundary](RecordWordBoundaryV2.md) document adjacent proved pieces.
