# Public record ABI v2: implementation contract

Status: design and standalone Python conformance model. **No proof profile admits
this boundary yet.** The current native verifier accepts only relation v1's flat
statement. An implementation must pass every gate below before enabling record
types in a circuit signature.

## Minimal first release

The first native slice admits nominal records of `m31` leaves, including
nested records and tuples, **only as the public result**. Circuit inputs stay
first-order, with their current public or private visibility. The standalone
reference validator also models future record inputs, but that capability
must remain disabled at the source parser until input flattening and native
assignment checks land. Retain the existing eight-word public budget. Other
leaf types require native checks for their additional invariants and are
excluded from this slice. A later version can add `u16`, `bit`, fixed-width
integers, and digest families with explicit semantic tags and range or
Boolean constraints.

The relation retains first-order arithmetic wires. Every input leaf has a
fresh relation input. Every result leaf points to a computed or input wire.
Two result paths **may point to the same wire**. The relation lists each
distinct public result wire once, in first-appearance order. The record ABI
lists every named result leaf, even aliases. Thus grouping and aliasing add
no arithmetic node, gate, AIR row, witness column, or public proof word. The
size of the relation, key, and statement may increase; report those bytes
separately.

For example:

```s31
struct Pair { first: m31, again: m31 }
circuit echo(public x: m31) -> public Pair {
    Pair { first: x, again: x }
}
```

The two paths `result.first` and `result.again` both reference `x`. The flat
relation has one public input wire and one distinct public output wire. Its
two public words are both `x`; the existing eight-word proof statement can
carry those words. There is no equality or copy gate for the second name.
The native verifier checks that both record leaves claim the same value.

## Relation and key

Use `version: 2`; preserve v1 decoding exactly and reject an ABI field on v1.
The v2 relation embeds a `public_abi` object with
`schema: "s31-public-record-boundary-v2"`, input root descriptors, one result
root descriptor, ordered tagged leaf paths, first-order wire names, leaf
types, visibility, and relation shape. A root's canonical type tree records
every nominal record name and declaration-ordered field, including static
tuples. The native relation validator checks:

1. Every input leaf appears once and corresponds exactly to a relation
   input with the same visibility, kind, and length. The relation has no
   unaccounted input wire.
2. Every result leaf references an existing wire with the declared shape.
   The ordered unique result references equal `public_outputs` exactly.
3. Tagged paths are unique and match a traversal of the type tree. The root
   names, nominal type names, field names, and field order are valid.
4. The sum of public input and **distinct public output** words is 1–8. Also
   cap total leaves, nesting depth, and statement bytes. Count aliases in
   the encoded record statement but once in the proof word vector.
5. The compiler emits no relation v2 from a type it did not elaborate, and
   the key records an ABI digest computed from the validated canonical
   descriptor. The native verifier rederives that digest from its embedded
   relation and rejects a different key digest before reading a proof.

Hash the canonical descriptor as
`SHA256("s31-public-record-boundary-v2\0" || canonical-json || "\n")`.
Canonical JSON uses UTF-8 ASCII escapes, sorted object keys, declaration-order
arrays, compact separators, no duplicate keys, and one trailing newline.
Do not depend on a mutable sidecar or on object iteration order. The relation
source digest already binds exact source bytes; the canonical IR hash must
also include the v2 ABI digest so two differently named statements cannot
claim identical compiler identity. Existing v1 IR hashes stay unchanged.

## Statement and assignment

The public v2 statement is a canonical JSON envelope containing `version: 2`,
the ABI digest, and ordered leaves for public input roots and the result root.
Each leaf carries its tagged path and canonical words. Private leaves are
present only in a prover assignment, never in the public statement. Both
prover and verifier decode the same v2 envelope. The verifier constructs its
existing eight-word vector from relation input order followed by ordered
**distinct** public result wires, comparing every alias leaf against the first
claim for that wire. It rejects missing, extra, reordered, duplicated,
mistyped, out-of-range, or mismatched alias leaves. It does not accept a
simultaneous v1 flat map that could contradict the named statement.

Parsing must reject duplicate JSON keys. Zig's standard typed JSON parser
does not by itself establish this property for arbitrary objects, so the
native path needs a checked canonical-byte parser or an explicit duplicate-key
scan before typed decoding. Never silently normalize an attacker-supplied
statement into a different statement.

## Source lowering

Change `Circuit.result` to carry a first-order or product type while keeping
`Circuit.params` first-order for the first native slice. The parser admits a
record or tuple result only for relation v2 and rejects function values
there. The elaborator counts recursively flattened public result words and
checks the exact result type. After evaluating the circuit result, the
specialist traverses the `StaticRecord` or `StaticTuple` in declaration order
to obtain leaf values and references. Existing `Builder.input` and
`Builder.realize` remain the source of first-order wires. The emitter derives
the ABI descriptor from the typed circuit and those references and finishes
the relation with distinct result wires. No field projection emits an
arithmetic node. Record input support later constructs static products from
fresh leaf inputs and requires a separate assignment/visibility audit.

The CLI writes only a v2 statement for a v2 package. Package admission
rederives `public-abi.json` from the sealed relation, compares the v2 ABI
digest with the sealed key, and rejects version/profile mismatches. Native
proof verification is the final authority; Python package checks cannot
substitute for native ABI validation.

## Required acceptance controls

- Honest nested record outputs accepted by independent oracle and generated
  native verifier; record inputs remain rejected. A later input release must
  test public/private visibility for nested input fields.
- A named-field program and manually flattened program have the same
  arithmetic rows, padded rows, witness columns, and preprocessing cells.
  Compare under **the same v2 proof profile**; the relation/key bytes may
  differ because names are intentionally authenticated.
- Two fields sharing one wire cost no extra arithmetic and both must match.
- Change one claimed leaf, swap two same-typed fields, change nominal type,
  change field order, visibility, or wire reference, delete a leaf, duplicate
  a path or JSON key, append unknown fields, or use an out-of-range M31 word:
  native verification must reject. Rehashing a self-authored package manifest
  must not bypass any native check.
- Keep v1 proof acceptance and v1 canonical IR hashes byte compatible.
  A v1 native verifier must reject a v2 statement and vice versa.
- Formalize typed flatten/reconstruct as inverses and path injectivity for
  validated layouts. Then prove public-word extraction corresponds to the
  normalized relation. This is narrower than the full Python-to-Zig compiler
  correspondence theorem, which remains a separate obligation.
