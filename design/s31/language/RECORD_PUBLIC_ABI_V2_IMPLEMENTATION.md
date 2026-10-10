# Public record ABI v2: implementation contract

Status: M31-leaf v2 record outputs and record-valued public/private inputs
are implemented for the direct-gate profile. The native verifier checks the
typed statement, embedded relation descriptor, and sealed key digest. Other
proof profiles and non-M31 boundary leaves remain disabled. The input slice
passed its local native proof and mutation acceptance; CI is still pending.

## Minimal first release

The initial native slice admitted nominal records of `m31` leaves, including
nested records and tuples, as the public result. The next slice extends that
same v2 relation to nominal record inputs with inherited public or private
visibility. Retain the existing eight-word public budget. Other
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
struct Pair { first: [m31; 1], again: [m31; 1] }
circuit echo(public x: [m31; 1]) -> public Pair {
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
present only in a prover assignment, never in the public statement. The
CLI accepts a typed root assignment, validates and lowers it to the flat
native witness assignment, and derives the single canonical typed statement.
The verifier admits only that v2 envelope. It constructs its
existing eight-word vector from relation input order followed by ordered
**distinct** public result wires, comparing every alias leaf against the first
claim for that wire. It rejects missing, extra, reordered, duplicated,
mistyped, out-of-range, or mismatched alias leaves. It does not accept a
simultaneous v1 flat map that could contradict the named statement.

Parsing must reject duplicate JSON keys. Zig 0.15's
`std.json.ParseOptions.duplicate_field_behavior` defaults to error; set it
explicitly in the native v2 path and test duplicates in nested leaf objects.
Check canonical bytes separately. Never silently normalize an attacker-supplied
statement into a different statement.

## Source lowering

`Circuit.result` carries a first-order or product type, and the parser admits
nominal record parameters for relation v2. The elaborator counts recursively
flattened public words and
checks the exact result type. After evaluating the circuit result, the
specialist traverses the `StaticRecord` or `StaticTuple` in declaration order
to obtain leaf values and references. Existing `Builder.input` and
`Builder.realize` remain the source of first-order wires. The emitter derives
the ABI descriptor from the typed circuit and those references and finishes
the relation with distinct result wires. No field projection emits an
arithmetic node. Record input lowering constructs static products from fresh
leaf input wires, preserving declaration order and root visibility. The typed
assignment adapter checks nested values before passing a flat map to the
native prover.

The CLI writes only a v2 statement for a v2 package. Package admission
rederives `public-abi.json` from the sealed relation, compares the v2 ABI
digest with the sealed key, and rejects version/profile mismatches. Native
proof verification is the final authority; Python package checks cannot
substitute for native ABI validation.

## Record-valued inputs

Record input support extends relation v2, rather than introducing an unbound
source-only sugar. **Status: implemented in the direct-gate profile; local
native acceptance passed, and CI remains the release gate.** Admit
nominal record roots whose nested fields may contain records or static tuples,
with `m31` leaves only. A circuit may return an `m31` scalar or a record.
When any boundary root is a record, every other circuit input and output leaf
must also be `m31` until additional native type checks are implemented.
For example, the source form is:

```s31
struct Amounts { left: [m31; 1], right: [m31; 1] }
circuit add_secret(public request: Amounts, private mask: Amounts)
    -> public [m31; 1] {
    request.left + request.right + mask.left + mask.right
}
```

The relation should contain four M31 input leaves, with paths
`request.left`, `request.right`, `mask.left`, and `mask.right`. The public
statement claims only the two `request` leaves and the scalar `result`.
The private `mask` leaves enter the proved computation; their names,
layout, and private visibility remain bound in the
v2 relation and key.

The source-level assignment for that example should be one typed object:

```json
{
  "version": 2,
  "public_inputs": {"request": {"left": [3], "right": [4]}},
  "private_inputs": {"mask": {"left": [5], "right": [6]}},
  "result": [18]
}
```

The lowering assigns four distinct first-order input wires in this order:

| Source path | Relation input | Visibility | Public statement leaf |
| --- | --- | --- | --- |
| `request.left` | first fresh input wire | public | yes |
| `request.right` | second fresh input wire | public | yes |
| `mask.left` | third fresh input wire | private | no |
| `mask.right` | fourth fresh input wire | private | no |

The native prover receives those four wire values and the result wire's
claimed value through its existing flat assignment interface. The generated
verifier receives exactly three ordered typed leaves: `request.left`,
`request.right`, and `result`. Its ABI digest commits to *all* four input
paths, including the private root's nominal type and visibility. It never
accepts a second flat public statement beside the typed one.

Each circuit input root has one visibility, `public` or `private`, inherited
by every M31 leaf. Traverse fields in declaration order and tuple elements
by increasing index; allocate a fresh relation input wire for every leaf.
Record construction in the expression environment is static and adds no
arithmetic node. Bind the root name, nominal type tree, tagged path, leaf
wire, type, width, and inherited visibility in the embedded `public_abi`.
The native validator checks that these leaves cover the relation inputs
exactly once and in the same order. Public leaves appear in the sole typed
verifier statement; private leaves appear only in the prover assignment.
Here `private` means absent from the declared public statement. This
transparent direct-gate v2 slice does not add zero-knowledge blinding.

For a source-level typed assignment, lower every root to the ordered flat
wire assignment before calling the native prover. Reject absent or extra
fields, wrong tuple length, noncanonical M31 words, and two names that
claim different values for one output wire. The typed public statement is
derived from that checked assignment and is checked independently by the
native verifier. The output may be a scalar or record; both use one v2 key
and statement schema. Compare a record-input circuit with an identical
manually flattened relation under the direct-gate AIR profile; input
packing, raw and padded AIR rows, and preprocessing cells must match.

The public proof-word budget is the sum of all **public input leaf widths**
plus the widths of **distinct result wires**. Repeating a result wire under
two result paths adds a named claim but no proof word. A result wire that also
names a public input still occupies the existing result proof slot, and the
native verifier checks that both claims agree. Private input leaves consume
no public slots. Generated leaf wire names must avoid every source parameter,
local, and generated relation name. A source input root named `result` is
rejected because the output root already uses that name.

Release gates for this increment are strict typed-assignment validation
(missing/extra fields, tuple arity, duplicate JSON keys, noncanonical M31),
native public/private path and visibility binding, native rejection of
private leaves injected into the public statement, alias equality, a
re-sealed key with a wrong ABI digest, v1 compatibility, and exact AIR and
preprocessing parity with a manually flattened direct-gate relation. Test
both scalar and record results, nested record/tuple inputs, eight-word limit
cases, and generated-name collisions. These controls must pass before the
source parser admits record-valued circuit parameters.

## Required acceptance controls

- Honest nested record outputs and public/private nested record inputs are
  accepted by the independent oracle and generated native verifier. The input
  acceptance must test public/private visibility for nested input fields.
- A named-field program and manually flattened program have the same
  arithmetic rows, padded rows, witness columns, and preprocessing cells.
  Compare under **the same direct-gate AIR profile**; the relation/key bytes may
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
