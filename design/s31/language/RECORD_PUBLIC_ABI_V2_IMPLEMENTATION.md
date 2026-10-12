# Public record ABI v2: implementation contract

Status: M31-leaf v2 record outputs and record-valued public/private inputs
are implemented for the direct-gate profile. Source-bounded extensions for
the public one-call direct-chip profile and the experimental one-to-eight-call
mixed profile are implemented and passed local native acceptance. The native verifier
checks the typed statement, embedded relation descriptor, sealed key digest
or embedded source identity, and source-derived component roster. Private
record chip endpoints and other proof profiles remain disabled. Direct-gate
admits public `bit`, scalar `u8`, and `[u16; N]` leaves (`1 ≤ N ≤ 8`). The
`u8` and `u16` input limbs have in-circuit Boolean decomposition and
reconstruction constraints; a result of either type must alias a public input
of the same type. Native edge-value and changed-claim acceptance, focused Lean
models, and independent reviews passed locally. Private `bit`/`u8`/`u16`
leaves, derived narrow-integer results, and narrow leaves in chip or mixed
profiles remain disabled. Full production parser-to-verifier correspondence
and broader soundness review remain release gates.

The [general Lean word-boundary model](../../../formal/s31/S31/Gadgets/Functional/RecordWordBoundaryV2.md)
now proves that validated nested record/tuple paths are unique and that
declared widths decode one exact canonical M31 public-word vector. It also
models distinct named output paths that share a proof wire. The theorem starts
after type-tree and wire-reference validation; Python/Zig descriptor parsing,
canonical bytes and digest, native verifier refinement, and the public `bit`,
`u8`, and `u16` range rules remain separate obligations of this particular
word-boundary theorem. Their focused models and native controls are described
in the [record guide](../../../src/frontends/s31/docs/records.md).

## Source-bounded public one-call chip

The direct-chip v2 slice accepts exactly one public `m31[4]` flat input wire,
one `repeat` node containing `square; add_const`, 16–32768 power-of-two
rounds, and one public `m31[4]` result wire. One or both endpoints may be
wrapped by nominal records; duplicate result fields may alias the result
wire. The eight proof words remain four initial and four final M31 values.
All named paths and aliases are checked by the same native v2 statement
parser used by direct-gate. Any private input or private chip boundary is
rejected before proof decoding. The source-derived v2 descriptor is validated
against the flat relation and hashed into the canonical IR identity.

The key schema is `s31-verification-key-direct-record-chip-v2`. It carries
both `public_abi_sha256` and the typed one-call
`manifest_precommitment_sha256`. Before reading proof bytes, the verifier
regenerates the ABI digest, circuit topology, AIR roster, preprocessed data,
manifest digest, and expected circuit identity from its embedded source and
pinned AIR. The manifest digest includes the source and canonical IR digests;
the latter includes the ABI digest. The effective source digest bound to the
existing public one-call proof transcript includes the manifest digest. A
version-1 chip proof cannot be reinterpreted as a version-2 record proof for
the same arithmetic graph. The underlying chip AIR and proof envelope remain
the one-call public profile; no extra arithmetic rows are introduced by
record grouping.

The [native acceptance script](../../../src/frontends/s31/tests/acceptance/acceptance_record_chip_v2.py)
passed locally on the pinned engine revision. It compares flat and
record AIR geometry, verifies both proofs, rejects changed paths, alias
claims, public values, noncanonical words, rehashed sidecars, independently
resealed bad ABI/manifest keys, a visibility-swapped embedded descriptor,
and cross-version proof replay. The mixed extension has a separate
[N=1 and N=8 native gate](../../../src/frontends/s31/tests/acceptance/mixed_boundary/record_general_v2.py)
for changed public words, paths, duplicate keys, and statement/assignment
mismatch. The mixed-general CI job passed on the preceding PR head; changes
after that head still require their own integrated run.

## Minimal first release

The initial native slice admitted nominal records of `m31` leaves, including
nested records and tuples, as the public result. It grew to admit record
inputs with inherited public or private visibility while retaining the
eight-word public budget. Public `bit` leaves erase to one M31 wire and the
native typed statement parser checks their claimed value before proof
decoding. Public scalar `u8` and `[u16; N]` leaves add arithmetic range gates
on their input wires; their results must alias same-type public inputs. Private
narrow integers, derived narrow-integer results, other fixed-width types, and
digest families await their own boundary rules.

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

The native canonical JSON writer caps nesting at 128 containers. The v2 type
tree itself permits at most 32 record or tuple edges; even with each edge's
field and array wrappers, a valid descriptor remains below the writer cap.
This limit also applies before canonical-byte comparison of a verifier
statement, so a deeply nested malformed path is rejected as an invalid
statement before proof decoding. The cap is a resource bound, not a change to
the ordered leaf or proof-word semantics.

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
