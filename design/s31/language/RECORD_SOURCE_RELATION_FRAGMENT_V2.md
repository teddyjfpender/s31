# Bounded independent record source-to-relation check

Status: implemented bounded public record ABI v2 source check.
The [record value refinement](../../src/frontends/s31/python/package/record_value_fragment.py)
also computes this grammar's M31 results from independently parsed source and
flat assignments. Its [46-case corpus](../../src/frontends/s31/tests/acceptance/record_abi/record_source_execution_fragment_v2.py)
compares 23 honest and 23 changed-result cases with Zig `Program.evaluate`.
The [Lean record value theorem](../../formal/s31/S31/Gadgets/Records/SourceValueV2.lean)
composes the checked SSA interpreter across ordered result fields and rejects
swapped or split-alias certificates. These are bounded semantic checks; they
do not authenticate native trace openings or establish full compiler soundness.
The production v2 record compiler, native descriptor parser, statement codec,
and representative native proofs already exist. This increment checks an exact
source fragment without calling the production lexer, parser, elaborator,
specializer, relation validator, ABI builder, or package verifier.

## Claim and boundary

For an accepted source, the independent checker reconstructs the exact
version-2 normalized relation, including its ordered record ABI descriptor.
It compares that object to canonical `source.s31.json`, reconstructs the
canonical `public-abi.json` artifact and its domain-separated descriptor
digest, and checks the source, relation, ABI, and manifest artifact hashes.
Its sole reported capability is `source-to-relation-only`. It makes no claim
about canonical optimization, gate extraction, AIR constraints, PCS/FRI, or
native verifier correctness. An unsupported source fails closed for this
opt-in check; ordinary S31 compilation is unaffected.

The checker belongs in `src/frontends/s31/python/package/record_source_fragment.py`.
Keeping it separate from the v1 checker limits the trusted grammar and avoids
changing an existing release boundary.

## First accepted grammar

* Exactly one nominal `struct R` with one to four distinct fields, each
  `[m31; 1]`. The record name starts with an uppercase ASCII letter and
  cannot collide with a built-in type. ASCII identifiers are bounded and
  cannot be reserved words or production builtin names. The circuit name
  cannot equal the record name. Whitespace and line comments may vary.
* Exactly one `circuit c` with one or two inputs of type `R`, each explicitly
  `public` or `private`, and a `public R` result. At least one input is public.
  The total distinct public input and output words cannot exceed eight.
* Zero to eight sequential `let name = operand + operand;` or
  `let name = operand .* operand;` statements. Each operand is an earlier let
  or a field selection `input.field`. No literals, calls, aliases, assertions,
  recursion, casts, nested records, tuples, or other operators enter this
  first fragment. Inputs and lets may not shadow any declared names.
* The final expression is one `R { field: operand, ... }` with every field
  exactly once. Constructor order may vary; emitted leaves follow declaration
  order. Duplicate output wires appear once in `public_outputs`, in first
  leaf-appearance order. No trailing source tokens are admitted.

This grammar admits useful private arithmetic and aliased record results. It
deliberately starts with width-one M31 leaves so its first assurance result
does not depend on integer range gadgets or vector shape rules.

For example:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit mix(public x: Pair, private y: Pair) -> public Pair {
    let p = x.left .* y.right;
    let q = p + x.right;
    Pair { right: x.right, left: q }
}
```

The independent relation has input wires `_s31_abi_input_0` through
`_s31_abi_input_3` in root and field declaration order; the first two are
public. It has `mul(_s31_abi_input_0, _s31_abi_input_3) -> p` and
`add(p, _s31_abi_input_1) -> q`. The result paths are `result.left -> q`
and `result.right -> _s31_abi_input_1`, so the flat public outputs are
`[q, _s31_abi_input_1]`. The four public proof words are the two input
leaves followed by these two outputs. The private `y` leaves are absent from
the public statement but remain relation inputs and influence `q`.
The current production compiler emits the relation exactly in this order and
the canonical v2 ABI artifact has `boundary_sha256` equal to
`7f753c6d58f189e17c3e57211a408dd23d196c0d818137e28dd114f32362f8d7`.
This value is a differential fixture, not an input to the independent checker.

## Exact checks

1. Tokenize source bytes independently with byte, token, identifier, input,
   field, let, and output bounds. Reject unknown syntax and trailing tokens.
2. Build input leaves, names, nodes, result leaves, output deduplication, and
   type trees directly from the parsed syntax. Reject references to a
   nonexistent or future wire, unknown fields, duplicate fields, and public
   word overflow.
3. Parse relation JSON with duplicate-key rejection and canonical serialization
   checks. Compare recursively with strict JSON type equality; `true` and
   `1.0` must not equal integer `1`. This catches changed operations, wire
   endpoints, visibility, record layout, paths, aliases, and unknown fields
   even if an attacker rehashes the package.
4. Derive `public-abi.json` as `s31-public-abi-v2` with the source-derived
   boundary and SHA-256 of
   `b"s31-public-record-boundary-v2\\0" || compact_sorted_boundary_json || b"\\n"`.
   Require the exact canonical artifact, including its fixed encoding label.
5. Require the package manifest's schema, name, `direct-gate` lowering,
   source-text and relation digests, and artifact hashes to match the bytes
   checked above. The resulting digest report is an audit result, not a proof
   or an admission certificate.

## Focused tests

* Compile independent grammar variants with production `compile_text` only
  on the *other side* of the test comparison: one/two inputs, private
  arithmetic, zero and multiple lets, changed field declaration order,
  constructor order, aliases, and four-field word-budget edge.
* Re-seal a synthetic package after changing node opcode or operands, input
  visibility/order, nominal or field name/order, leaf path/wire, result alias,
  `public_outputs`, descriptor digest, ABI encoding, and artifact hash. Every
  mutation must fail the independent package check.
* Reject duplicate JSON keys, noncanonical JSON, `true` or `1.0` in integer
  slots, boolean/float manifest version tags, duplicate constructor fields,
  shadowing, unknown/future wire, stale keywords such as `enum` and `match`,
  lowercase or built-in nominal type names, a circuit/record name collision,
  trailing tokens, unsupported operations, oversized source, and a
  nine-word public boundary.
* Build one honest package through the normal builder, then run both the
  ordinary package verifier and the independent check against its actual
  emitted artifacts. This catches a mismatch hidden by synthetic fixtures.
* A native direct-gate proof for one accepted source is a separate acceptance
  control: honest proof accepted, changed typed claim rejected, and native
  statement words agree with the independently reconstructed field order.
  It is evidence for this example, not a universal correspondence claim.

The existing broader record corpora and Lean word-boundary theorems remain
separate evidence. This bounded check does not replace them or expand their
claims.
