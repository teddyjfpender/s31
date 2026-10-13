# Static-sum dead-code elimination design

Status: implemented with a focused native proof gate. This pass addresses the unused total constructor
payload identified in the [static-sum security review](../security/STATIC_SUM_REVIEW_2026-10-12.md).

## Scope and semantics

The source evaluator remains strict. It typechecks and specializes the payload
of `Choice::Left(e)` before selecting a `match` arm, even when that arm ignores
the payload. A later graph pass may remove an unobserved node only when the
node's operation is total and deterministic on every well-typed input. This
preserves the obligation of an unused checked inverse, division, overflow,
range check, or assertion. The source effect pass still runs before graph
construction and rejects a partial operation in an inactive dynamic `if` arm.

The first reviewed erasable set is `constant`, `add`, `sub`, `mul`, `add_const`, and
`mul_const`: canonical M31 constants and field addition/subtraction/multiplication are
total. Every other relation operation is retained by default. Extending the
set requires a separate review of its native constraints and input-range
semantics. The pass changes only source files containing an enum declaration;
the independently checked, bounded direct-gate correspondence grammar does
not accept enums and presently reconstructs every arithmetic `let`. A global
pass would therefore change certified normalized relations without updating
their independent checker.

## Algorithm

Given the completed, topologically ordered normalized relation, seed a live
wire set with every public output, both sides of every assertion, and every
wire named by the public ABI descriptor. Traverse nodes in reverse order.
Keep a node when its name is live or its operation is outside the erasable
set. For every kept node, mark its `lhs`, `rhs`, and `selector` operands live.
Reverse the kept list to restore original order. Inputs and public ABI paths,
names, visibility, and output aliases are never rewritten. Remove source-map
entries only for deleted nodes. Revalidate the v2 record descriptor against
the pruned relation before returning it.

The reviewed native `relation.Node` and canonical IR have exactly those three
optional wire operands. `index`, `constant`, `length`, and `rounds` are numeric;
the `repeat` body is a sequence of static steps with numeric constants. The
reference oracle checks this node schema. If a later schema adds an unknown
field or a body shape whose dependencies have not been reviewed, the pass must
leave the entire graph and source map unchanged until that schema is audited.

The backward traversal retains all ancestors of every result, assertion, and
potentially failing or constraining operation. A deleted node has no path to
these roots and is total, so deleting it cannot change accepted assignments
or public values. Conservative roots also retain Boolean gates that constrain
bit inputs and all unreviewed chip/hash/range operations. If a later pass
renames anonymous temporary wires to make relations textually identical to a
handwritten source, it must rewrite every operand, output, ABI leaf, source-map
key, and certificate-facing identity together. This pass does not rename.

## Acceptance checks

The focused Python tests are in
[`test_static_sum_dce.py`](../../../src/frontends/s31/tests/python/functional/test_static_sum_dce.py).
They cover an ignored total payload and transitive dead chain, an unused
inverse that still fails at zero, a live assertion whose arithmetic ancestor
survives, a v2 public-record alias, one-node `repeat` chip shape, and the
unmodified independently certified non-enum fragment. A focused native
direct-chip build, honest proof, changed-claim rejection, and equality of
reported AIR geometry with the direct recurrence run in
[`static_sum_dce.py`](../../../src/frontends/s31/tests/acceptance/functional/static_sum_dce.py).
The enum source and direct recurrence have identical canonical IR digest,
292 raw and 512 padded QM31 rows, and 4,096 preprocessed cells. The enum
source's 61,706-byte native proof was accepted; the changed claim was
rejected. These tests are evidence for examples, not a compiler-correctness
proof.
