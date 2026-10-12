# Record descriptor to statement leaves (ABI v2)

`RecordDescriptorWireRefinementV2.lean` joins two existing models after a
descriptor has been parsed: the whole-descriptor shape and lexical checker,
and the public statement claim checker. The first bridge checks one selected
public input root and requires membership in the descriptor. The second bridge
(`checkDescriptorBinding` and `checkDescriptorClaims`) traverses the entire
descriptor itself, so it has no selected-root membership premise.

For a root with type tree `T`, `expectedLeaves` walks all leaves in declaration
order. Each leaf becomes one statement descriptor with four fields:

| Field | Source in the model |
| --- | --- |
| `path` | Root name, then record field names and tuple indices along the tree |
| `kind` | The tree leaf's `m31` or `bit` tag |
| `width` | The tree leaf's declared word width |
| `wire` | The supplied first-order relation reference for that leaf |

`checkPublicInputBinding` compares the *entire supplied relation leaf list*
with that generated list. It also runs `checkLexicalDescriptor` and requires
public visibility. `checked_public_input_binding` derives exact list equality,
distinct leaf paths, and valid kind/width pairs. This removes a separate
trusted path/shape premise for the selected root. The wire reference function
is supplied by the relation boundary and remains a separate native/compiler
correspondence obligation.

`checkPublicInputClaims` additionally runs the existing `admitClaims` check.
The theorem derives positional path/width/range agreement and repeated-wire
payload agreement. `checked_expected_wire_lookup` shows that first-occurrence
wire projection returns the words of every accepted leaf occurrence, including
aliases.

## Whole public statement

`expectedDescriptorLeaves` filters the descriptor's input roots by public
visibility, emits each public root's leaves in root and tree declaration order,
then appends **all** leaves of the result root. This is the order of the native
`claimedWords` walk. Private roots still participate in descriptor shape,
name, and nominal checks; they contribute no public claims. The result is an
output root and has no input visibility flag.

The executable `checkDescriptorBinding` compares the *entire* supplied
relation leaf list against that projection. It checks exact paths, leaf kinds,
widths, wire references, root order, and result inclusion. The reference maps
are supplied per input root and for the result root. They are explicit
first-order relation boundary inputs, not derived from the type tree.
`checkDescriptorClaims` then checks positional claim shape and value ranges,
plus agreement when public input and result paths refer to the same wire.

For example, take these roots in descriptor order:

```text
x      : public  Pair { value : m31[1] }  -> relation wire 0
secret : private Pair { value : m31[1] }  -> no statement claim
y      : public  Pair { value : m31[1] }  -> relation wire 1
result :         Pair { value : m31[1] }  -> relation wire 1
```

The expected claims are `x.value=[7]`, `y.value=[9]`, and
`result.value=[9]`, in that order. The result and `y` alias wire 1, so the
statement projection with public input wires `[0,1]` and output wire `[1]`
is `[7,9,9,0,0,0,0,0]`. Lean examples check acceptance and reject an inserted
`secret` claim, omitted result, reordered public inputs, changed result wire,
changed result kind or width, and a result payload of `[8]` conflicting with
`y.value=[9]`.

## Hand calculation

Take the checked descriptor input `x : Pair { value : m31[1] }`. The relation
maps its one leaf to wire `0`. The ordered statement descriptor is:

```text
path = [root "x", field "value"]
kind = m31
width = 1
wire = 0
```

The claim `x.value = [7]` passes. Its first-wire projection is `[7]`, and the
eight-slot prover statement is `[7, 0, 0, 0, 0, 0, 0, 0]`. The Lean fixtures
prove the binding is accepted, the input is a member of the checked
descriptor, and the statement projection has exactly those words. Changing
the supplied relation leaf to wire `1` while the relation reference remains
wire `0` fails the binding check. Changing the claim path to `x.other` fails
the claim check.

## What remains external

This model starts from a parsed `NamedLayout`; it does not prove that native
JSON parsing constructs it. It does not derive relation references from S31
source or bind native byte serialization and digest to this model. It also
does not authenticate a prover trace or prove verifier acceptance. The
`root ∈ descriptor.inputs` identifies the selected root only for the older
single-root theorem. The whole-descriptor checker gets its roots directly from
its descriptor argument and covers every *public* input leaf and every result
leaf. Both checks still take relation-wire reference maps as external inputs.
The theorem does not establish that the native validator's `program.inputs` or
`program.public_outputs` produced those maps, or that those lists select the
same wires for final eight-word projection. Those require a separate native
relation correspondence proof. JSON parser/type-code equivalence, canonical
bytes and digest, and proof authentication are also separate obligations.
