# Record descriptor to statement leaves (ABI v2)

`RecordDescriptorWireRefinementV2.lean` joins two existing models after a
descriptor has been parsed: the whole-descriptor shape and lexical checker,
and the public statement claim checker. It checks one selected public input
root at a time. The theorem requires that the root actually belongs to the
checked descriptor's input list.

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
`root ∈ descriptor.inputs` premise identifies the selected descriptor root;
the executable binding check then covers every emitted leaf for that root.
Both that membership premise and the `refs` relation-wire map are external to
the executable check. The result and all other input roots require their own
binding checks; this theorem makes no whole-statement coverage claim.
