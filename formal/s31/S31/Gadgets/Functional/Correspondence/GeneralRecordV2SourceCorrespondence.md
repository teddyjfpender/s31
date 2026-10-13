# Exact source correspondence for the bounded record v2 fragment

`GeneralRecordV2SourceCorrespondence.lean` reads the actual `.s31` bytes. It
accepts one nominal record with one to four `[m31; 1]` fields, one or two
record inputs with at least one public input, one to eight arithmetic `let`s
(`+` or `.*`), and a result constructor containing every declared field. A
flat `let R { field: local, other } = input;` may bind a subset of fields from
an already evaluated record input; at most sixteen distinct bindings enter
the checked grammar. Each projection retains the input field's original flat
wire, while the typed structural certificate records the ordered aliases.
Computed pattern right sides and nested products remain outside this grammar
because omitted fields may carry eager effects. The
checker accepts ASCII whitespace and `//` comments and rejects all
other syntax. This is a bounded class, not the full S31 text language.

For example:

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit paired(public x: Pair, private y: Pair) -> public Pair {
    let z = x.left .* y.right;
    Pair { right: x.right, left: z }
}
```

The checker independently names the four input leaf wires in declaration
order. The public `x` fields are `_s31_abi_input_0` and
`_s31_abi_input_1`; the private `y` fields are `_s31_abi_input_2` and
`_s31_abi_input_3`. Field projection selects an existing wire and emits no
arithmetic node. The sole normalized node is:

```json
{"name":"z","op":"mul","lhs":"_s31_abi_input_0","rhs":"_s31_abi_input_3"}
```

The constructor writes fields in source order `right, left`, but the public
ABI and normalized result use declared field order `left, right`. Their leaf
references are therefore `[z, _s31_abi_input_1]`. Given `x=(2,3)` and
`y=(5,7)`, the source record result is `(14,3)` over M31. The eight public
proof-word slots are `[2,3,14,3,0,0,0,0]`; the private values are witness
values rather than public words. A repeated result reference is one
normalized output wire even when two distinct named paths point to it.

The Lean executable checks four package artifacts together:

1. It lexes the exact source bytes and resolves root fields and earlier
   locals.
2. It reconstructs the complete typed structural `program` and compares it
   with the canonical structural certificate JSON.
3. It reconstructs the complete normalized relation v2 JSON, including
   inputs, arithmetic nodes, distinct result wires, and the public record
   boundary. It compares that object with the canonical relation bytes.
4. It compares the ordered record boundary with the canonical public ABI v2
   sidecar. Unknown fields, alternate JSON spelling, trailing source tokens,
   missing fields, and forged projections fail.

`checked_source` proves that success retains the independently parsed source.
`checked_relation_json` and `checked_expected_graph` prove that success joined
the canonical relation bytes to the source-derived graph. `eval_node_output`
defines the M31 addition/multiplication value step; `same_result_wire_same_value`
states the alias consequence for a pair of result references.
`flat_pattern_alias_operand` proves that a valid bound local keeps its source
name in the structural expression while the arithmetic operand points to its
existing input wire. The general exact-byte source checker reconstructs
ordered projections and the complete relation; `checked_expected_graph`
applies to every source it accepts. The static Program admission checker then
compares the source-derived graph with the actual typed `Program`. The focused
corpus checks duplicate binders, wrong nominal type, computed pattern input,
field swaps, and resealed package mutations through that executable checker.

`checkSourceTopology` is a second, name-only check used by the typed-program
admission gate. Its successful result is stored in `Static` and proves that
the independent scalar source evaluator can run for every canonical input.
This rejects unavailable operands and result references even if a future
parser change were to admit them.

Build and run the focused gate:

```sh
cd formal/s31
lake build s31-general-record-v2-source-check
cd ../..
python3 -B formal/s31/scripts/check_record_v2_source_correspondence.py
```

The focused corpus includes five compiler-produced packages, including a
renamed/subset flat pattern and patterns interleaved with arithmetic, and
twelve negative packages. The new adversarial
cases reseal a wrong pattern field, substitute a private input projection with
a public one, or change the arithmetic operand in the normalized relation.

## Boundary of this result

The checker compares JSON objects using Lean's `Json` equality routine; the
theorem records that executable comparison. Lean validates the syntax of the
three SHA-256 fields but does not recompute those hashes. Existing package
snapshot code must bind the exact artifact bytes and recompute hashes.

This module does not establish production parser equivalence for all S31,
prove the native direct-Gate row emitter or public statement parser equivalent
to this value model, or authenticate a committed AIR trace with PCS/FRI. The
v1 M31 structural release verifier does not admit record v2. A record v2
release needs an explicit v2 admission path joining this checker to the
native rows, ABI statement, and package hashes; adding this Lean executable
does not silently widen that release class.
