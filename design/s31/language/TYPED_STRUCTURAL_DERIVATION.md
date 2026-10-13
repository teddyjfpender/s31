# Typed structural derivations for bounded M31 source

The `typed-structural-derivation.json` package artifact records a small typed
source tree, not just a digest of a relation. Package verification reparses the
exact `.s31` bytes independently of the production compiler, checks that the
artifact contains precisely that tree, then **replays the tree with a second
evaluator**. The replay must reproduce the complete normalized relation and
public ABI sidecar, including every public field path and output alias.

This covers the existing bounded version-1 M31 source grammar and the bounded
version-2 nominal record grammar. It also covers a helper call using wires
obtained from a static tuple, a combination accepted by the production parser
but outside the narrower Lean effects byte parser. That combination receives
this executable certificate and, for the reviewed all-public short-lane
direct-Gate graph, a separate source-bound native fixed-row certificate. It
does not receive a Lean `Program.evaluate` byte-run certificate.

## One rule for three uses

The replay has four relevant value forms: a typed M31 wire, a canonical M31
literal, a product of named typed fields, and a pending arithmetic operation.
Only a `let` binding of a pending operation creates a normalized relation
node. `construct` gathers existing wire references into a product. `project`
checks the product's field name or tuple index and returns the exact selected
wire reference. Neither operation creates a node or a witness cell.

| Source form | Product keys | Selection | Erased result |
| --- | --- | --- | --- |
| `(x, y)` and `p.1` | `"0"`, `"1"` | `project(p, "1")` | existing wire `y` |
| `h(x, y)` and formal `b` | argument slots `"0"`, `"1"` | `project(args, "1")` | existing wire `y` bound to `b` |
| `x.left` on `Pair` | `"left"`, `"right"` | `project(x, "left")` | flattened ABI wire for `x.left` |

The generic Lean theorem `TypedStructuralProjection.project_named_construct`
states this selection rule for any finite product and any checked mapping
from a key to a slot. The Python checker additionally verifies the concrete
source syntax, types, field names, normalized node order, and ABI bytes. The
Lean theorem does not itself prove that the Python parser or native prover
implements that mapping.

### Tuple plus helper, by hand

```s31
fn subtract(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
circuit paired(public x: [m31; 2], public y: [m31; 2]) -> public [m31; 2] {
    let p = (x, y);
    let a = p.0;
    let b = p.1;
    let z = subtract(a, b);
    z
}
```

The derivation constructs `p={"0":x,"1":y}`, projects `a=x` and `b=y`,
constructs the helper's argument product, binds its formal parameters by
projection, and creates one node `z := sub x y`. With `x=[7,11]` and
`y=[3,5]`, the independent value replay obtains `z=[4,6]`. The public ABI is
the eight-word vector `[7,11,3,5,4,6,0,0]`. All products and projections
erase; the normalized relation has exactly one subtraction node.

### Named record fields, by hand

```s31
struct Pair { left: [m31; 1], right: [m31; 1] }
circuit paired(public x: Pair, private y: Pair) -> public Pair {
    let z = x.left .* y.right;
    Pair { right: x.right, left: z }
}
```

The input record `x` is a product of flattened wires
`_s31_abi_input_0` and `_s31_abi_input_1`; `y` uses the next two private
wires. Field projection selects those exact wires. The sole arithmetic node
is `z := mul _s31_abi_input_0 _s31_abi_input_3`. Output constructor fields
may appear in source order `right,left`; the public ABI follows the declared
record order `left,right`. With `x=[2,3]` and `y=[5,7]`, the result is
`Pair {left:14,right:3}`. The public words are `[2,3,14,3,0,0,0,0]`.
The ABI retains the named paths `x.left`, `x.right`, `result.left`, and
`result.right`, including the output alias to the input wire.

## What package verification checks

For admitted conservative text packages, building writes the artifact and
verification requires it. The checker derives and compares:

1. the exact source-byte tree and its complete typed `construct`, `project`,
   helper, arithmetic, assertion, and output steps;
2. the entire normalized relation, including flattened record inputs, node
   order, assertions, and selected output wires;
3. the canonical public ABI sidecar and its record field paths or v1 public
   word layout; and
4. a caller-supplied flat typed assignment, by checking all canonical M31
   inputs, source arithmetic/assertions, claimed outputs, and eight ABI words.

Re-sealed mutation tests change a tuple index, a helper body, or a record
field, then recompute the proposed relation, ABI, and certificate digests.
The checker still rejects each proposal against the unchanged source bytes.
Unsupported expressions, malformed field names, noncanonical words, and
duplicate assignment keys fail closed.

The existing v1 Lean exact-byte source and normalized interpreter checker
remains the formal `Program.evaluate` link for its admitted pure/effectful
grammar. Its effects byte parser now admits one binary M31 helper called after
tuple projections; `CombinedHelperTupleErasure.lean` specializes the
checked-run interpreter theorem to literal two-lane source bytes. Its runtime
audit checks that the source parses to one ordered subtraction, while the
kernel theorem for that concrete parse result remains open. The ordinary
package builder now emits an effects source-relation certificate for the
strict one-helper, two-parameter tuple/projection/call subset. The package
verifier replays it from exact source and relation bytes, and the Lean runtime
gate can use that artifact. Wider helper/product syntax stays on the typed
structural route. The v2
record checker and the common product theorem provide an executable relation,
ABI, and value check, but no v2 exact-byte `Program.evaluate` theorem. Native
fixed-row custody applies only when the separate direct-Gate row checker
enrolls the erased graph; arbitrary native trace authentication, production
parser equivalence, and PCS/FRI soundness remain separate obligations.

For the tuple-plus-helper example above, the short-lane native checker now
replays the exact source-bound structural certificate, derives the SSA graph,
and checks every emitted fixed Gate cell, source address and public-word span.
The sample `x-y` graph has one subtraction source row at fixed trace row 493
in the padded 512-row direct-Gate layout. Its fixed columns, fixed commitment,
and whole-prover cost report equal the flat `let z = x - y` spelling. An
accepted native proof carries that commitment; changing it makes the native
verifier reject. This is fixed-row correspondence conditional on the pinned
native inspector/verifier and PCS. The Lean theorem covers source semantics
through `Program.evaluate`, while native proof soundness and the cross-tool
parser equivalence remain separate.

```sh
PYTHONPATH=src/frontends/s31/python python3 -m unittest \
  src.frontends.s31.tests.python.security.test_structural_derivation -v
```
