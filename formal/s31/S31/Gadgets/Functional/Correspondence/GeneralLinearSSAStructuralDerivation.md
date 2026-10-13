# Bounded typed structural erasure in Lean

`GeneralLinearSSAStructuralDerivation.lean` checks the exact canonical bytes of
`typed-structural-derivation.json` for its `m31-v1` arm. It independently
decodes a typed expression tree, erases it to indexed SSA, parses the `.s31`
source with the existing Lean parser, and requires both routes to equal the
complete normalized relation and source-derived public ABI. The executable is
`s31-general-linear-structural-check`.

For example:

```s31
fn sub(a: [m31; 2], b: [m31; 2]) -> [m31; 2] { a - b }
circuit c(public x: [m31; 2], private y: [m31; 2]) -> public [m31; 2] {
    let pair = (x, y);
    let left = pair.0;
    let right = pair.1;
    let out = sub(left, right);
    out
}
```

The typed tree has two input leaves, a two-field `construct`, two `project`
nodes, and a helper `apply`. Construction and projection select existing wire
IDs; they allocate no arithmetic SSA nodes. The helper binds `a` to input ID
0 and `b` to input ID 1, then its `-` body emits one `sub(0, 1)` node at ID 2.
The result selects ID 2. The check compares this complete ordered graph,
including assertions and public/private input order, with the graph parsed
directly from source bytes and with normalized relation JSON. It separately
compares the order of helper declarations with source text. The typed tree's
step list is replayed in order; a reorder of independent, erased alias steps
may still yield the same graph and therefore pass this semantic checker.

The kernel theorem `checked_relation_graph` states these equalities and the
helper declaration order for every
input accepted by `checkRelation`; it is conditional on the validator result.
`checkPackage` additionally checks source-derived public ABI bytes and the
lowering label; `checked_package_graph` carries the same graph theorem through
that exact package entry point. The decoder requires every field, rejects unknown fields,
canonicalizes JSON spelling, and excludes the record-v2 arm. It bounds source,
tree, certificate, relation, expression depth, lanes, helpers, steps, and SSA
nodes. The executable is a standalone opt-in audit. It is not called by
`verify-release`, `verify-effects-lean`, or the ordinary package verifier.
To apply it to an untrusted package, the caller must independently pin the
package and checker bytes and pass the same captured source, tree,
certificate, relation, and ABI files to this executable.

This does **not** prove that Python emits the same tree for every accepted
source, recompute embedded SHA-256 fields in Lean, cover record-v2 or general
S31 syntax, authenticate native AIR rows, or prove PCS/FRI soundness. Package
pinning owns exact byte identity; Python's package verifier checks the
structural artifact against a separate source replay. The generated audit
compares production, Python, and Lean on several source families and rejects
re-sealed wrong projections, helper bodies, malformed fields, and unsupported
fragments. These controls are evidence of tested parser overlap, not a
universal Python/Lean parser equivalence theorem.
Because production and release admission do not consume this check, they
continue to rely on Python's structural erasure implementation.

Run from `formal/s31`:

```sh
lake build s31-general-linear-structural-check
python3 tests/audit/structural_derivation_lean.py
```
