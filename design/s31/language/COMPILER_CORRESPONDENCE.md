# S31 compiler correspondence: proof boundary and completion plan

The desired theorem is about the bytes produced by the actual S31 toolchain:
for every accepted source file and canonical assignment, the generated native
verifier accepts only proof statements satisfying the source program's meaning.
It must cover every selected circuit, chip, and AIR profile, including the
manifest and public/private interface. The existing Lean development has
valuable local constraint proofs, but it does not establish that theorem.

## Proved compositional fragment

[`CompilerCorrespondence.lean`](../../../formal/s31/S31/Gadgets/Functional/CompilerCorrespondence.lean)
defines an intrinsically typed, four-lane M31 language of arbitrary nested
`+` and `.*` expressions. For every expression and every four-lane input, it
proves:

1. Static lambda application specializes to the exact direct strict field
   graph. The graph accepts exactly the source value for **every** satisfying
   auxiliary witness.
2. Each normalized operation is evaluated by the actual Lean implementation
   of S31's `evaluateNode`, with arbitrary intermediate values.
3. Each matching packed row is checked by the nine QM31 operation residuals.
   The preprocessed opcode is fixed by the expression.
4. The graph, normalized evaluator calls, and AIR rows accept exactly the
   same four-lane result. A forged result cannot pass this local model.

The induction works at any expression depth. It deliberately duplicates a
repeated subtree; the positional SSA theorem below handles `let` sharing.
The normalized relation here is a compositional tree of actual
`evaluateNode` calls, not a proof that the production Python compiler emitted
a correct flattened `Program.nodes` list. The AIR relation covers local packed
arithmetic rows; lookup balance, trace scheduling, public pins, and STARK
verification are separate proof obligations. The existing `TextSquare4*`
modules go deeper into those boundaries for one source-bound example.

## Remaining proof obligations

| Boundary | Completion criterion |
| --- | --- |
| Source bytes to AST | A checked parser relation accounts for tokens, precedence, names, and rejected malformed programs. A digest of source bytes alone does not prove parsing. |
| AST to typed core | Elaboration preserves lexical binding, nominal types, visibility, field and integer semantics, and eager effects. Every rejected dynamic operation has a defined failure outcome. |
| Typed core to normalized SSA | Specialization preserves meaning and failures across arrays, records, assertions, branching, library calls, sharing, and static loops. Every emitted node and edge is covered, with no unbound or duplicate wires. |
| Normalized SSA to circuit/chip plan | Each native compiler profile is proven to implement the same relation, including range constraints, chip inputs/outputs, component ordering, and cost-dependent profile selection. |
| Circuit plan to AIR columns | Every committed row and preprocessed column corresponds to the chosen plan; all reads have authenticated producers, and selectors/multiplicities are fixed or constrained. |
| AIR to verifier statement | The generated manifest, verifying key, public inputs/outputs, ABI version, and transcript bind the same program. A malicious prover can choose arbitrary committed columns, so honest trace-generation checks are insufficient. |

The next boundary is connecting actual source bytes and Python's parser,
elaborator, and serializer to these checked Lean models, then connecting the
normalized `Program` to Zig's circuit/chip plan and generated component
manifest. Source hashes trigger review but do not establish correspondence.

### Checked positional SSA increment

[`SSACertificate.lean`](../../../formal/s31/S31/Gadgets/Functional/SSACertificate.lean)
implements that first checker for the four-lane `+`, `.*`, and static `let`
fragment. A source has de Bruijn variables, so shadowing is explicit. The
deterministic emitter assigns wire `0` to the input and names each later
instruction with the next integer. The checker independently replays all
instructions, rejects a duplicate/nonsequential name or a forward operand,
and compares the selected output's reconstructed term with the elaborated
source. Accepted certificates are proved to evaluate to the source value for
all inputs, both in a direct field interpreter and when every instruction is
run through the executable normalized `evaluateNode`.

For `let square = x .* x; square .* square`, the accepted certificate is:

| Wire | Operation | Operands |
| --- | --- | --- |
| `0` | input `x` | — |
| `1` | `.*` | `0, 0` |
| `2` | `.*` | `1, 1` |

The selected output is wire `2`. Lean checks this certificate and rejects
mutations with a wrong operand, wrong output wire, duplicate name, forward
read, or missing output.

[`SSAEmitterProof.lean`](../../../formal/s31/S31/Gadgets/Functional/SSAEmitterProof.lean)
proves that the deterministic emitter produces an accepted positional
certificate for **every** source in the four-lane add/multiply/static-let
fragment. The induction carries a checked prefix, the next fresh ID, valid
references, and the returned source term. Combined with the certificate
soundness theorem, every emitted instruction trace evaluates to the source
result for all inputs, including through the actual normalized
`evaluateNode` used by the positional interpreter. This theorem covers shared
`let` wires and shadowed de Bruijn variables.

[`SSANamedProgram.lean`](../../../formal/s31/S31/Gadgets/Functional/SSANamedProgram.lean)
models a canonical named serialization into real `S31.Program.nodes`: input
`x`, wire `1` as `w1`, wire `2` as `w2`, and output `w2`. Its static checker
accepts only an exact encoding of an accepted positional certificate and
requires the real `Program.validate` to succeed. Validation enforces unique
names, backward operand resolution, four-lane shapes, and the eight-word
public statement limit. The accepted named checker implies exact node and
output lists plus source-correct positional normalized execution. For the
shared-square program, a separate arbitrary-input theorem evaluates the
actual named `Program.nodes` list with real name lookup and `evaluateNode`;
it computes `x⁴` in all four lanes. Reordered, duplicate, unbound, and
malformed-output examples are rejected by the static checker and by
`Program.validate`.

The generic theorem does **not** yet prove that every canonical named program
executes identically through `Program.environment`; the arbitrary-input
named-execution theorem currently covers the shared-square instance. More
importantly, the model does not prove that Python emits these names or nodes
from arbitrary `.s31` source bytes, that JSON parsing preserves them, or that
Zig lowers them to the corresponding AIR and verifier. Those are explicit
production correspondence obligations, not consequences of source bindings.
The positional emitter is total for all formal source trees; named-program
acceptance also depends on the normalized validator's 128-character name
limit, so a universal named theorem needs an explicit program-size bound or a
different bounded naming scheme.

[`SSAAirRows.lean`](../../../formal/s31/S31/Gadgets/Functional/SSAAirRows.lean)
extends this fragment from one final arithmetic row to the complete emitted
instruction trace. Each instruction carries its fixed add or pointwise-mul
opcode, resolved earlier-wire operands, and all nine packed QM31 operation
residuals. Lean proves an accepted row yields exactly the normalized SSA
value, every valid deterministic step has an honest row, and the result of
**all** accepted rows for any compiled source equals that source's result.
This is a full local arithmetic-row refinement for the four-lane fragment.
Its premise that row operands are the values of earlier addressed wires is
where the native Gate lookup join must be connected; it is not yet a proof of
the production row writer or verifier.
