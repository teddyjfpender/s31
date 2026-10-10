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

### Certificate-backed path to the production theorem

The practical route is to make the Python compiler an **untrusted producer of
a checked artifact**. A separate small checker receives the exact `.s31`
source bytes, proposed typed syntax, normalized relation, chosen chip-call
plan, and generated component roster. It must reparse the source bytes (or
check a token stream against them), replay typing and specialization, and
compare every emitted node, address, visibility, public claim and selected
AIR component. A digest or sample execution cannot replace this check.

The checker's acceptance theorem should have this shape:

```text
check(source_bytes, certificate, relation, chip_plan, roster) = accept
  → ∀ canonical_assignment,
      relation_accepts(canonical_assignment)
      → source_denotation(source_bytes, canonical_assignment)
```

The theorem must include failures and assertions, not just successful
arithmetic results. Its AIR refinement must quantify over arbitrary prover
columns satisfying constraints; honest trace generation alone is too weak.
An explicit proof-profile tag and version belong to the certificate so that
a theorem for the direct Gate circuit cannot be reused for a chip profile.

The generated verifier must rerun or embed the checked artifact's result,
bind its digest into the key and transcript before commitments, and construct
the PCS component schedule from that same validated roster. Until a
byte-level checker is part of the shipped verifier path, the Lean four-lane
fragment below is a local semantic proof and native acceptance tests are
empirical controls. They do not establish the theorem at the top of this
document for all `.s31` files.

### Bounded byte-to-SSA increment

[`SSATextBytes.lean`](../../../formal/s31/S31/Gadgets/Functional/SSATextBytes.lean)
implements a byte lexer and parser inside Lean for one much smaller source
grammar: ASCII identifiers and whitespace, `//` comments, one public
`[m31; 4]` input and output, and 1–16 canonical binary `let` operations.
The parser consumes all tokens, resolves each named operand to a prior wire,
and rejects duplicate names, forward reads, reversed commutative operands,
and repeated operations. It constructs the source meaning from those parsed
instructions, rather than trusting a separately emitted source term. Its
general theorem has this precise form:

```text
(parseBytes bytes).map Parsed.certificate = some certificate
  → ∀ four_lane_input,
      executeNormalized certificate four_lane_input
        = denotation bytes four_lane_input
```

The generated shared-square fixture proves the premise by Lean computation
for its exact 207 source bytes. It also checks the parsed circuit and public
names and proves that a literal opcode change in the bytes yields a different
certificate. [`SSANormalizedBytes.lean`](../../../formal/s31/S31/Gadgets/Functional/SSANormalizedBytes.lean)
adds an exact canonical JSON byte encoder from the parsed names and
instructions. Its checker admits a source/normalized pair only if every
normalized byte equals that expected encoding, then proves the resulting
certificate computes the source-byte denotation on every input. The fixture
kernel-checks the actual exported `source.s31.json` bytes and rejects literal
normalized-opcode and public-output changes. Its final local AIR claim uses
this two-file check. [`SSAAirColumnCells.lean`](../../../formal/s31/S31/Gadgets/Functional/SSAAirColumnCells.lean)
derives the eight selector, address, and multiplicity cells for each source
operation from the same certificate and checks exported native column values
at their grouped AIR rows. The shared-square instance checks rows 502 and
503, including two uses of the first result and four public-unpack uses of
the last result; selector, address, sampled-row, and multiplicity mutations
fail by kernel reduction. `SSAOutputAirCells` then checks eleven exported
cells for all four public-output masks, three inverse multiplications, and
four ABI copies against the same source-selected output and native allocation
formula. The fixture still relies on the outer exporter to
bind the embedded arrays to the package, and Lean does not compute the
displayed SHA-256 digests. The total add-row count and source-independent
rows remain package-checker premises, and committed-column authenticity is
still a PCS obligation. The Python checker accepts some Unicode whitespace
that this ASCII Lean parser rejects; their full parser equivalence is not
proved. Nor is equivalence between the
production JSON readers and the exact Lean byte encoder. Production Zig
compilation, native Gate lookup authentication, committed AIR columns, and
PCS binding remain separate proof obligations.

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

[`SSANamedExecution.lean`](../../../formal/s31/S31/Gadgets/Functional/SSANamedExecution.lean)
closes the generic **modeled named-execution** step. It maintains a relation
between every checked positional term and the value found at its canonical
name in the real normalized environment. For every checked certificate whose
finite names are collision-free, the actual `Program.nodes` fold using
`evaluateNode` returns the source value on all four-lane inputs. The theorem
then runs the real `Program.environment` on any assignment whose public input
has been accepted as those four lanes. A finite `namesDistinct` test is part
of `checkBounded`, so successful checking supplies the name premise rather
than relying on an axiom. For **every** supported source term, the deterministic
emitter and canonical named program pass that checker when this finite name
test and `Program.validate` succeed. The shared-square program is a concrete
accepted witness, so the theorem is non-vacuous.

[`SSANamedPublicClaim.lean`](../../../formal/s31/S31/Gadgets/Functional/SSANamedPublicClaim.lean)
extends the same checked fragment through normalized `Program.evaluate`.
When an assignment is accepted, its declared public output has the source
value at the canonical output name. The proof uses the actual output-checking
path, including the value equality check, and an accepted public input whose
four lanes are the source input.

These bounds matter: `Program.validate` limits names to 128 characters, and
the modeled `wN` names cannot be valid for all mathematically unbounded source
trees. The model still does not prove that Python emits these names or nodes
from arbitrary `.s31` source bytes, that JSON parsing preserves them, or that
Zig lowers them to the corresponding AIR and verifier. Those are explicit
production correspondence obligations, not consequences of source bindings.

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

[`SSALocalPipeline.lean`](../../../formal/s31/S31/Gadgets/Functional/SSALocalPipeline.lean)
composes these modeled checks for **any** accepted bounded certificate in the
same four-lane fragment. Every such certificate has an honest complete row
trace. Given arbitrary accepted arithmetic rows, an accepted normalized
`Program.evaluate` result, and the checked source/certificate/program triple,
the selected row value, named environment output, and accepted public output
all equal source denotation. The row model reads operands from the addressed
prior values; native Gate authentication and row emission remain independent
proof obligations.

### One source-bound end-to-end arithmetic instance

[`TextSquare4CompilerChain.lean`](../../../formal/s31/S31/Gadgets/Functional/TextSquare4CompilerChain.lean)
checks that the generated normalized `Program` for
`functional_square4.s31` is exactly the accepted shared-let SSA encoding after
renaming `w1` to `_s31_i1_0` and `w2` to `result`. It checks the complete
concrete program equality, including its ordered nodes, inputs, output, and
metadata. The two shared multiplications compute `x²` then `x⁴`; expanding
the repeated square without a let emits three multiplications. The named
`Program.nodes` fold and both packed QM31 arithmetic AIR rows accept a claim
exactly when it equals the formal source value. Successful normalized
`Program.evaluate` acceptance binds the public `result` to that same value.

This is a checked **single compiler output**, with the generated program
recorded as Lean data. It does not prove that the Python parser and emitter
produce this record from arbitrary source bytes, that JSON preserves it, or
that Zig lowers it into the native AIR and transcript for every profile.
