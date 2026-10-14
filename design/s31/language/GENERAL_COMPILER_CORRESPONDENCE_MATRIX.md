# General compiler correspondence: construct inventory and proof plan

Status: partial. This file separates a source-to-normalized-relation claim
from a normalized-relation-to-native-AIR claim. The former has an executable
independent parser for a bounded M31 fragment; the latter is established only
for narrower direct-Gate packages. Neither establishes native PCS/FRI
soundness. A source digest identifies bytes but does not prove their meaning.

## Production source surface

The production parser's expression variants are `name`, `number`, `field`,
`array`, `tuple`, `record`, `variant`, `match`, `project`, `field_project`,
`let`, `if`, `lambda`, `binary`, `apply`, and `call`. Its declarations include
`use std@1`, `fn`, `struct`, `enum`, and `circuit`; statements include `let`
and `assert_eq`. This is an inventory of implemented syntax, not an assurance
that every syntactically valid program is admissible or total.

| Source family | Independent source-to-relation certificate today | Missing proof obligation |
| --- | --- | --- |
| Circuit declaration, public/private `[m31; N]` inputs, public result | 1–4 inputs, equal `N` in 1–8; public words at most 8 | Other input types and shapes, public ABI v2 records, privacy-to-native binding |
| Names, statement `let`, aliases | Straight-line named wires, at most 32 lets and 16 arithmetic nodes | General lexical scope, shadowing, generated names, nested expression lets |
| Arithmetic | One `+`, `-`, or `.*` per let, with wire operands or canonical `splat<N>(C_m31)` | Nested operator precedence, all other field operations and result shapes |
| Assertions | At most 16 equality assertions between named wires | Arbitrary expressions, result-independent effects, native assertion enforcement |
| Static functions | Up to 8 used pure one- or two-argument helpers, each one arithmetic expression; calls receive named wires | General function bodies, higher-order values, closures, recursive-call rejection, specialization fuel |
| `use std@1` | Exact import spelling is accepted when no standard-library call is used; package lock checked separately | Independently specified standard-library calls and pinned source semantics |
| Natural/field literals, arrays, tuples, records | Field literal inside canonical `splat`; flat 2–4 element tuples of existing equal-length M31 wire arrays, static `.0`–`.3` projection and aliases are source-byte checked and erased before SSA. The bounded v2 record checker covers input field projection and output construction. The Lean record bridge now checks exact source/tree/relation/ABI bytes, decodes the actual typed normalized `Program`, and proves evaluator equality for every assignment. One public one-field add record also has statement and native fixed-row release admission. | Nested products, array shape changes, general record specialization, general record statement ownership, native AIR theorem, and a shared typed certificate across all structural forms |
| Sums, pattern matching, `if` | Excluded | Static constructor semantics, exhaustive branches, dynamic bit selection |
| Lambdas, `Fn`, application | Excluded | Closure capture, polymorphic function values, inlining and name allocation |
| Blinded mode and dynamic builtins | Excluded | Privacy policy, relation op witnesses, circuit/chip boundary proofs |

The independent checker reconstructs the *entire* normalized relation for
its admitted grammar. The builder emits `source-relation-certificate.json`,
and package verification independently reproduces it from exact source and
relation bytes. The indexed `ssa` projection carries every input, node,
assertion and the selected output. `linear-ssa-m31-v1` is emitted only for
the add/sub/mul graph with no assertions or constant arithmetic; otherwise
the artifact lists each unsupported feature and sets the Lean profile to
null. This is an executable trusted checker boundary until the source-byte
parser itself is modeled or verified in Lean.

The separate `typed-structural-derivation.json` artifact now records a typed
source tree and checks one generic construct/project erasure rule across
static tuples, helper parameter binding, and nominal record fields. It
replays the tree independently to the complete relation and ABI, then checks
canonical source values for a supplied assignment.
The bounded `m31-v1` arm now also has a Lean decoder and independent generic
erasure evaluator. For every accepted exact-byte package it requires the
tree's complete ordered indexed SSA, Lean's source-byte SSA, and the parsed
normalized relation to agree, including inputs, nodes, assertions, and
selected output. `checked_relation_graph` proves this conditional join in the
kernel. The strict bounded-M31
[`structural_lean_release.py`](../../../scripts/release/structural_lean_release.py)
entry point now requires it on a pinned package snapshot before native proof
verification, and the full release feature gate requires a real combined
helper/tuple package to pass. The general `s31 verify-release` and ordinary
package verifier do not invoke it; those paths still rely on Python structural
erasure. The
general record-v2 release arm, universal Python/Lean parser equivalence,
native AIR-row theorem, and PCS/FRI remain open. The one-field public add
record has an opt-in pinned row gate; see
[`GeneralRecordV2ProgramAdmission.md`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneralRecordV2ProgramAdmission.md).
See
[`GeneralLinearSSAStructuralDerivation.md`](../../../formal/s31/S31/Gadgets/Functional/Correspondence/GeneralLinearSSAStructuralDerivation.md)
for a hand-worked tuple/helper example and exact gate scope. The production compiler
accepts a helper call after tuple projections; this executable certificate
admits that combination, and the reviewed all-public short-lane direct-Gate
profile additionally receives source-bound native fixed-row checking. The
Lean effects byte parser now resolves one binary M31 helper after tuple
projection, and its exact-byte theorem connects matching source, certificate,
relation, ABI, assignment, and public statement bytes to `Program.evaluate`.
`CombinedHelperTupleErasure.lean` gives the conditional exact-byte interpreter
theorem; its runtime audit checks that the literal two-lane source and the
independent relation parser agree on one ordered subtraction. The kernel
theorem proving that literal parse result remains open. The ordinary builder
now emits and verifies an effects source-relation certificate for the strict
one-helper, two-parameter grammar with source-only tuple lets, projections,
aliases, and helper calls. Wider Python helper/product syntax stays on the
typed structural route. The bounded v2 record case has executable
source/relation/ABI/value checks and an exact-byte Lean source-value theorem.
`GeneralRecordV2ProgramAdmission.lean` checks the actual typed normalized
program against a source-derived graph and proves `Program.evaluate` identity
for every assignment to that checked program. The one-field public add class
also has a pinned statement and fixed-row gate. Universal Python/Lean parser
equivalence and a native AIR theorem remain open. See
[`TYPED_STRUCTURAL_DERIVATION.md`](TYPED_STRUCTURAL_DERIVATION.md).

For the pure profile, `formal/s31/S31/Gadgets/Functional/Correspondence/GeneralLinearSSABytes.lean`
independently decodes the complete certificate bytes and enforces canonical
JSON spelling before checking the indexed graph. The bounded independent
source-byte parser derives the Lean term from exact `.s31` bytes.
`GeneralLinearSSA.lean` proves arbitrary-witness soundness and honest
completeness for its packed M31 arithmetic rows. The
`GeneralLinearSSAProgramEvaluate.lean` bridge now proves that arbitrary
complete pure SSA AIR traces and an aligned named normalized program compute
the same selected output through the actual `Program.evaluate` interpreter.
Its assignment-to-initial-environment correspondence remains an explicit
premise in the inner theorem. `GeneralLinearSSAInputState.lean` now discharges
those premises with a finite checker over a typed assignment. The remaining
join for that inner theorem is from canonical assignment/ABI bytes to that
exact typed assignment.
`GeneralLinearSSAByteRun.lean` now composes both independent byte checks on
the same supplied canonical assignment JSON, runs the actual normalized
interpreter, and proves the accepted pure public claim equals the bounded
source-byte denotation for arbitrary checked M31 inputs. This byte-run gate
still needs production compiler/parser equivalence and native verifier
public-pin ownership to become end-to-end compiler correspondence.
This does **not** authenticate native committed rows or verify the
certificate's SHA-256 identities. A runtime Lean gate checks the actual
five-lane production fixture and rejects malformed byte and graph mutations.
The public-four-lane overlap with the older direct-Gate checker has an
executable join requiring equal indexed graphs; its row theorem still assumes
modeled authentication.

The effectful fragment has a separate named evaluator induction for binary
and canonical M31 constant nodes. It proves every accepted modeled arithmetic
row evaluates to the same value in the actual normalized environment, for an
arbitrary number of steps and lanes, under explicit initial-name alignment
and freshness premises. A single named assertion check is equivalent to its
zero-polynomial constraint once its operands are aligned. The follow-on
theorem handles the entire ordered normalized assertion loop: given an
accepted arithmetic AIR trace, exact named nodes, and a structurally
resolved assertion list, successful `Program.evaluate` forces every
assertion polynomial. It composes with the checked effectful SSA source model
to show that accepted normalized programs preserve source assertion effects.
The effectful Lean source-byte parser also admits flat static tuples of 2–4
existing M31 arrays and canonical constant-index projection. Its local
`project_product_exact` theorem states that a projection selects precisely
the indexed producer ID; construction and selection allocate no SSA node.
The existing exact-byte effectful `Program.evaluate` theorem therefore also
applies to admitted tuple programs. `StaticTupleErasure.lean` specializes the
checked-run interpreter theorem to literal tuple source bytes; the runtime
Lean checker verifies that those bytes are in the admitted grammar. The
independent Python parser reconstructs its complete normalized relation and
certificate; a live paired native build checks equal relation bytes and
complete cost reports against scalar spelling. See
[`STATIC_TUPLE_ERASURE.md`](STATIC_TUPLE_ERASURE.md) for exact scope and
measurements.
The public-output theorem also proves that an accepted evaluator binds its
declared M31 output to the checked effectful source value.
The exact-byte Lean effects parser now resolves up to eight distinct used
one- or two-parameter M31 helpers with a single binary body each. Each call
adds one ordered SSA node after resolving its arguments; unary bodies may
reuse the same input twice. The package checker can therefore apply the
existing arbitrary-graph interpreter theorem to a chain of helpers, including
one with private inputs and source assertions. Sixteen generated programs
cover helper counts 1, 2, 4, and 8 across lane lengths 1–4, comparing
production output, the independent Python relation, and Lean's exact-byte
statement gate. Re-sealed wrong graph bytes fail both independent checkers.
This is empirical parser agreement, not a Python/Lean parser equivalence
theorem. The Python checker admits additional grouped helper spelling that
Lean still rejects fail-closed.
`GeneralLinearSSAEffectsByteRun.lean` now composes the exact effectful
source/certificate/relation/ABI/typed-assignment byte checks and the actual
assertion-checking normalized interpreter. It proves accepted public claims
satisfy the independently parsed source computation and every source
assertion for arbitrary checked M31 inputs. Native AIR row authentication,
public-pin ownership, and PCS/FRI still require separate joins.
Honest completeness holds for the same fragment when source assertions hold,
the typed public output matches the source result, and public ABI word
encoding succeeds; the normalized evaluator then accepts without assuming
an AIR witness or assertion acceptance.
For interpreter soundness alone, the checked certificate also constructs
its deterministic honest arithmetic trace, so successful evaluation implies
source assertion truth and the public output value without a supplied AIR
trace premise. This does not authenticate a prover supplied native trace.
The generic `GeneralLinearSSAEffectsPackageCheck.lean` gate derives arbitrary
bounded effectful M31 inputs and the claim from canonical typed assignment
bytes, checks canonical public statement JSON, and uses the same exact-byte
theorem. The opt-in `verify-effects-lean` wrapper requires external pins for
the package and Lean checker, snapshots the proof inputs, and passes the same
statement bytes to both Lean and the native verifier. Native gate-row custody
and verifier implementation correctness remain separate obligations. The
supplied private assignment is a Lean-checked witness for the public claim;
the native proof is not bound to those particular private witness bytes.
The verifier-side Lean checker receives that full private assignment, so
this opt-in audit does not preserve private-witness secrecy.

### Narrow source-to-native row admission

`pure-native-rows-certificate.json` joins the checked source-to-relation
certificate to a fresh native direct-Gate topology for either one public
`[m31; N]` input with `N` from 1 through 3, or two public equal-length
`[m31; N]` inputs with `N` equal to 1 or 2. The result is one public array
of the same length, and the graph has 1–16 distinct, canonically ordered
`add`, `sub`, or `mul` SSA nodes; the public result selects one of those nodes.
The source may also contain a flat static tuple of already typed M31 arrays
and constant-index projection. That case must pass the independent exact-byte
product parser and the separate Lean effects parser. Product construction and
projection allocate no normalized node, so the same source-derived full Gate
schedule applies. The source bytes are mandatory for product enrollment;
passing only an effects-profile certificate cannot enroll it.
For a static helper call after tuple projection, the separate version-2 native
certificate instead replays the exact source-bound typed structural artifact
and checks the same bounded graph and complete native schedule. A bounded
Lean effects byte-run theorem now covers one binary helper after tuple
projection when a matching effects certificate is supplied. The ordinary
package builder now supplies that certificate for the strict subset, while
the native row checker continues to use the structural version-2 certificate
for this combined case. This does not
upgrade the native certificate's fixed-row-only capability or prove the
Python and Lean parsers equivalent. Native enrollment admits no private
inputs, constants or assertions.
The checker derives a
complete gate schedule from that source graph, then independently compares
every gate address, operation selector, multiplicity and fixed-column cell
with the native topology and component-manifest digests. It also checks exact
public word packing, unused-word zero copies, source address spans, source
row positions and the exported fixed root against the verifier key. Package
verification requires this artifact whenever a direct-Gate text package
falls inside that fragment. The existing direct-Gate correspondence checker
handles its separate four-lane fragment.

This certificate's capability is
`source-relation-to-native-fixed-rows-only`. It relies on the pinned native
inspector, verifier and PCS for the claim that the exported root commits to
the checked columns. It does not prove the witness satisfies the AIR, that
the native verifier enforces the public input claim, or PCS/FRI soundness.
`tests/acceptance/compiler_correspondence/static_tuple_native_rows.py` builds
an all-public tuple package, runs the independent Lean source and assignment
checker, replays the complete 512-row topology, recommits all eight native
fixed columns, and compares that root with the key and a native-accepted
proof's fixed commitment. It also checks that changing that commitment makes
the verifier reject. This is a checked honest proof and tamper control, not an
independent cryptographic proof-opening theorem or authentication of arbitrary
native traces.
The public-only short-lane diagnostic now independently reconstructs the
complete 12×512 uncommitted main trace from the source-certified indexed SSA,
fixed Gate schedule, and one canonical public assignment. Fresh native exports
for one input of one or three lanes and two inputs of two lanes are compared
cell by cell, including all public and unused ABI words. The acceptance test
also recommits those source-derived cells through the installed native PCS,
verifies one honest proof for each shape, and checks that its main commitment
matches the recommitted root. The one-lane sample selects an earlier output
node while retaining a dead suffix. This strengthens the honest proof
correspondence check; it does not derive those main cells from an arbitrary
accepted proof or authenticate PCS openings.
Two public inputs fit within the eight-word ABI only at these lengths:
`2N` input words plus `N` result words must be at most eight. Returning an
input directly, private inputs, constants, assertions,
noncanonical commutative node order, duplicate expressions that native CSE
would merge, and all other operations are outside this row claim.

The older four-package `native_source_cells.json` fixture is historical
evidence: its recorded engine gitlink predates the current pinned engine, and
no CI job rebuilds it. Do not use it as current native evidence until a fresh
four-package regeneration is checked in. The ordered-subtraction native
fixture has its own live CI rebuild and is refreshed with compiler changes.

At this revision, **20 of 147** checked-in `.s31` example files fit this
source fragment; an independent comparison with the production compiler
found **zero** relation mismatches among those 20. This file count is a
coverage indicator, not a probability of correctness. The test corpus also
includes accepted private/assertion/constant cases and re-sealed forgeries.

## Normalized operation inventory

The formal source-binding roster lists 57 normalized relation operations.
The source-to-relation certificate above currently models only `add`, `sub`,
`mul`, `add_const`, and `mul_const`. The Lean `linear-ssa-m31-v1` theorem
models only `add`, `sub`, and `mul`; it has no assertion semantics.

| Operation family | Production operation names | Remaining correspondence work |
| --- | --- | --- |
| Field and control | `constant`, `cast_m31`, `add`, `sub`, `mul`, `add_const`, `mul_const`, `repeat`, `select`, `sum_lanes`, `inv`, `is_zero` | Complete source, normalized-node, witness, AIR, and native-verifier links for each form |
| Boolean and arrays | `array_get`, `array_concat`, `array_slice`, `bool_not`, `bool_and`, `bool_or`, `bool_xor`, `bool_select` | Shape/index proof, Boolean constraints, padding and output selection |
| Hashes | `hash_blake2s`, `hash_blake2s_leaf`, `hash_blake2s_pair`, `hash_poseidon2_leaf`, `hash_poseidon2_pair`, `hash_sha256d_header` | Byte/word semantics, exact chip or circuit schedules, authenticated cross-component boundary |
| Bitcoin and wide integers | `u256_add`, `u256_le`, `u256_add_checked`, `u256_sub`, `u256_sub_checked`, `bitcoin_target_mainnet`, `bitcoin_prev_hash`, `bitcoin_header_bits`, `bitcoin_genesis_hash_mainnet`, `bitcoin_header_time`, `bitcoin_block_work`, `u32_lt` | Limb range and carry constraints, endian layout, statements across chips |
| Fixed integers | `int_view`, `int_add_checked`, `int_add_wrapping`, `int_sub_checked`, `int_sub_wrapping`, `int_le`, `int_mul_wrapping`, `int_mul_checked`, `int_cast_checked`, `int_bit_and`, `int_bit_or`, `int_bit_xor`, `int_bit_not`, `int_shl`, `int_shr_logical`, `int_shr_arithmetic`, `int_rotl`, `int_rotr`, `int_div_rem` | Type-width and signedness preservation, overflow and division side conditions, bit decompositions |

This operation roster is checked against `formal/s31/source-bindings.json`;
adding a relation operation requires updating the inventory and its proof
status. Local algebra theorems for several operations do not by themselves
prove production code emission or authenticated native rows.

## Compositional route to a complete claim

1. **Byte-to-typed-AST admission.** Specify the complete lexical grammar,
   type declarations, visibility, imports and source binding rules in a
   small reference checker. Emit a typed syntax derivation with source spans.
   The checker must reject every unknown token, AST variant and type rule.
   Prove the checker sound against a source-byte semantics in Lean, or reduce
   the trusted base to a verified parser. SHA-256 source identity is not a
   substitute for this step.
2. **Static specialization admission.** Record each function application,
   closure capture, static conditional, tuple/record projection, enum match,
   and builtin expansion as a local derivation. Check that substitutions
   preserve types and semantics, bind generated names, and consume explicit
   fuel. The arbitrary-length SSA theorem can then compose the residual M31
   graph without a separate theorem per source program.
3. **Optimization admission.** Independently check before/after relations for
   dead-code elimination, static-power fusion, CSE, and any future rewrite.
   Preserve assertion and public/private roots, output ABI, and all effectful
   nodes. A compiler fingerprint documents implementation identity but never
   discharges semantic preservation.
4. **Relation-to-native admission.** For each of the 57 operation forms,
   reconstruct the exact emitted circuit/chip rows, fixed cells, public input
   projection, and native verifier evaluations. State lookup balance and
   cross-chip authentication as explicit premises until proven. Compose rows
   by the relation's topological names and output roots.
5. **Proof-system closure.** Connect the authenticated trace/AIR statement
   to polynomial commitments, FRI, transcript challenge order and final
   public claim. This is a separate native PCS/FRI soundness workstream.

The next useful implementation seam is a versioned, typed intermediate
certificate for the source AST and each specialization step. Each rule should
name exact input and output objects, not only hashes. A small independent
checker can validate those derivations while the production Python compiler
continues to optimize. The generic Lean SSA kernel already makes pure M31
graph length and lane count parameters rather than proof-by-example constants;
the parser and lowering boundaries are the remaining obstacle to applying it
to arbitrary source programs.
