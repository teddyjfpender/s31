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
| Natural/field literals, arrays, tuples, records | Field literal only inside canonical `splat`; other forms excluded | Typed static values, product projection and erasure, array shape changes, record ABI |
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

For the pure profile, `formal/s31/S31/Gadgets/Functional/Correspondence/GeneralLinearSSABytes.lean`
independently decodes the complete certificate bytes and enforces canonical
JSON spelling before checking the indexed graph against a separately supplied
Lean source term. `GeneralLinearSSA.lean` proves arbitrary-witness soundness
and honest completeness for its packed M31 arithmetic rows, and their
equivalence to normalized `evaluateNode` steps. This does **not** derive the
Lean term from `.s31` bytes, authenticate native committed rows, or verify
the certificate's SHA-256 identities. A runtime Lean gate checks the actual
five-lane production fixture and rejects malformed byte and graph mutations.
The public-four-lane overlap with the older direct-Gate checker has an
executable join requiring equal indexed graphs; its row theorem still assumes
modeled authentication.

### Narrow source-to-native row admission

`pure-native-rows-certificate.json` joins the checked source-to-relation
certificate to a fresh native direct-Gate topology for **one public**
`[m31; N]` input and output, with `N` from 1 through 3 and 1–16 distinct,
canonically ordered `add`, `sub`, or `mul` SSA nodes. The checker derives a
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
Two source inputs cannot enter this checker yet: the native topology inspector
currently accepts exactly one input. Private inputs, constants, assertions,
noncanonical commutative node order, duplicate expressions that native CSE
would merge, and all other operations are outside this row claim.

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
