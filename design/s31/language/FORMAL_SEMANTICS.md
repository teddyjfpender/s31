# S31 normalized semantics and constraint proofs

## Contract

Formalize every operation currently admitted by S31 relation IR v1, including
failure cases, fixed-width signed and unsigned arithmetic, array shapes,
hash encodings, static repeats, assertions and the eight-word public ABI.
The normalized relation is the semantic boundary; text specialization and
canonicalization must agree with it but are not assumed formally verified.

Reuse the existing Lean M31 model and local proof infrastructure through a
local Lake dependency. Keep S31 specifications and proofs in a separate
`formal/s31/` package, grouped by semantics, gadgets and evidence. Do not copy
field implementations or import the whole RISC-V frontend theorem surface.
The toolchain stays pinned to the existing Lean 4.29.0.

Every admitted operation must have an executable semantics and an explicit
coverage entry. New operations, changed source identities or missing proofs
must fail the gate. Hash constants are generated from pinned repository assets
and checked byte-for-byte. No uninterpreted hash callback may be presented as
complete executable semantics.

## Proof obligations

For individual arithmetic constraint gadgets, prove both soundness for
arbitrary satisfying auxiliary witnesses and completeness by constructing
honest witnesses. Keep integer range premises explicit and prove the bridge
from bounded M31 equations to integer equations. Prove Boolean selection,
zero testing, inversion, carry/borrow chains, checked/wrapping arithmetic,
signed interpretation, comparison, array operations and public bindings.
Reuse the existing Poseidon S-box residual proof where applicable and compose
round/encoding semantics through the same local arithmetic primitives.

The equations in a formal gadget must be inspectably matched to production
gadget equations. A value interpreter or equality-by-definition theorem alone
cannot certify production compilation. Coverage distinguishes executable
operation semantics, proved local constraint relations, and production
compiler/AIR correspondence. Claims remain bounded to actually checked
theorems; arbitrary-trace LogUp composition, alternative AIR lowerings,
Zig machine-code correctness, STARK soundness and zero knowledge remain
separate obligations.

The QM31 operation AIR row is modeled by its nine literal polynomial residuals
in `formal/s31/S31/Gadgets/Air/Qm31Ops.lean`. Its row theorem proves one-hot
opcode selection and exact packed outputs for arbitrary row values. A separate
theorem relates the add and pointwise-multiply rows to S31's normalized
four-lane M31 evaluator. This is local AIR correspondence, not a proof of
trace construction, Gate lookup/LogUp consistency, compiler emission, or the
STARK verification protocol.
The source-to-row composition theorem covers typed functional pointwise
expressions of any array length. It equates strict graph acceptance with
existence of every packed AIR row witness carrying the same active result for
the final arithmetic operation, including a short final chunk with arbitrary
unused input-lane values. AIR rows for operand subexpressions are separate.
The direct conditional has a separate row theorem: one shared complement row,
then two scalar products and an addition per packed word, agree with the
normalized `select` node across all array words, provided its selector is
constrained to zero or one.
Lean also checks that selector `2` can satisfy those arithmetic rows with an
interpolated output, so the Boolean premise is indispensable.
The direct selector self-product row now proves that premise for **every**
four-coordinate QM31 witness. Lean builds the quadratic field tower,
including the nonsquare facts for `-1` and `5`, and proves its multiplication
agrees with the AIR's four-coordinate formula. Binding the selector wire's
base coordinate to the source M31 input gives the exact normalized `select`
result for the compiler-shaped row schedule. Actual Gate address wiring
remains a separate global obligation.
Lean separately proves the five compiler-shaped Boolean operation row
schedules sound and complete for base-field encoded Boolean inputs. All
intermediate row witnesses are quantified. Their operand producers and Gate
address wiring remain separate global obligations.
The ordinary `checkedBitWord` path is modeled too: Lean proves that the
compiler's `anchor + value = anchor` row enforces zero for an arbitrary
anchor, and that its multiply/subtract/zero row sequence accepts exactly
canonical QM31 bits. A bound source M31 value is consequently Boolean.
The `is_zero` gadget has a separate exact row proof: for any QM31 input,
the two zero assertions and inverse equation bind its indicator to one
exactly for zero, with honest witnesses in both cases. Restricting those
rows to canonical M31 values agrees with the normalized `is_zero` node.
Packed inversion now has a matching row theorem too: the pointwise product,
active-lane mask subtraction, and zero assertion admit a witness exactly
when every active M31 input is nonzero; each claimed lane is the field
inverse. This holds for arbitrary array lengths and final-word padding.
Packed lane extraction has a matching one- or two-row theorem: the
pointwise unit mask and optional basis-inverse multiply return precisely
the chosen base-field value, even with arbitrary unused packed coordinates.
The equality component now has a separate exact Gate-event model. Given
closed events and unique values at produced addresses, its two lookups
force equality of their addressed operands. This composes with the masked
short-word arithmetic rows to prove every active lane of a partial-word
assertion agrees. The resulting post-lookup array theorem covers any length.
The `mix4` diffusion step now composes the proved `sum_lanes` rows with a
QM31 broadcast multiply and a packed add. Its local rows agree with the
executable normalized repeat-body step for all four-lane inputs.
For `sum_lanes`, Lean models the final-word mask, pairwise packed addition
passes, QM31 dual projection and base-coordinate extraction. The resulting
row relation is sound and complete against the normalized `sum_lanes` node
for any nonempty array, including the compiler's one-lane alias path.
An abstract Gate relation model now proves that exact multiset balance plus
unique produced values per address forces row operands to equal their
preprocessed-address producers. The production compressed LogUp argument is
still an explicit assumption, not a theorem of this package.
The unique-producer premise follows in the Lean model from distinct row output
addresses and disjoint external producers; the abstract straight-line
`start + index` address pattern is proved distinct. A proof that the Zig
builder follows this allocation pattern for each compiled S31 program is
still required.

## Evidence and hygiene

Build every S31 Lean source, audit theorem axioms, reject proof escapes and
check exact operation inventory and source bindings. Include constructive
non-vacuity witnesses, invalid-boundary cases and mutation controls.
Use semantic parity cases against the existing independent Python oracle,
covering all operations and each checked arithmetic failure. Parity tests
are regression evidence, not a compiler-correctness theorem.

For generated hash circuits, prove a reusable builder invariant: a gate may
read only existing wires, its primitive has the required arity, and each
returned wire exists in the resulting state. Compose this invariant through
the hash's actual builder functions and prove the accepted output relation
for complete subcircuits, then extend it through rounds and loops. The
Poseidon2 fifth-power, SHA sigma and complete SHA-256 compression round are
proved by this method. The SHA round proof also composes over an arbitrary
`foldlM` list of live message wires, with exactly 27 gates per round. A
parameterized multi-round circuit is proved strictly sound for any number of
rounds with message words supplied as inputs. The concrete 64-round core
using the generated SHA constants is also certified; message expansion,
full schedule wiring and final feed-forward remain open.

Prove that an executable schedule checker implies well-formed gate indices,
output indices and primitive arities. Run it on every supported fixed hash
profile in CI, with malformed-circuit rejection controls. Keep executable
profile checks separate from kernel-checked certificates for an entire
parameterized schedule family.

Keep generated constants/fixtures identifiable with a deterministic generator;
keep caches, Lean binaries and raw build logs outside tracked sources.
Use focused scripts and a dedicated CI lane. Proof checking runs at build/CI
time and does not add proving-time constraints or change source/key identity.
Document all assumptions and uncovered correspondence boundaries in the
package README and PR. Keep the existing research draft status.
