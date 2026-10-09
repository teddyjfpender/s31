# S31 normalized semantics and local constraint proofs

This package gives executable Lean semantics for **all 43 operations in S31
relation IR v1** and proves the local constraint models sound and complete.
It reuses `RiscvRefinement.Field.M31` and the existing
`RiscvRefinement.Recursion.CompactPoseidon` S-box proofs through a local Lake
dependency. The [contract](../../design/s31/language/FORMAL_SEMANTICS.md) fixes
the boundary and evidence requirements.

The normalized typed relation is the language boundary. The model covers
metadata validation, shapes, canonical input values, public/private
assignments, arithmetic failures, assertions and claimed public outputs.
Public input words precede output words and the statement is zero-padded to
eight words. Fixed widths and order are part of the source-bound statement;
padding alone cannot distinguish a trailing zero from a changed width.
Transparent and blinded proof modes have identical value semantics. That
theorem does not establish zero knowledge.

## Organization and reuse

| Location | Responsibility |
| --- | --- |
| `S31/Semantics/Types`, `Validation`, `Node`, `Program`, `Json` | Typed IR, complete operation dispatch, validation, assignment and public ABI. `Json` is an executable adapter, not a parser-correctness proof. |
| `S31/Semantics/Words`, `Integers`, `Bitcoin` | Little-endian limbs, five signed/unsigned widths, checked/wrapping operations, compact target and block work. |
| `S31/Semantics/Graph`, `Poseidon2`, `Blake2s`, `Sha256` | Explicit straight-line gate schedules and exact hash encodings. No uninterpreted hash callback is used. |
| `S31/Semantics/Functional` | Intrinsically typed `let`/lambda/application core, static specialization into first-order field polynomials, and an arbitrary-witness local constraint relation. |
| `S31/Gadgets/` | Primitive residual proofs, arbitrary auxiliary witnesses, constructive completeness and composition. |
| `S31/Gadgets/FunctionalGraph` | Executable polynomial-to-graph lowering and a kernel-checked strict circuit proof for the captured-square example. |
| `S31/Evidence/` | Checked operation coverage, non-vacuity/invalid-boundary theorems and live axiom enumeration. |
| `coverage.json` | Reviewed mapping of every operation to semantics, local gadget theorems and production source functions. |
| `source-bindings.json`, `proof-inventory.json` | Generated exact source identities and the complete theorem inventory, including the reused modules and three source-derived proof declarations. |
| `scripts/s31_formal.py`, `scripts/s31_formal_lib/` | Regeneration, escape/inventory checks, independent parity and adversarial proof controls. |

The package pins Lean **4.29.0** and Mathlib revision
`8a178386ffc0f5fef0b77738bb5449d50efeea95`. The committed Lake manifest pins
transitive dependencies. Generated hash constants come directly from the
repository's Poseidon2, SHA-256, BLAKE2s and genesis assets. S31 uses the
existing canonical M31 implementation rather than copying field arithmetic;
`Gadgets/Field` proves its bridge to `ZMod 2147483647` and kernel-checks
primality with Mathlib's Lucas–Lehmer certificate for `2^31-1`. The generic
`norm_num` primality proof for a 31-bit number can exceed the kernel's
recursion limit on some hosts.

## Proven local obligations

### Typed functional core

`Functional.Expr Γ τ` can be constructed only with well-typed variables,
field addition/multiplication, `let`, lambdas and application. `Meaning` gives
these expressions their ordinary field/function meaning. `specialize` maps
field values to polynomial expressions and functions to compile-time Lean
functions, so the residual `Poly` syntax has only inputs, literals, adds and
multiplies. `specialize_correct` proves by induction that specialization
preserves meaning for **all** well-typed core expressions, environments and
input assignments. `program_correct` specializes the theorem to first-order
field inputs and output.

`Poly.Accepts` independently checks local add/multiply residuals and
existential intermediate values. `Poly.accepts_sound_complete` proves that
every satisfying witness yields exactly the polynomial evaluation, and that
an honest witness exists. `program_accepts_iff` composes this with the source
theorem. `specialize_beta` proves that static function application has the
same residual result as binding the argument in a `let`.

The hand-written `capturedSquare` term models
`let saved = x in let f = fun(y : m31) -> m31 => y * y + saved in f(saved)`.
`capturedSquare_zero_cost` reduces its residual tree to `x*x+x`, and
`capturedSquare_accepts` proves its local constraints accept exactly that
value for every M31 input. `FunctionalGraph` lowers every residual polynomial
through the generic graph builder. `Poly.emit_valid` proves by induction that
emission preserves a valid builder, keeps the input prefix fixed, returns a
live wire, and never removes gates. `Poly.emit_prefix` proves emitted gates
append to the old graph, and `Poly.emit_value` proves the returned wire
evaluates to the polynomial on every input assignment. Thus `Poly.code_valid`
proves every emitted graph has valid wire indices and arities, while
`Poly.code_eval` proves its output value equals polynomial evaluation.
`Poly.code_accepts` applies the independent strict graph constraint theorem
to arbitrary intermediate witnesses. `program_graph_accepts` composes these
results with typed source specialization: for **every** program in the small
total field/function core, strict graph acceptance is equivalent to its
source result. For the worked example, the checked circuit is:

| Wire | Meaning | Local equation |
| --- | --- | --- |
| `0` | input `x` | supplied graph input |
| `1` | `x*x` | `w₁ - x*x = 0` |
| `2` | `w₁+x` | `w₂ - (w₁+x) = 0` |

The graph output is wire `2`. `capturedSquareCode_shape` proves the executable
lowering produces exactly those two gates; `capturedSquareCode_valid` proves
well-formed indices and arities. `capturedSquareCode_accepts` proves strict
acceptance is equivalent to the source result for **every** intermediate
witness. These are kernel-checked statements about the
small formal core. The Python parser, S31's wider type set, library calls,
assertions, partial operations, and production AIR lowering are outside this
theorem. The formal
source identity inventory now includes the Python
syntax, parser, specializer and libraries so changes there force a reviewed
binding update; the source digests themselves do not prove compiler correspondence.

Soundness quantifies over every satisfying auxiliary witness. Completeness
constructs witnesses for every input within the stated range and shape
premises. Honest-witness evaluation alone is insufficient for soundness.

| Gadget family | Main results |
| --- | --- |
| Field arithmetic and zero anchors | Residual equations iff addition, multiplication, equality or zero; canonical M31/ZMod bridge and inversion iff nonzero. |
| Boolean operations and selection | Bit equation iff 0 or 1; NOT, AND, OR, XOR, scalar/Boolean selection; zero indicator sound for every inverse witness, including the unconstrained inverse at zero. |
| Range and packing | Byte range via scaled u16; 16 Boolean bits iff u16; byte-pair packing, endian round trips and canonical digest reduction, including quotient 2. |
| Carry/borrow arithmetic | Local field equations imply integer equations; whole chains iff checked or wrapping arithmetic; reversed subtraction iff ≤ or <. |
| Signed arithmetic | Sign extraction, most-significant-limb sign, two's-complement interpretation, signed comparison, overflow predicates, composed signed checked addition/subtraction iff mathematical results. |
| Packed M31 lanes | QM31 basis multiplication, coordinate extraction, active masks, scalar multiplication, production sum projection/dual literals, `mix4`, active-lane inversion. |
| Static repeats | Pointwise primitive constraints, sum witnesses, bodies and arbitrary finite repeat counts iff the executable recurrence. |
| Hashes | Arbitrary intermediate gate witnesses iff the full Poseidon2 leaf/pair, personalized terminal BLAKE2s and header double SHA-256 results, including packing and digest reduction. |
| Bitcoin target | One-hot exponent range, byte placement, nonzero byte-sum inverse and high-zero bytes iff a positive target within mainnet's `2^224-1` limit. |
| Bitcoin division/work | Nontruncated schoolbook product, terminal carry, strict remainder, unique quotient/remainder and the exact block-work formula. |
| Wires and public bindings | Constant/alias/get/concat/slice identities, assertion residuals, fixed-width segment/padding binding, proof-mode independence; a successful evaluator returns exactly the declared claim **and every declared output equals its computed value**, including kind and width. Changing only a private witness cannot change the claim. |
| Graph wiring | `Code.WellFormedFor` requires that every gate reads an input or earlier wire, every output index exists, and each primitive has its exact operand count. `Code.check_sound` proves that the executable checker implies this proposition; `strict_code_sound_complete` combines it with arbitrary-witness primitive soundness. |
| Builder composition | `emit_valid` and `build_valid` prove that valid emitted gates and live outputs produce a valid circuit. The actual Poseidon2 fifth-power, SHA sigma and complete SHA compression-round builders preserve this invariant. Their strict circuit relations are proved equivalent to the computed outputs; fifth power and sigma are also reduced to explicit mathematical formulas. |

Range premises are explicit. A modular equation alone cannot imply an integer
equation: the bridge needs both sides below M31. For the Bitcoin multiplication
columns, the maximum is `32*255² + 255 + 65535 = 2,146,590 < 2³¹-1`.
High product digits and the terminal carry are retained, so the multiplication
proof cannot accept truncation of a 512-bit product.

The hash relation checks each primitive gate and existential intermediate
wire; its definition does not call the hash interpreter. `Graph.Accepts`
proves generic straight-line composition. Word gadgets use canonical
`BitVec 32` values, per-bit polynomial equations and an integer word-add carry
equation; the range/limb lemmas separately justify those encodings. Fixed
hash schedules are marked `irreducible` to keep elaboration from repeatedly
expanding thousands of gates; they remain explicit, executable definitions
and introduce no axiom.

`Graph.Accepts` on its own has the historical `getD` fallback for malformed
indices or missing primitive operands. Use `Code.strictAccepts` when making a
statement about a valid circuit: its `WellFormedFor` premise rules out these
fallbacks. The formal package proves the generic rule and small valid/invalid
schedule examples. The CI gate runs `s31-check --schedule-check` over 57
generated hash profiles: Poseidon2 pair and four leaf sizes, SHA-256
compression, and BLAKE2s word counts 0–16 with three personalization values.
It also demands rejection of an invalid wire and a missing operand. Lean proves
that a `true` checker result implies `WellFormedFor`. The 57 executable results
are **regression evidence, not kernel-checked proofs that every parameterized
hash schedule is valid**. Fixed schedule certificates for all parameters and
the correspondence to production AIR emission remain obligations.

### Kernel-certified hash subcircuits

The builder proof works gate by gate, so Lean does not need to normalize a
whole hash permutation. For the Poseidon2 fifth-power routine, input `x` is
wire 0 and the generated circuit is:

| New wire | Constraint |
| --- | --- |
| 1 | `w₁ = x · x` |
| 2 | `w₂ = w₁ · w₁` |
| 3 | `w₃ = x · w₂` |

`Poseidon2.fifth_valid` proves that these gates preserve valid wiring in any
already-valid builder state. `Poseidon2.fifthCircuit_valid` proves the complete
one-input circuit is well formed. `Poseidon2.fifthCircuit_correct` then proves,
for **every** satisfying intermediate witness, that the only accepted output
is the canonical M31 value of `x⁵`.

For SHA sigma, the one-input circuit emits `rotr(x,a)`, `rotr(x,b)`, their XOR,
then either `shr(x,c)` or `rotr(x,c)`, then one final XOR. The
`Sha256.sigmaCircuit_correct` theorem covers either choice and arbitrary shift
amounts. `Sha256.round_valid` then proves that the **actual SHA-256 round
builder** preserves valid wiring for any live eight-word state and message
wire. Its 27 gates include `Ch`, `Maj`, both capital sigma functions, the
round constant and the output additions. `Sha256.rounds_valid` inducts over
the actual `foldlM` of round/message pairs: for any list of live message
wires, the state remains eight live words and the builder adds exactly
`27 × rounds` gates. `Sha256.roundCircuit_valid` proves
that a complete nine-input circuit generated by that builder is well formed;
`roundCircuit_strict_sound_complete` says every accepted auxiliary witness
has exactly the computed eight-word round output. The circuit proof holds for
every round constant, not merely the 64 standard constants.

`Sha256.roundsCircuit_valid` and `roundsCircuit_strict_sound_complete` lift this
to a complete parameterized circuit for any list of `(message wire, constant)`
pairs. The first eight inputs are the initial state. Each message wire must
name one of the circuit inputs, so a 64-round instance can take all 64
expanded words as inputs. The theorem covers every satisfying witness for
those rounds. It does not yet certify that the 48 expanded message words are
the correct SHA-256 schedule of a 16-word block.

`Sha256.sha64Circuit_valid` specializes this to the generated table of 64
SHA-256 round constants. Its 72 inputs are eight state words followed by 64
already-expanded message words. `sha64Circuit_strict_sound_complete` proves
that the 64-round core accepts exactly the circuit's computed eight-word
state for every input and every auxiliary witness. The round invariant gives
`64 × 27 = 1728` gates in this core; it excludes message expansion and the
final eight feed-forward additions.

These are proofs of generated subcircuits used by the hash schedules. The
complete Poseidon2, SHA-256 and BLAKE2s schedules still need compositional
builder invariants for message expansion, state indexing and final
feed-forward. The one-round theorem
relates acceptance to the generated circuit evaluator; a separate
formula-level refinement theorem for the entire compression function is not
yet present.

## Scope of the claim

**The local mathematical constraint models are proved. Production compiler
correctness is not proved.** Source hashes and the operation map make a
manual correspondence review inspectable; they cannot establish that every
Zig lowering emits exactly those constraints. In particular, raw text/JSON
parsing and specialization, general compiler lowering, chip/direct/sparse
AIR correspondence, lookup/LogUp composition over arbitrary traces, Zig
machine code, STARK soundness and zero knowledge remain separate obligations.
The typed model constrains private values mathematically; visibility affects
the public ABI and does not itself imply witness privacy.
The public binding theorems concern accepted executions under the *same declared*
public inputs and outputs. They prove agreement for every output, including
the second output of a two-output example, but do not assert that private
inputs are hidden or that a circuit is bound to the claim: production AIR correspondence remains
an explicit separate obligation. Lean also checks one honest private binding,
a changed private witness, and a forged public output claim.

The Python parity corpus is regression evidence for the executable semantics,
not a proof of compiler or cryptographic correctness. Hash parity includes
Python `hashlib` and the existing independent Poseidon2 implementation.
The source inventory includes both reused Lean modules, whose theorems are
also included in the live axiom audit. Only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` axioms are approved. Proof sources reject
`sorry`, `admit`, custom `axiom`, `unsafe` and `native_decide`.

## Reproduce the gate

Run from the repository root with the pinned Lean toolchain available:

```sh
python3 scripts/s31_formal.py
python3 -m unittest scripts.tests.test_s31_formal
mkdir -p zig-out/s31/formal
cd formal/s31
lake exe cache get Mathlib.Data.ZMod.Basic Mathlib.Tactic Mathlib.NumberTheory.LucasLehmer
lake build S31 s31-check
lake env lean S31/Evidence/AxiomAudit.lean > ../../zig-out/s31/formal/axioms.log
LEAN_NUM_THREADS=1 lake env leanchecker -v S31 RiscvRefinement.Field.M31 RiscvRefinement.Recursion.CompactPoseidon > ../../zig-out/s31/formal/kernel.log
cd ../..
python3 scripts/s31_formal.py \
  --audit zig-out/s31/formal/axioms.log \
  --kernel-log zig-out/s31/formal/kernel.log \
  --parity formal/s31/.lake/build/bin/s31-check \
  --controls --report zig-out/s31/formal/evidence.json

# The same executable can run the schedule gate by itself:
formal/s31/.lake/build/bin/s31-check --schedule-check
```

`leanchecker` replays declarations with Lean's kernel; it is not a separate
proof assistant. One worker bounds memory without reducing its checks. The
gate requires exact replay and theorem inventories, builds every `S31.*`
source, rejects missing evidence, and compiles valid controls before requiring
invalid controls to fail. It also alters actual byte-range, carry-base and
signed-overflow definitions and requires their original proofs to fail.
Temporary mutations never alter repository sources.
The mutation set includes polynomial addition and graph emission in the
functional core; changing either addition to multiplication must make the new
proofs fail to compile.

The dedicated [CI workflow](../../.github/workflows/s31-formal.yml) runs these
steps without a skip path and preserves live evidence. Caches, binaries and
raw logs are ignored build artifacts. After a reviewed semantics/source
change, regenerate with `python3 scripts/s31_formal.py --write`, inspect the
diff and rerun the full gate. Regeneration updates identities; it does not
prove a new correspondence obligation. Formal checking adds no constraints
or work to the production prover.
