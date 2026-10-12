# Functional S31: v0.1.0 release contract

Status: **in progress**. The existing compiler accepts a typed first-order
text subset and now erases monomorphic higher-order source functions into the
same normalized relation. This document states the architecture and evidence
required before calling the functional frontend a releasable language.

## The semantic split

S31 has two stages:

1. **Static source stage.** Names, functions, closures, type arguments, fixed
   shapes, library aliases and source modules are resolved and specialized.
   Values of `Fn(A) -> B` and source tuples belong here. No witness bit or field word may
   control which program graph is generated.
2. **Dynamic relation stage.** Circuit inputs, fixed-width values, field
   arrays, digest types and primitive operations become a typed, acyclic
   relation. The Zig compiler chooses an AIR profile from this relation and
   generates a bound native verifier.

This is an application of binding-time separation and specialization as
developed in [Partial Evaluation and Automatic Program Generation](https://studwww.itu.dk/people/sestoft/pebook/).
The explicit two-stage typing boundary is also informed by
[Davies and Pfenning's modal analysis of staged computation](https://www.cs.cmu.edu/~fp/papers/CMU-CS-99-153.pdf).
Higher-order functions are eliminated before the relation boundary; the
first-order target is consistent with the transformation studied in
[Defunctionalization at Work](https://tidsskrift.dk/brics/article/view/21684).
The current compiler performs direct specialization; these references guide
the intended language design and are not proofs about this implementation.

The core value judgment should eventually be explicit:

```text
Γ ⊢ e : Static τ     or     Γ ⊢ e : Circuit τ ! ε
```

Here `ε` records partial proof operations, such as checked inversion or
overflow, and assertions. A `Fn` or tuple value has no circuit representation. Circuit
inputs and outputs require first-order `Circuit` types. Source functions may
accept and return `Fn` or tuple values, but each application must specialize to a
finite relation. Effect tracking for partial operations draws on the general
approach of making effects explicit in function types, as in
[Koka's row-polymorphic effect types](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/paper-20.pdf);
S31 needs a much smaller fixed effect set, not Koka's full handler system.

## Lowering invariant

For any well-typed source program `p`, let `specialize(p)` be its normalized
relation and `ops(r)` be the primitive relation graph. The intended
zero-abstraction-cost invariant is:

```text
ops(specialize(let x = e₁ in e₂))
    = ops(specialize(e₂[x := e₁]))

ops(specialize((fun(x: A) -> B => body)(arg)))
    = ops(specialize(body[x := arg]))

ops(specialize(let pair = (a, b) in pair.0 + pair.1))
    = ops(specialize(a + b))
```

Equality is up to fresh node names and shared references; source and package
identities may differ. It must preserve operation order, types, constants,
public bindings and the chosen chip-recognizable recurrence. A mechanical
release gate must compare canonical IR, AIR components, raw and padded rows,
preprocessing, and FRI parameters for representative direct, sparse and chip
profiles. The [functional acceptance gate](../../../src/frontends/s31/tests/acceptance/acceptance_functional_core.py)
checks four-lane arithmetic through both generic `gate` and `direct-gate`, a `direct-chip` recurrence, a
`sparse-wide-gate` checked 256-bit reduction, and a captured array/hash
closure under `direct-gate`,
including native proofs and exact AIR-cost equality with first-order forms.
These are program-specific evidence, not a theorem for all S31 sources.

An explicit typed ANF or SSA-like residual core would make this invariant
easier to audit and optimize. ANF's role in simplifying functional compilation
is described in [The Essence of Compiling with Continuations](https://felleisen.org/matthias/papers.html).
The current Zig relation is already first-order and topologically ordered;
the Python frontend still interleaves specialization with node emission.

## Witness-dependent conditional rule

A witness-dependent `if` cannot discard an inactive branch from a fixed AIR.
Eagerly compiling both branches and selecting their values is sound only for
operations that are total on both paths. An inactive checked inverse or
overflow can otherwise make an apparently valid conditional unprovable.
The v0.1 subset uses `if bit then a else b` only when both branches have the
same selectable first-order type and are total on well-typed values. The
compiler emits both branches followed by the existing constrained selection;
`bit` results use `bool_select`. An exhaustive effect inventory classifies
all current builtins, and transitive analysis includes named functions and
known closures. An opaque function parameter carries a deferred effect
obligation; each concrete static call resolves it, and no unresolved effect
may reach the circuit boundary. A partial condition remains a precondition
of the whole expression. The source `if` adds no relation node beyond the
equivalent explicit selector.

The release gate still needs broader geometry equivalence checks and a
formal correspondence from source conditionals through effect analysis to
the generated AIR. Lean composes total source branches with the local
selector relation and proves soundness for both bit values; it does not
verify the Python effect pass or the complete production AIR emission.
Lean also proves that a conservative totality check makes eager and lazy
conditionals agree in a small language with checked inversion, and exhibits
the inactive inverse-of-zero counterexample when that premise is dropped.
The local u16-vector selector theorem further proves that byte and wide
nominal selections preserve the selected input and its limb range, including
arbitrary intermediate witnesses for the compiler's complement, products and
sum. The production profile correspondence remains a separate obligation.

## Release evidence, not release intentions

The following are required for a v0.1.0 claim:

The current executable functional profile sample is deliberately small. The
same source-level four-lane square and handwritten first-order form have equal
full reported AIR geometry under both `gate` and `direct-gate`; the generic
profile has 4,248,656 preprocessed cells and the direct profile has 4,096.
This illustrates a real circuit profile cost difference for one function, not
a universal timing or proof-size ratio. `direct-chip` uses a 16-round
recurrence, and `sparse-wide-gate` uses a checked 256-bit sum. The
[`acceptance_functional_core.py`](../../../src/frontends/s31/tests/acceptance/acceptance_functional_core.py)
gate checks native acceptance, independent output values and altered public
claim rejection for all four cases.

| Requirement | Evidence required | Current state |
| --- | --- | --- |
| Grammar and diagnostics | Versioned grammar, location-precise errors, malformed and fuzzed input corpus, bounded parse and specialization resources | The v1 grammar documents exact source forms, including postfix application of returned closures, parenthesized lambdas, named `fn` references as static values, and returned or local static recurrence steps. The parser bounds token count, numeric token length, recursive expression/type descent and final AST depth with located errors; static call and effect analysis have separate limits. Pinned generated corpora check 96 scalar, 64 four-lane array, nine packed-lane, 29 math/hash, 40 tuple and 160 higher-order function-route programs against independent values and exact first-order IR; malformed mutations have located diagnostics. The higher-order corpus also checks that partial effects survive ten function-value routes into inactive conditional arms. Record ABI leaves are capped before expansion; repeated immutable effect shapes share memory; assertion expansion is bounded and duplicate equalities are erased. Native validation caps aggregate input words, total relation items, JSON source bytes and early shape work; both compiler routes check actual unpadded gate and variable counts during lowering. Generic repeat expansion has its own aggregate lane-step budget. Wider grammar fuzzing remains. |
| Type soundness | Separate typed elaboration of **all** declarations, no function values at circuit boundary, well-defined static/dynamic effects | Pure elaboration checks every function and lambda body, source types, lexical scopes and call-graph bounds before emission. An exhaustive conservative effect pass rejects potentially partial inactive `if` arms. Value-dependent checks still run during specialization; a machine-checked effect soundness proof remains missing. |
| Semantic preservation | Proof or independently checked translation for typed source → normalized relation, including closure capture, shadowing, arrays and library calls | Lean proves source evaluation agrees with strict graph acceptance for every typed program in its total field/function core, including lexical capture, beta erasure, field outputs and source-level equality assertions. The core includes shape-indexed M31 arrays with pointwise arithmetic, splats, indexed reads and bounded `take`/`drop`/`concat` views; every array output lane is bound by an arbitrary-witness strict graph theorem. Total-branch field and array conditionals, including one shared selector and all array lanes in a strict graph, and a small conservative effect check are proved. Lean also proves the mathematical meaning and strict field-graph acceptance of nonempty static sum/dot and Horner polynomial combinators in the source core; their graph schedule is a model, not a proof of Python mathlib lowering. The worked four-lane quadratic proves closure erasure and all-output strict graph acceptance for a typed analogue of a checked-in `.s31` example. A curried two-application scalar analogue proves one-gate erasure and arbitrary-witness output binding. A named-function-value scalar analogue proves static binding and application erase to one multiply with strict-graph output binding. Array conditionals, pointwise M31 addition/subtraction/multiplication and concat/get/slice views agree with concrete normalized nodes evaluated by `evaluateNode`. A static recurrence theorem proves the `square; add_const 7` body acts independently on every lane for any round count and binds all satisfying abstract repeat witnesses. A worked `mix4` theorem proves the three hand-calculated rounds and arbitrary-witness output binding for the coupled four-lane step. Theorems connect final pointwise arithmetic and Boolean array choice for arrays of any length to packed AIR rows, including short final rows; a separate masked pairwise reduction theorem covers normalized `sum_lanes`. Python text compilation, the full library, the full effect checker and production AIR correspondence remain unproved. |
| Zero-cost abstractions | Canonical graph and AIR geometry equivalence across arithmetic, hashes, arrays and chip extraction, plus regression ceilings | Functional arithmetic and conditional gates compare canonical IR and direct-gate AIR geometry with explicit equivalents. Static tuples and nominal records now support whole-product selection and assertion by emitting exactly the fieldwise primitive relation. The typed nested-record fixture has native proof acceptance for both selector values and changed-claim rejection; it matches its handwritten fieldwise form at 299 raw and 512 padded QM31 rows, with all reported geometry fields equal. Nine packed-lane cases compare exact normalized IR across lengths 1–15; native geometry checks for lengths 3, 5 and 9 are gated in CI. A five-lane named subtraction helper now matches direct source in normalized IR and the full release-gated AIR cost tuple; its native proof accepts the honest result and rejects changed claims in the first and fifth lanes. Twenty math and nine Poseidon2 programs compare exact normalized IR with direct forms and independently checked values. A native CI gate pins equal complete geometry for a curried one-gate sum, named four-lane square, handwritten quadratic, static matrix product, returned `mix4` step, and three-hash Poseidon2 parent under `direct-gate`, with 275, 312, 318, 326, 344 and 11,840 raw QM31 rows. Named steps passed through `Fn` helpers and constant-capturing closure steps each match direct `iterate` in normalized IR, selected chip, AIR geometry and FRI settings under `direct-chip`; a functional checked `UInt256` sum matches its direct form under `sparse-wide-gate`. A captured closure over array views and a Poseidon2 hash matches a direct circuit. Wider native hash and array geometry remains. |
| Build and native verification | Build, prove, verify, changed-statement rejection, independent oracle, reproducible source/key/IR identity | Functional arithmetic has native trials under generic `gate` and `direct-gate`; conditional, named and captured recurrence-chip, and sparse-wide native trials also pass, including both selector values and changed-claim rejection. Packed arrays of lengths 3, 5 and 9 each pass two native proofs, independent modular arithmetic, and changed-claim rejection; their raw QM31 row counts are 311, 319 and 328, while each padded trace has 512 rows and 4096 preprocessed cells. The curried sum, named four-lane square, handwritten quadratic, static matrix product, returned `mix4` step and Poseidon2 pair also have native proofs, independent expected results and false-claim rejection. The scoped twelve-profile candidate matrix passed for the `v0.1.0-rc.4` developer prerelease; this is finite fixture evidence, not general source coverage. |
| Public record ABI | A versioned, source-bound encoding for nominal public records, with checked visibility, paths, aliases, canonical words and native rejection controls | ABI v2 is implemented for direct-gate record inputs and outputs, with narrow public one-call direct-chip and mixed-general extensions. Direct-gate admits public `bit`, scalar `u8`, `[u16; N]` for `1 ≤ N ≤ 8`, and scalar `u32` leaves with native range and claim controls. Private narrow leaves, derived narrow results, narrow leaves in chip or mixed profiles, and private record chip endpoints are not admitted. The Lean model does not yet refine the production parser and native verifier. |
| Repository hygiene | Parser, AST, elaborator, specialization, library and CLI isolated by directory, module READMEs and pinned dependency versions | Syntax, parser, builtin typing, elaboration and specialization live under `python/language/`. Standard and math library implementations live under `python/library/`, with compatibility imports and an expanded source lock/fingerprint. Cost and semantic-equation reports live under `python/inspection/`. Source identity, package building and integrity checks live under `python/package/`. Native trials and fold audits live under `python/runtime/`. Argument parsing and command dispatch live under `python/cli/`; the root executable/API is 44 lines. All modules have READMEs and enter the source fingerprint. A smaller declarative command table remains desirable. |
| Release artifact | Tagged source, lockfile, supported-profile matrix, signed or otherwise authenticated distribution process, changelog and exact test commands | The [v0.1.0-rc.4 developer prerelease](https://github.com/teddyjfpender/s31/releases/tag/v0.1.0-rc.4) ships a hash-checked complete source bundle with its pinned engine and a finite-evidence archive. It does not satisfy the full v0.1.0 soundness and correspondence requirements in this table; trusted distribution and an independent native PCS/FRI soundness argument remain open. |

The opt-in strict `verify-release` path now independently reparses exact
source bytes for a bounded public four-lane direct-gate fragment. It covers
up to eight acyclic pure functions, calls to earlier declarations, local
arithmetic lets, expression-level lexical `let … in` inside circuit lets, and
named unary `Fn([m31; 4]) -> [m31; 4]` values passed through static aliases
and function parameters. It also admits unary lambdas with bounded pure
arithmetic and lexical-let bodies over the argument and existing captured wires.
The same bounded lambdas may be supplied inline as arguments to unary `Fn`
parameters, including captures from the current lexical scope.
The checker replays generated and anonymous wire names, requires exact
normalized relation and canonical SSA equality, then checks the native gate
topology and fixed-root key before native proof verification. The
[composed-function](../../../src/frontends/s31/examples/functional/release_square4/README.md),
[lexical-let](../../../src/frontends/s31/examples/functional/release_let4/README.md),
and [named-function-value](../../../src/frontends/s31/examples/functional/release_higher_order4/README.md)
fixtures each match their handwritten two-gate form at 322 raw and 512 padded
QM31 rows, pass `verify-release`, and reject a changed public result. This is
finite evidence for this fragment. The
[captured-lambda fixture](../../../src/frontends/s31/examples/functional/release_closure4/README.md)
matches its handwritten four-gate form at 324 raw and 512 padded QM31 rows
and tests lexical capture across a shadowed name.
The [inline-lambda fixture](../../../src/frontends/s31/examples/functional/release_inline_lambda4/README.md)
passes one anonymous function to a helper that applies it twice and matches
its handwritten two-gate form at 322 raw and 512 padded QM31 rows. The
certificate does not cover other lambda operations, general closures or
higher-order source, records, private inputs, other AIR profiles, or the native
PCS/FRI proof
system, and it does not replace the full compiler correspondence proof above.

The independent bounded [source-to-relation checker](SOURCE_RELATION_FRAGMENT.md)
now parses one pure named function over homogeneous `[m31; N]` arrays for
`1 ≤ N ≤ 8`, including ordered subtraction, and checks its static call against
the exact normalized relation without invoking the production compiler. The
five-lane functional subtraction acceptance runs that check on the generated
package and separately verifies its native proof. The checker's capability is
`source-to-relation-only`; it does not certify the circuit, AIR, or proof.

The typed product extension adds `(A, B)` and `(a, b)` with statically checked
`.0`/`.1` projections. A tuple is evaluated eagerly and erased before relation
emission. Tuple patterns are parser sugar over one hygienic binding and static
projections; their depth is bounded. The `tuple_square_sum.s31` example compiles to the exact normalized
three-node relation of its handwritten form. The Lean source core has product
semantics and a general specialization theorem covering pairs and projections;
its worked scalar theorem binds arbitrary satisfying local graph witnesses.
The native direct-gate cost and proof comparison is part of the functional
library gate: the tuple and direct forms share a 314-raw-row, 512-padded-row
AIR and an accepted 56,967-byte native proof; a changed claim is rejected.
Forty generated tuple sources compare exact relation IR and independent values
at both selector bits. This evidence still does not prove Python compiler
correctness.

Named functions and lambdas now also accept tuple and nominal record parameter
patterns. The parser assigns one hidden parameter to the whole argument and
inserts only static projections; cross-parameter duplicate names and wrong
product types fail with located diagnostics. The checked-in weighted-pair
example emits the exact two-node `mul; add` relation of its handwritten form.
The source-level effect test keeps a partial inverse visible inside a
destructured closure on an inactive conditional arm. Step-flow analysis tracks
the exact projection path through product parameters and returned functions so
the `mix4` recurrence reaches chip recognition without granting step context
to an unrelated tuple member. The Lean functional core proves the modeled
pair-parameter beta erasure; Python lowering and native AIR correspondence
remain separate obligations.

The Lean package now has an intrinsically typed total field/array/function core,
a semantic simulation theorem for specialization, and strict graph theorems
that bind every field output and check field equality assertions. It also has
local arithmetic AIR row proofs, packed-lane lemmas and an exact Gate multiset
model. The remaining work is to connect the Python parser and specializer to
this core, extend the theorem to full effects and libraries, and connect the
resulting first-order graph to the production AIR and native verifier. This
follows the style
of [Wright and Felleisen's syntactic type-soundness work](https://felleisen.org/matthias/papers.html).
That theorem must be separate from the existing local AIR gadget proofs and
from probabilistic STARK soundness. Until all rows above have adequate
evidence, the repository should describe the frontend as an evolving subset.

The `HigherOrderRoutes` model now proves for arbitrary residual inputs that a
captured returned function, a local function binding, and higher-order passage
produce the same two-node polynomial graph as `x*x + y`. Its strict-graph
theorems bind every accepted output, construct the honest witness and exclude
a forged claim. The pinned generated Python corpus checks analogous source
routes against the production text compiler, but there is still no theorem
that the Python compiler implements the Lean specialization function.
