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
checks four-lane direct-gate arithmetic, a `direct-chip` recurrence, a
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

| Requirement | Evidence required | Current state |
| --- | --- | --- |
| Grammar and diagnostics | Versioned grammar, location-precise errors, malformed and fuzzed input corpus, bounded parse and specialization resources | The v1 grammar documents exact source forms, including postfix application of returned closures, parenthesized lambdas, named `fn` references as static values, and returned or local static recurrence steps. The parser bounds token count, numeric token length, recursive expression/type descent and final AST depth with located errors; static call and effect analysis have separate limits. Pinned generated corpora check 96 scalar, 64 four-lane array, nine packed-lane and 29 math/hash programs against independent values and exact first-order IR; malformed mutations have located diagnostics. A focused application suite checks curried and named values, lexical shadowing, errors and conditional effects. Wider grammar fuzzing remains. |
| Type soundness | Separate typed elaboration of **all** declarations, no function values at circuit boundary, well-defined static/dynamic effects | Pure elaboration checks every function and lambda body, source types, lexical scopes and call-graph bounds before emission. An exhaustive conservative effect pass rejects potentially partial inactive `if` arms. Value-dependent checks still run during specialization; a machine-checked effect soundness proof remains missing. |
| Semantic preservation | Proof or independently checked translation for typed source → normalized relation, including closure capture, shadowing, arrays and library calls | Lean proves source evaluation agrees with strict graph acceptance for every typed program in its total field/function core, including lexical capture, beta erasure, field outputs and source-level equality assertions. The core includes shape-indexed M31 arrays with pointwise arithmetic, splats, indexed reads and bounded `take`/`drop`/`concat` views; every array output lane is bound by an arbitrary-witness strict graph theorem. Total-branch field and array conditionals, including one shared selector and all array lanes in a strict graph, and a small conservative effect check are proved. Lean also proves the mathematical meaning and strict field-graph acceptance of nonempty static sum/dot and Horner polynomial combinators in the source core; their graph schedule is a model, not a proof of Python mathlib lowering. The worked four-lane quadratic proves closure erasure and all-output strict graph acceptance for a typed analogue of a checked-in `.s31` example. A curried two-application scalar analogue proves one-gate erasure and arbitrary-witness output binding. A named-function-value scalar analogue proves static binding and application erase to one multiply with strict-graph output binding. Array conditionals, pointwise M31 addition/multiplication and concat/get/slice views agree with concrete normalized nodes evaluated by `evaluateNode`. A static recurrence theorem proves the `square; add_const 7` body acts independently on every lane for any round count and binds all satisfying abstract repeat witnesses. A worked `mix4` theorem proves the three hand-calculated rounds and arbitrary-witness output binding for the coupled four-lane step. Theorems connect final pointwise arithmetic and Boolean array choice for arrays of any length to packed AIR rows, including short final rows; a separate masked pairwise reduction theorem covers normalized `sum_lanes`. Python text compilation, the full library, the full effect checker and production AIR correspondence remain unproved. |
| Zero-cost abstractions | Canonical graph and AIR geometry equivalence across arithmetic, hashes, arrays and chip extraction, plus regression ceilings | Functional arithmetic and conditional gates compare canonical IR and direct-gate AIR geometry with explicit equivalents. Nine packed-lane cases compare exact normalized IR across lengths 1–15; native geometry checks for lengths 3, 5 and 9 are gated in CI. Twenty math and nine Poseidon2 programs compare exact normalized IR with direct forms and independently checked values. A native CI gate pins equal complete geometry for a curried one-gate sum, named four-lane square, handwritten quadratic, static matrix product, returned `mix4` step, and three-hash Poseidon2 parent under `direct-gate`, with 275, 312, 318, 326, 344 and 11,840 raw QM31 rows. Named steps passed through `Fn` helpers and constant-capturing closure steps each match direct `iterate` in normalized IR, selected chip, AIR geometry and FRI settings under `direct-chip`; a functional checked `UInt256` sum matches its direct form under `sparse-wide-gate`. A captured closure over array views and a Poseidon2 hash matches a direct circuit. Wider native hash and array geometry remains. |
| Build and native verification | Build, prove, verify, changed-statement rejection, independent oracle, reproducible source/key/IR identity | Functional arithmetic, conditional, named and captured recurrence-chip, and sparse-wide native trials pass, including both selector values and changed-claim rejection. Packed arrays of lengths 3, 5 and 9 each pass two native proofs, independent modular arithmetic, and changed-claim rejection; their raw QM31 row counts are 311, 319 and 328, while each padded trace has 512 rows and 4096 preprocessed cells. The curried sum, named four-lane square, handwritten quadratic, static matrix product, returned `mix4` step and Poseidon2 pair also have native proofs, independent expected results and false-claim rejection. A complete supported-profile release matrix remains. |
| Repository hygiene | Parser, AST, elaborator, specialization, library and CLI isolated by directory, module READMEs and pinned dependency versions | Syntax, parser, builtin typing, elaboration and specialization live under `python/language/`. Standard and math library implementations now live under `python/library/`, with compatibility imports and an expanded source lock/fingerprint. The package/trial/inspection CLI remains a large root module and needs separation. |
| Release artifact | Tagged source, lockfile, supported-profile matrix, signed or otherwise authenticated distribution process, changelog and exact test commands | No v0.1.0 tag or release audit yet. |

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
