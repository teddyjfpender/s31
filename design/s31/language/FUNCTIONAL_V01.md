# Functional S31: v0.1.0 release contract

Status: **in progress**. The existing compiler accepts a typed first-order
text subset and now erases monomorphic higher-order source functions into the
same normalized relation. This document states the architecture and evidence
required before calling the functional frontend a releasable language.

## The semantic split

S31 has two stages:

1. **Static source stage.** Names, functions, closures, type arguments, fixed
   shapes, library aliases and source modules are resolved and specialized.
   A value of `Fn(A) -> B` belongs here. No witness bit or field word may
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
overflow, and assertions. A `Fn` value has no circuit representation. Circuit
inputs and outputs require first-order `Circuit` types. Source functions may
accept and return `Fn` values, but each application must specialize to a
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
```

Equality is up to fresh node names and shared references; source and package
identities may differ. It must preserve operation order, types, constants,
public bindings and the chosen chip-recognizable recurrence. A mechanical
release gate must compare canonical IR, AIR components, raw and padded rows,
preprocessing, and FRI parameters for representative direct, sparse and chip
profiles. The [functional acceptance gate](../../../src/frontends/s31/tests/acceptance/acceptance_functional_core.py)
currently checks one four-lane direct-gate example and a native proof. This
is evidence for that program, not a theorem for all S31 sources.

An explicit typed ANF or SSA-like residual core would make this invariant
easier to audit and optimize. ANF's role in simplifying functional compilation
is described in [The Essence of Compiling with Continuations](https://felleisen.org/matthias/papers.html).
The current Zig relation is already first-order and topologically ordered;
the Python frontend still interleaves specialization with node emission.

## Conditional semantics must be decided before syntax

A witness-dependent `if` cannot discard an inactive branch from a fixed AIR.
Eagerly compiling both branches and selecting their values is sound only for
operations that are total on both paths. An inactive checked inverse or
overflow can otherwise make an apparently valid conditional unprovable.
The v0.1 language must therefore either:

- give dynamic `if` a typed, total-branch effect rule and lower it to
  constrained selection, or
- expose only an explicit strict selector and reserve `if` for static
  conditions.

The release specification must state the rule, prove bitness of the selector,
type-check both dynamic branches, and test zero, nonzero and partial-operation
cases. The current subset deliberately has no general `if` expression.

## Release evidence, not release intentions

The following are required for a v0.1.0 claim:

| Requirement | Evidence required | Current state |
| --- | --- | --- |
| Grammar and diagnostics | Versioned grammar, location-precise errors, malformed and fuzzed input corpus, bounded parse and specialization resources | Handwritten parser and bounded token/call depth; grammar/fuzz gate missing. |
| Type soundness | Separate typed elaboration of **all** declarations, no function values at circuit boundary, well-defined static/dynamic effects | Boundary and applied-function checks exist; unused bodies and full effects remain unchecked. |
| Semantic preservation | Proof or independently checked translation for typed source → normalized relation, including closure capture, shadowing, arrays and library calls | Lean proves source evaluation agrees with strict graph acceptance for every typed program in its total field/function core, including lexical capture and beta erasure. Python text compilation, arrays, library calls, effects and production AIR correspondence remain unproved. |
| Zero-cost abstractions | Canonical graph and AIR geometry equivalence across arithmetic, hashes, arrays and chip extraction, plus regression ceilings | One functional arithmetic gate exists; broader gate missing. |
| Build and native verification | Build, prove, verify, changed-statement rejection, independent oracle, reproducible source/key/IR identity | Existing package path and one functional native trial pass. |
| Repository hygiene | Parser, AST, elaborator, specialization, library and CLI isolated by directory, module READMEs and pinned dependency versions | Syntax, parser, builtins and specialization now live under `python/language/`; a separate elaborator and further library/CLI separation remain. |
| Release artifact | Tagged source, lockfile, supported-profile matrix, signed or otherwise authenticated distribution process, changelog and exact test commands | No v0.1.0 tag or release audit yet. |

The Lean package now has an intrinsically typed total field/function core
and a semantic simulation theorem for specialization. The remaining work is
to connect the Python parser and specializer to this core, extend the theorem
to arrays, effects and libraries, and connect the resulting first-order graph
to the production AIR. This follows the style
of [Wright and Felleisen's syntactic type-soundness work](https://felleisen.org/matthias/papers.html).
That theorem must be separate from the existing local AIR gadget proofs and
from probabilistic STARK soundness. Until all rows above have adequate
evidence, the repository should describe the frontend as an evolving subset.
