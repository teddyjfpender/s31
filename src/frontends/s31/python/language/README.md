# Text frontend implementation

The public Python entry point is `../text_frontend.py`. It retains the
`Parser`, `SourceError`, `compile_text` and `compile_file` imports used by the
CLI and existing tests. Implementation files are grouped by compiler phase:

| File | Responsibility |
| --- | --- |
| `syntax.py` | Located AST, declared function signatures, and static closures. |
| `builtins.py` | Compiler-owned names, lexical tokens, binding powers, and resource caps. |
| `parser.py` | Lexing, declaration and expression parsing, and first-order circuit boundary checks. |
| `types.py`, `builtin_types.py` | Source-only static array/literal types and pure builtin typing rules. |
| `elaborate.py` | Whole-program type checking, lexical scopes and call-graph bounds before emission. |
| `effects.py` | Exhaustive builtin totality inventory and transitive effect check for eager conditional arms. |
| `specialize.py` | Lexical environments, typed function application, source specialization, and normalized relation emission. |

`Fn` values never enter normalized relation JSON. Function application
specializes a body into the existing `s31_stdlib.Builder`, whose primitive
nodes are then validated and compiled by Zig. `../s31.py` hashes every Python
file in this directory into its compiler fingerprint, so changing parser or
specializer semantics invalidates cached packages and native verifier builds.

The elaborator checks unused declarations and lambda bodies without emitting
relation nodes. The effect pass rejects `if` arms that could fail even when
inactive. Opaque function parameters carry deferred effect obligations,
resolved when concrete static closures are supplied. Both arms specialize
into one fixed circuit. Specialization repeats value-level checks, including
bit provenance, constant partial operations, and static repeat shape. The Lean
source-core theorem does not yet prove this Python elaborator or all builtin
rules correct; those remain in the
[v0.1.0 release contract](../../../../../design/s31/language/FUNCTIONAL_V01.md).

The parser bounds both recursive descent and the final AST depth, so a long
left-associated expression cannot bypass the source nesting limit. The
[v1 grammar](../../docs/reference/GRAMMAR_V1.md) records its tokens and
precedence; the [generated source corpus](../../tests/python/generated/README.md)
checks direct and functional lowering against independent modular arithmetic.
