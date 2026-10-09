# Text frontend implementation

The public Python entry point is `../text_frontend.py`. It retains the
`Parser`, `SourceError`, `compile_text` and `compile_file` imports used by the
CLI and existing tests. Implementation files are grouped by compiler phase:

| File | Responsibility |
| --- | --- |
| `syntax.py` | Located AST, declared function signatures, and static closures. |
| `builtins.py` | Compiler-owned names, lexical tokens, binding powers, and resource caps. |
| `parser.py` | Lexing, declaration and expression parsing, and first-order circuit boundary checks. |
| `specialize.py` | Lexical environments, typed function application, source specialization, and normalized relation emission. |

`Fn` values never enter normalized relation JSON. Function application
specializes a body into the existing `s31_stdlib.Builder`, whose primitive
nodes are then validated and compiled by Zig. `../s31.py` hashes every Python
file in this directory into its compiler fingerprint, so changing parser or
specializer semantics invalidates cached packages and native verifier builds.

The current design still interleaves expression type checks with relation
emission; a separate elaboration phase and semantics-preservation proof are
required by the [v0.1.0 release contract](../../../../../design/s31/language/FUNCTIONAL_V01.md).
