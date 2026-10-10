# S31 Python frontend

| Directory or entry point | Responsibility |
| --- | --- |
| [`language/`](language/README.md) | Lexing, parsing, source types, whole-program elaboration, effect checks and specialization. |
| [`library/`](library/README.md) | Compiler-owned standard and math libraries, including typed relation construction. |
| `text_frontend.py` | Stable source compilation API over the language phases. |
| `s31.py` | Package, proof trial, inspection and command-line entry point. |
| `oracle.py`, `poseidon2_oracle.py` | Independent value checks used by trials and tests. |
| `proof_privacy.py` | Proof-mode policy and package checks. |
| `s31_stdlib.py`, `s31_mathlib.py` | Compatibility imports for existing callers. |

The compiler fingerprint includes every implementation file under `language/`
and `library/`, plus the compatibility imports, package entry point and pinned
native assets. The standard-library lock separately records the exact
compatibility and implementation sources used in a text package. Source
functions and tuples are specialized before the normalized relation reaches
Zig; the generated native verifier is bound to that relation and package.
