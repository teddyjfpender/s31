# S31 Python frontend

| Directory or entry point | Responsibility |
| --- | --- |
| [`language/`](language/README.md) | Lexing, parsing, source types, whole-program elaboration, effect checks and specialization. |
| [`library/`](library/README.md) | Compiler-owned standard and math libraries, including typed relation construction. |
| [`inspection/`](inspection/README.md) | Verified-package cost and source-equation reports. |
| [`package/`](package/README.md) | Compiler identity, atomic package builds and artifact/key verification. |
| [`runtime/`](runtime/README.md) | Native proof trials, profile comparisons and recursive fold-chain audits. |
| `text_frontend.py` | Stable source compilation API over the language phases. |
| `s31.py` | Command-line entry point and stable Python API imports. |
| `oracle.py`, `poseidon2_oracle.py` | Independent value checks used by trials and tests. |
| `proof_privacy.py` | Proof-mode policy and package checks. |
| `s31_stdlib.py`, `s31_mathlib.py` | Compatibility imports for existing callers. |

The compiler fingerprint includes every implementation file under `language/`
`library/`, `inspection/`, `package/` and `runtime/`, plus the compatibility imports, CLI entry point and pinned
native assets. The standard-library lock separately records the exact
compatibility and implementation sources used in a text package. Source
functions and tuples are specialized before the normalized relation reaches
Zig; the generated native verifier is bound to that relation and package.
