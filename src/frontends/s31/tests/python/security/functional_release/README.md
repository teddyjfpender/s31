# Functional release correspondence

The tests here exercise the v2 direct-gate certificate's independent parser
for up to eight pure named functions in an acyclic call graph. They compare production compilation and checked
source parsing on one, four, and sixteen gate programs, and on helpers with
local lets, repeated and nested calls, and different return forms. They require exact
normalized and canonical IR equality with handwritten forms. Rejection cases
cover shadowing, unbound arguments, effectful or nested bodies, malformed
types, unused helpers, and commutative order outside the v2 contract.
Lexical-let tests compare nested, shadowed and returned-alias expressions
with the production compiler and direct gate sources, and reject malformed
or unbound expressions and generated-name collisions. An unused bound
arithmetic expression must still emit its eager gate.
The higher-order cases pass named unary functions through `Fn` parameters,
lexical bindings, and circuit aliases. They compare the exact one-gate result
with handwritten arithmetic and reject an array used as a function, a function
used as an array, shadowing, an unbound function, or a function at the public
output. `test_static_lambda.py` checks a bounded pure unary lambda body,
including passage through `Fn`, exact gate equality with handwritten source,
capture across lexical shadowing, and rejection of unbound or ill-typed forms.
It also compares an inline lambda passed to a higher-order helper with
handwritten gates and production compilation, and rejects malformed inline
lambda types or captures.
Other lambda operations and general closures remain outside this bounded
certificate.
The separate `test_lexical_corpus.py` exhausts all 30 chains of one to four binders with
add/multiply chains, including static helper calls and parenthesized source
expressions. Every case must match both production compilation and a direct
handwritten gate schedule byte for byte at the normalized relation level.
`test_lexical_mutations.py` then makes 2,000 fixed token mutations to the
native lexical fixture. The checker must reject malformed sources without
crashing; all eleven mutations it still accepts must compile to exactly its
independently reconstructed relation.

Run from the repository root:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python/security/functional_release -p 'test_*.py' -q
```

The native [release acceptance](../../../acceptance/compiler_correspondence/higher_order_release.py)
builds a real package and proves a public claim. These tests do not replace
the native AIR, PCS, or verifier checks.
