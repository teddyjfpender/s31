# Functional release correspondence

The tests here exercise the v2 direct-gate certificate's independent parser
for one pure named helper. They compare production compilation and checked
source parsing on one, four, and sixteen gate programs, then require exact
normalized and canonical IR equality with handwritten forms. Rejection cases
cover shadowing, unbound arguments, effectful or nested bodies, malformed
types, unused helpers, and commutative order outside the v2 contract.

Run from the repository root:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python/security/functional_release -p 'test_*.py' -q
```

The native [release acceptance](../../../acceptance/compiler_correspondence/functional_release.py)
builds a real package and proves a public claim. These tests do not replace
the native AIR, PCS, or verifier checks.
