# A named helper in the strict release fragment

[`functional.s31`](functional.s31) squares each of four public M31 values
through a named pure helper, then doubles the square. The helper is a static
source abstraction. [`manual.s31`](manual.s31) writes the same two gates
directly. Both compile to the same normalized relation, compact canonical
IR, and native AIR geometry: one pointwise multiplication and one addition.

For input `[0, 1, 2, 7]`, the public result is `[0, 2, 8, 98]` modulo
`p = 2³¹−1`. The first gate constrains `first[i] = x[i]²`; the second
constrains `result[i] = first[i] + first[i]` for each lane. The native proof
also binds the public input and output through the direct-gate AIR.

The strict v2 release certificate independently reparses the functional
source, reconstructs the same positional SSA, checks the complete native
gate topology and fixed root, and preflights the generated verifier key.
The [native acceptance gate](../../../tests/acceptance/compiler_correspondence/functional_release.py)
builds both sources, compares their AIR cost reports, proves the functional
program, verifies it with `verify-release`, and rejects a changed public
result. This fragment covers one pure named helper with one or two
`[m31; 4]` parameters and one `+` or `.*` body operation. General S31
functions remain usable through ordinary compilation and verification; the
strict release certificate's grammar is narrower and documented in
[`source_fragments`](../../../python/package/source_fragments/README.md).

Run from the repository root:

```sh
python3 src/frontends/s31/tests/acceptance/compiler_correspondence/functional_release.py
```
