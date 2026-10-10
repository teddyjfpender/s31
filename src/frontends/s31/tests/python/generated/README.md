# Generated functional source gate

`test_functional_generated.py` creates 96 deterministic, well-typed S31
programs from a small independent expression grammar. Each program uses a
higher-order helper, a capturing closure, lexical `let`, field arithmetic and
witness-dependent `if`. The generator evaluates the source tree directly with
Python modular integers. The S31 relation oracle separately evaluates the
compiler's emitted graph for both selector values and several boundary input
values; forged public results must fail. Every functional program also has an
explicit first-order form, and the two must produce **identical relation IR**.
The same 96 terms also compile with immediate `(fun …)(argument)` application;
that third source form must emit the same relation and therefore inherits the
independently checked values and forged-output rejection.

`test_functional_arrays_generated.py` adds 64 deterministic four-lane array
programs. Its independent source evaluator covers pointwise addition and
multiplication, rotation through `drop`/`take`/`concat`, nested `let`, shadowed
lambda parameters and witness-dependent `if`. Each program has a functional
closure form and an explicit first-order form; the gate compares their entire
normalized relations and checks six concrete assignments plus forged outputs.
The array corpus has its own pinned SHA-256 identity and seed.

`test_functional_packing_generated.py` exercises array lengths 1, 2, 3, 4,
5, 7, 8, 9 and 15. Each program uses a capturing closure, a static higher-order
call, pointwise arithmetic and a total witness-dependent conditional. The
functional and first-order forms must emit identical normalized IR, while an
independent integer evaluator checks both selector values, field wrap and
forged-output rejection. A separate native gate builds both forms at lengths
3, 5 and 9, compares circuit/AIR geometry, and verifies two proofs per length.

`test_functional_library_generated.py` adds 20 deterministic four-lane math
programs across polynomial evaluation, dot product, matrix-vector and matrix
multiplication, and field powers. Nine more programs cover Poseidon2 leaves of
4, 8, 12 and 16 words and a two-leaf parent. Functional closure calls and
explicit direct forms must produce identical normalized relations. Independent
modular arithmetic and the pinned Poseidon2 reference calculate expected
outputs; changed claims must fail. The 29-source corpus has a pinned SHA-256
identity. These are source/value gates; only the existing acceptance cases
compare native AIR geometry and proofs.

`test_tuple_generated.py` adds 40 deterministic source products, including
nested pairs and chained projections. Each program computes two independently
generated scalar terms and selects a projected component with a constrained
public bit. The source evaluator computes the expected value without reading
compiler internals. Functional and first-order sources must emit identical
relation IR; both bit values, field boundaries, random inputs and false public
claims are checked. The two-source corpus has a pinned SHA-256 identity.

A second gate perturbs valid source text and requires located diagnostics for
rejected mutations. Deep expressions and function types must hit explicit,
located nesting limits. The scalar corpus is deterministic (`SEED = 0x531F00D`);
its two-source SHA-256 identity is pinned in the test. The corpora need no
third-party fuzzing dependency. They cover this functional subset, not the
full standard library or production AIR emission. Native proof and AIR
geometry gates live in `tests/acceptance/` and run in CI.

Run with the normal Python suite:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py'
```
