# Generated functional source gate

`test_functional_generated.py` creates 96 deterministic, well-typed S31
programs from a small independent expression grammar. Each program uses a
higher-order helper, a capturing closure, lexical `let`, field arithmetic and
witness-dependent `if`. The generator evaluates the source tree directly with
Python modular integers. The S31 relation oracle separately evaluates the
compiler's emitted graph for both selector values and several boundary input
values; forged public results must fail. Every functional program also has an
explicit first-order form, and the two must produce **identical relation IR**.

`test_functional_arrays_generated.py` adds 64 deterministic four-lane array
programs. Its independent source evaluator covers pointwise addition and
multiplication, rotation through `drop`/`take`/`concat`, nested `let`, shadowed
lambda parameters and witness-dependent `if`. Each program has a functional
closure form and an explicit first-order form; the gate compares their entire
normalized relations and checks six concrete assignments plus forged outputs.
The array corpus has its own pinned SHA-256 identity and seed.

A second gate perturbs valid source text and requires located diagnostics for
rejected mutations. Deep expressions and function types must hit explicit,
located nesting limits. The scalar corpus is deterministic (`SEED = 0x531F00D`);
its two-source SHA-256 identity is pinned in the test. Neither corpus has
no third-party fuzzing dependency. It covers this small functional subset,
not the full standard library or production AIR emission. Native proof and
AIR geometry gates live in `tests/acceptance/`.

Run with the normal Python suite:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py'
```
