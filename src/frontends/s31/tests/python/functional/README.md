# Functional source tests

`test_application.py` checks direct application of a parenthesized lambda,
an expression-level `let` that returns a function, and curried functions
returned by named declarations. Each case compares the complete normalized
relation to a first-order source and checks independently calculated field
values and forged public results. Partial operations in eager conditional
arms and invalid applications must still be rejected with source locations.

`test_static_recurrence.py` checks that named functions, returned functions,
and constant-capturing closures passed to `iterate<N>` retain exactly one
`repeat` relation node. It covers `mix4` through higher-order helpers,
independent recurrence values, false public claims, lexical shadowing,
unsupported dynamic captures, and partial inactive branches.
It also compares returned named steps, function factories, identity helpers,
and local `mix4` closures with a direct `mix4` recurrence, and checks that
ordinary `mix4` calls remain outside the source language.

`test_power_chains.py` checks every bounded static-power schedule through
exponent 255 for valid prior powers and no multiplication-count regression
against the binary fallback. It compares `pow<15>` with a handwritten
five-gate graph, then evaluates honest and false field claims across small,
boundary, and large exponents. For large `2^k−1` powers and their shifted
forms, it pins shorter saved-power chains and checks every multiplication's
two previously computed parents. It also compares the 19 reference pairs
with the [kernel-checked certificate](../../../../../../formal/s31/S31/Gadgets/Functional/PowerChains.lean).
For large exponents with small odd factors, it pins shorter factored chains,
checks every saved parent, and compares the emitted `pow<196605>` graph with
the 21-step schedule certified in Lean. A nested functional version using
`power` and `twice` helpers must emit the same 84-gate graph as
four direct calls, with independently checked public outputs.
The eight-lane
[native comparison](../../acceptance/math/power_chain.py) verifies both the
19-step and 30-step `pow<65535>` schedules across four calls.

`test_product_control.py` checks whole-product `if` and `assert_eq` against
explicit fieldwise source. It covers nested nominal records, a mixed bit/u16/M31
record, projection after selection, strict typed public ABI flattening,
inactive partial-operation rejection and nominal type mismatches. The native
gate under `tests/acceptance/functional/product_control.py` proves both
selector values and pins equal complete AIR geometry at 299 raw and 512
padded QM31 rows.

`test_resource_bounds.py` checks that repeated record parameter types share
one abstract effect shape, the 1,024-leaf record ABI budget is enforced before
input expansion, and repeated product assertions are deduplicated and charged
against a bounded expansion budget.

`test_static_sums.py` checks static enum erasure, selected-arm evaluation,
and effect resolution through a generic enum helper. Its safe constructor
matches a direct conditional relation exactly; the risky constructor and an
eagerly partial constructor payload are rejected inside dynamic branches.
It also checks a nested dynamic `if` in an unselected static arm: only a
concrete call choosing that arm makes the partial effect relevant.

`test_pattern_parameters.py` checks tuple and nominal record binders in
named functions and lambdas against direct first-order relations and
independent field values. It covers eager evaluation, duplicate names,
malformed product types, inactive partial operations through returned
closures, and exact `Fn` projection paths through recurrence helpers. A
non-step function in the same nested product must not acquire step context.

Run through the repository's Python discovery command:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py' -q
```
