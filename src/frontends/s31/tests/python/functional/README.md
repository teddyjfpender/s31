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
boundary, and large exponents.

Run through the repository's Python discovery command:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py' -q
```
