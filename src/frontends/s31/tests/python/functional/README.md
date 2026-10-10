# Functional source tests

`test_application.py` checks direct application of a parenthesized lambda,
an expression-level `let` that returns a function, and curried functions
returned by named declarations. Each case compares the complete normalized
relation to a first-order source and checks independently calculated field
values and forged public results. Partial operations in eager conditional
arms and invalid applications must still be rejected with source locations.

Run through the repository's Python discovery command:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python -p 'test_*.py' -q
```
