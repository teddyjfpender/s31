# CLI checks

Run the focused command-line tests from the repository root:

```sh
python3 -m unittest discover -s src/frontends/s31/tests/python/cli -p 'test_*.py'
```

These tests exercise the executable CLI and the source-only compiler path.
They do not build a native prover or certify AIR/proof soundness.
