# Executable source audit tests

`test_source_function_check.py` exercises the optional Lean
`s31-source-function-check` executable against production S31 text
compilation and the independent Python source parser. It checks exact
canonical relation bytes for 96 programs and rejection of source, relation,
formatting, reserved-name, and shadowing mutations.

Run from `formal/s31` after building the executable:

```sh
lake build s31-source-function-check
python3 -m unittest discover -s tests/audit -p 'test_source_function_check.py' -q
```

The test samples the compiler boundary; the theorem in
`S31/Gadgets/Functional/Correspondence/SourceFunctionBytes.lean` establishes
the mathematical source, normalized-name, and packed-row relationship for
every program the bounded Lean parser accepts.
