# Executable source audit tests

`general_linear_ssa_effects_certificate.py` runs the strict Lean effects
certificate gate on the production affine/assertion fixture and rejects
arithmetic, assertion, JSON-canonicalization, and size mutations. Build and
run from `formal/s31`:

```sh
lake build s31-general-linear-effects-certificate-check
python3 tests/audit/general_linear_ssa_effects_certificate.py
```

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

`native_canonical_digest.py` builds two fresh direct-gate packages: five-lane
subtraction and reversed-operand addition. It first requires the Lean audit
to accept source, normalized relation, and compact canonical IR bytes. It
then hashes those bytes and compares the result with each package's native
cost report and verification key. This covers the unsorted subtraction and
sorted commutative paths in the native canonicalizer. It does not prove the
native SHA-256 implementation or verifier correct.

```sh
python3 formal/s31/tests/audit/native_canonical_digest.py
```
