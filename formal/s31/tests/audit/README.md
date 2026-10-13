# Executable source audit tests

`structural_derivation_lean.py` runs the generic M31 typed-tree erasure gate
over generated tuple, helper, constant, assertion, and private-input programs.
It checks compiler/Python/Lean agreement, re-sealed wrong erasures, exact
field shape, and unsupported fragments. The same generated programs also run
the `statement` mode with concrete private assignments and public statements;
wrong private values or public results are rejected. The separate native
helper/tuple fixture verifies an actual direct-Gate proof and exercises this
mode against its source package. The statement-mode theorem covers any
program admitted by the bounded Lean grammar, while native private witness
and PCS authentication remain separate obligations:

```sh
lake build s31-general-linear-structural-check
python3 tests/audit/structural_derivation_lean.py
```

`general_linear_public_abi.py` checks three source-derived certificate
fixtures against exact `.s31` bytes, ABI, assignment, and 32-byte public word
files. It includes two public inputs, a private input, zero padding, and 36
rejection controls for arithmetic, constants, assertions, proof mode, circuit
name, and ABI. A source and relation renamed together remain accepted because
this Lean gate does not recompute the certificate's SHA-256 fields. Build the
runtime gate first:

```sh
lake build s31-general-linear-public-abi-check
python3 tests/audit/general_linear_public_abi.py
```

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
