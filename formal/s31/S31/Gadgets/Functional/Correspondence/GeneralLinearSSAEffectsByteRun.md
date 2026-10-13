# Exact byte gate for an effectful SSA run

[`GeneralLinearSSAEffectsByteRun.lean`](GeneralLinearSSAEffectsByteRun.lean)
joins the bounded effectful source parser, exact certificate JSON, exact
normalized relation JSON, canonical public ABI and assignment JSON, and
the actual `Program.evaluate` interpreter. Supported arithmetic is `add`,
`sub`, `mul`, `add_const`, and `mul_const`; source assertions are ordered
equalities between named M31 arrays. The relation uses transparent proof
mode.

The gate gives one exact assignment byte string to the independent ABI
checker and strict typed parser. Its finite input-state check binds every
public and private lane to the initial indexed SSA values and requires
future node names to be absent. Exact graph alignment checks every ordered
operation, operand, constant, assertion pair, and selected output index.
Successful `Program.evaluate` includes the real assertion loop. The gate
does not compare source and interpreter final values as a condition.

For every accepted run, `checked_effects_byte_run` proves that the public
claim is accepted by the independently parsed source denotation, including
**all source assertions**; that raw statement bytes are the ordered public
input/output words; and that the typed assignment parsed from exact bytes
is accepted by the normalized interpreter. The proof derives modeled
arithmetic AIR rows from the checked source certificate for arbitrary M31
inputs. Interpreter acceptance forces assertion polynomials, and its
selected public output equals the source computation.

The handwritten fixture computes `shifted = x + 7`, `scaled = shifted * 9`,
asserts `y = scaled`, then returns `y - x`. For `x=[1,2,3]` and
`y=[72,81,90]`, the public output is `[71,79,87]`. The executable accepts
that fixture and rejects nine mutations: changed private input, wrong
output, changed arithmetic operation or constant, changed assertion,
duplicate/noncanonical assignment keys, changed source assertion, and
changed public bytes.

The theorem covers the bounded source grammar and modeled packed AIR
semantics. It does not prove production Python parser equivalence, native
gate-row custody, native public-pin ownership, or PCS/FRI verification.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsByteRun \
  s31-general-linear-effects-byte-run-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsByteRun
python3 tests/audit/general_linear_effects_byte_run.py
```
