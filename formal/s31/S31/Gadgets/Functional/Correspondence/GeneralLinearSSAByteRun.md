# Exact byte gate for a pure SSA run

[`GeneralLinearSSAByteRun.lean`](GeneralLinearSSAByteRun.lean) composes the
independent source-byte, certificate, normalized relation, public ABI,
assignment, and interpreter checks for the bounded pure `m31` grammar.
The executable `checkPureByteRun` accepts a source file, canonical JSON
artifacts, 32 raw public-statement bytes, and the field values under review.
It runs the actual `Program.evaluate` on a typed assignment parsed from the
**same exact assignment JSON bytes** that the ABI checker reads.

It checks every instruction's named graph alignment and the finite initial
SSA state, requires the typed public output to equal the ABI claim, and
requires the interpreter's returned eight words to equal the ABI's ordered
public words. It never compares the interpreter's computed output against
the source term's output as a checker condition.

`checked_pure_byte_run` proves for every accepted run:

1. The independent source-byte denotation is the parsed source term.
2. The claimed public output equals that term's evaluation for the supplied
   M31 field inputs.
3. The raw statement bytes encode the exact ordered public words.
4. The typed assignment comes from the exact canonical JSON bytes, and the
   actual normalized interpreter accepts it.

The proof uses the general named-environment induction and the finite
input-state theorem; it does not assume the final output equality it
concludes. The handwritten `a=[3], b=[2]` subtraction example and modeled
AIR equations are in the [interpreter bridge]. The reviewed five-lane
fixture is admitted by `s31-general-linear-byte-run-check`. Seven byte
mutations are rejected: changed private input, changed public output,
duplicate assignment key, noncanonical JSON spacing, changed normalized
operation, reversed source subtraction, and nonzero public padding.

This remains a **bounded pure** source grammar: no constant arithmetic,
assertions, records, general calls or native chip scheduling. The field
inputs supplied to the checker are checked against the typed assignment,
but this Lean gate does not prove the production Python compiler equivalent
to the independent Lean source parser. The raw public bytes are checked as
supplied; native verifier public-pin ownership and PCS/FRI proof
authentication remain separate.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAByteRun \
  s31-general-linear-byte-run-check
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAByteRun
python3 tests/audit/general_linear_byte_run.py
```

[interpreter bridge]: GeneralLinearSSAProgramEvaluate.md
