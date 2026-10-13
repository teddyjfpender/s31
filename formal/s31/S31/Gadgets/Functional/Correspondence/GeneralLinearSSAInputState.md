# Checking the interpreter's initial SSA state

[`GeneralLinearSSAInputState.lean`](GeneralLinearSSAInputState.lean) closes
the explicit input-state premises of the [pure normalized evaluator bridge]
with a finite executable check over a **typed** `S31.Assignment`.

For each declared input, `checkInputState` runs the same `S31.assigned`
operation as the real `Program.environment` initializer. It checks that the
private field names are exact, that every indexed SSA input name looks up to
the corresponding M31 lane array, and that no future instruction name is
already present. It returns the actual computed input environment. The Lean
theorem `checked_input_state` derives the four premises `hprivate`,
`hinputs`, `hcarries`, and `habent` from successful execution. The joined
`checked_pure_source_program_evaluate_with_state_check` theorem then uses
these facts in the arbitrary-input structural evaluator proof.

For example, with `a=[3]`, `b=[2]`, and names
`[a,b,delta,doubled]`, the check accepts the two private inputs. It rejects
`b=[7]` when the source-indexed value is `[2]`, rejects a future SSA name
that aliases `a`, and rejects a missing `b` input. These four cases are
kernel-checked as `input_state_*` controls.

The check accepts a typed assignment supplied to Lean. It does **not yet**
prove that canonical assignment JSON bytes decode to this exact typed object;
the existing public ABI byte checker and this gate must be joined for that
claim. It also does not authenticate native public pins or PCS/FRI proof
rows. No final output is compared by this input-state gate.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAInputState
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAInputState
```

[pure normalized evaluator bridge]: GeneralLinearSSAProgramEvaluate.md
