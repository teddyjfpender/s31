# Pure SSA source to normalized evaluator

[`GeneralLinearSSAProgramEvaluate.lean`](GeneralLinearSSAProgramEvaluate.lean)
relates the bounded, straight-line `m31` source grammar to the **actual**
normalized `Program.evaluate` interpreter. It proves the arithmetic step and
the whole named-environment fold for arbitrary lane values. The final theorem
uses an independently parsed source term, an exact normalized relation graph,
and modeled packed AIR completeness. It does not assume that the source and
interpreter outputs are equal.

## Hand calculation

```s31
circuit subtraction_twice(private a: [m31; 1],
                          private b: [m31; 1]) -> public [m31; 1] {
    let delta = a - b;
    let doubled = delta + delta;
    doubled
}
```

With `a=[3]` and `b=[2]`, the indexed SSA begins with `a` at ID 0 and `b`
at ID 1. The two instructions are `delta = sub(0,1)` at ID 2 and
`doubled = add(2,2)` at ID 3. The modeled arithmetic AIR constrains the
corresponding outputs `d` and `z` by

```text
d - (a - b) = 0             hence d = 1
z - (d + d) = 0             hence z = 2
```

The actual `Program.environment` starts with the two named input values,
evaluates `delta` into the environment, then evaluates `doubled`. The
induction proves that its entry for each numeric SSA ID equals the
corresponding AIR value, including intermediate values that are not selected
as output. `Program.evaluate` also checks that the supplied public output
agrees with `doubled`. The concrete Lean controls prove that `[2]` is
accepted, while a wrong public claim and reversed subtraction are rejected.

## The checked theorem

`checked_pure_source_program_evaluate` works for any admitted number of
instructions and any M31 lane assignment within the bounded pure source
grammar. It consumes the exact source-byte/certificate check and the exact
source-name/relation-graph check. It also requires the executable
`checkPureAlignment` Boolean to bind every certificate instruction to the
same named normalized node. Mutating `sub` to `add` or swapping subtraction
operands makes that Boolean false; Lean checks both controls.

The proof derives the output ID, distinct SSA names, graph equality,
normalized program validation, selected output name, and a complete modeled
AIR trace from those checks. It then proves that every accepted
`Program.evaluate` assignment claims the independently parsed source
meaning. The theorem quantifies over arbitrary field values; it does not
compare two final outputs in a test or certificate field.

Four input-state premises remain explicit:

- `hprivate`: the assignment has exactly the private input names expected by
  the normalized program.
- `hinputs`: mapping the program's inputs through `S31.assigned` yields the
  supplied initial named environment.
- `hcarries`: each initial named value equals the value indexed by the
  source-derived SSA input ID.
- `habent`: future SSA names are absent from that initial environment.

These are necessary for the induction but are **not yet derived from** the
canonical assignment/ABI byte checker in this theorem. Callers must supply
proofs of them. The [finite input-state checker](GeneralLinearSSAInputState.md)
now supplies those proofs from a typed assignment; the JSON-to-typed-assignment
join remains open. The theorem concludes equality for the named public output
value when `Program.evaluate assignment = .ok words`; it does not prove that
`words` are the verifier's authenticated eight public words.

The theorem covers pure `add`, `sub`, and `mul` SSA nodes. The effects
grammar's constants and assertions, helpers, records, other operations,
native gate rows, public-pin ownership, and PCS/FRI proof verification need
separate correspondence joins. The production Python compiler is not proved
equivalent to the Lean source parser. This module proves an interpreter
semantics bridge for the independently checked pure graph, not general
compiler or native prover correctness.

## Recheck

```sh
cd formal/s31
lake build S31.Gadgets.Functional.Correspondence.GeneralLinearSSAProgramEvaluate
lake env leanchecker S31.Gadgets.Functional.Correspondence.GeneralLinearSSAProgramEvaluate
```
