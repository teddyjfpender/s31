# One S31 program, from source to a Lean soundness bound

This page follows the real [fourth-power source](../../examples/arithmetic/functional_square4.s31).
Its public input is four M31 values and its public result is their fourth
powers. The [fixture](../../examples/arithmetic/functional_square4.valid.json)
uses `x = [0, 1, 2, 7]` and claims `[0, 1, 16, 2401]`.

```s31
fn apply_twice(f: Fn([m31; 4]) -> [m31; 4], x: [m31; 4]) -> [m31; 4] {
    let once = f(x);
    f(once)
}

circuit functional_square4(public x: [m31; 4]) -> public [m31; 4] {
    let square = fun(v: [m31; 4]) -> [m31; 4] => v .* v;
    let result = apply_twice(square, x);
    result
}
```

`apply_twice`, the lambda, and `let` disappear during specialization. The
generated relation has **two** elementwise multiplication nodes: `x .* x`,
then the saved result multiplied by itself. Lean checks the exact generated
two-node program and its all-input meaning in
[TextSquare4Proof.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4Proof.lean).
This certificate is regenerated from this source file on each formal audit.
It does not prove that the Python parser preserves meaning for every program.

## What the circuit wires mean

The native Zig compiler's exported addresses are checked against the
[generated topology](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4Native.lean):

```text
scalar inputs:   11, 12, 13, 14
public copies:   11 + 0 -> 3, 12 + 0 -> 4, 13 + 0 -> 5, 14 + 0 -> 6
pack into QM31:  11,12,13,14 -> 22   (three basis muls, three adds)
square rows:     22 .* 22 -> 23; 23 .* 23 -> 24
unpack result:   24 -> 25,28,31,34   (four masks, three inverse muls)
public copies:   25,28,31,34 + 0 -> 7,8,9,10
```

An address identifies one circuit value. For this fixture, wire `22` holds
the four QM31 coordinates `(0, 1, 2, 7)`. The `.*` operation multiplies
coordinates separately, so wire `23` holds `(0, 1, 4, 49)` and wire `24`
holds `(0, 1, 16, 2401)`. The pack uses QM31 basis elements; the unpack masks
one coordinate and multiplies by that basis element's inverse to recover a
base-field value. The output copy gates bind those four values to public
slots. The circuit builder has a separate reserved output slot before S31's
four input and four result slots.

The local AIR relation for each `.*` row has the pointwise-multiply flag set.
For every coordinate `i`, its output residual is
`out[i] - in0[i] * in1[i] = 0`, along with one-hot and Boolean flag
constraints. This equation applies to **arbitrary** intermediate witness
values. [TextSquare4NativeBoundary.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4NativeBoundary.lean)
proves that accepted local rows on the exported input-to-output path force the
public result to be `x⁴`. The native circuit also contains range and
representation gates; the theorem uses the path sufficient for this
functional claim.

## Why AIR arithmetic alone does not join wires

Each AIR row carries its own input values. A row could locally satisfy
`4 * 4 = 16` while claiming it read `4` from an address whose producer wrote
`5`. The Gate lookup compares **address and value together**. For example,
the first square reads `(22, (0,1,2,7))` twice and yields address `23` with
`(0,1,4,49)`; the second square must read that same address and value.

[GateWireMap.lean](../../../../../formal/s31/S31/Gadgets/Air/GateWireMap.lean)
proves that exact balance of all Gate read/yield events plus unique produced
values at declared addresses yields a coherent address-to-value map. Its
scratch counterexample permits two different values at scratch address `40`
while addresses below `35` remain unique. The exported fourth-power path
uses only addresses `0` through `34`.
[The native exporter](../../tools/formal/README.md) checks that this
program has 322 declared variables, 322 arithmetic rows, no permutation
scratch rows, and exactly one builder yield per declared variable. Lean
checks the selected path addresses fit within that exported bound. The
exporter also enumerates producer outputs and checks they are exactly
`0..321`; Lean's modeled producer scan accepts that generated range. The
correspondence between the builder's **values** and the modeled Gate event
list remains a separate premise for path addresses `0..34`.
The production AIR pads this circuit to 512 arithmetic rows. The exporter
checks the actual preprocessed opcode flags, address columns and positive
multiplicities for all 23 selected gates. Padding adds `add` rows before the
`mul` and `pointwiseMul` groups, so the two squares occupy rows 502 and 503.
[TextSquare4TraceRows.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4TraceRows.lean)
uses those positions in the Lean premise; the trace values at those rows still
need to satisfy the local AIR equations.
The [trace-value bridge](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4TraceValues.lean)
models the native writer gathering each arithmetic row's two inputs and
output from one address-indexed value table. Lean proves that the resulting
arithmetic yield events carry exactly that table's values, so these rows no
longer need a separate event-value coverage premise. External component
yields still need a value-table correspondence, and the modeled gather has
not been proved equivalent to executing the Zig writer.
The trace-value bridge also composes with the fixed-forged-witness LogUp
bound: the `(5s² + 2s + 1536) · |QM31|` exceptional-pair count no longer
assumes arithmetic yield values match a separately declared event list.
It still assumes external yields match the value table and that the selected
rows, public pins, address/count checks and other stated AIR premises hold.
An adversarial prover may commit values that were not generated by the honest
trace writer. The gather-model theorem therefore cannot by itself establish
security for arbitrary committed traces; the Gate lookup and STARK verifier
bridges remain necessary.
The [producer-roster proof](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4ProducerRoster.lean)
addresses this malicious-row concern for the worked circuit. The exporter
reads the actual padded preprocessed columns and lists active arithmetic
output addresses; Lean checks that list has no duplicates. Given the modeled
rows match those fixed columns, repeated lookup yields from one row still
have one value even when the prover chose that value arbitrarily. This removes
the honest-gather premise from the fourth-power claim and its ideal-challenge
bound. Committed-column and verifier soundness still need proofs.
[TextSquare4Witness.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4Witness.lean)
constructs and checks every selected local row for the concrete public
input `[0,0,0,0]` and result `[0,0,0,0]`. This shows that the row premises
themselves are satisfiable; it is not a complete native proof witness.
[TextSquare4WitnessAll.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4WitnessAll.lean)
constructs the wire values for **every** four-word input. It proves that the
23 selected AIR rows and public bindings have a satisfying assignment exactly
when the claimed output is `x⁴`. This equivalence covers the selected path;
the remaining native component rows and the full proof protocol have separate
obligations.
[TextSquare4GateJoin.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4GateJoin.lean)
uses this result to remove the assumed shared-wire map from the public-claim
proof. It requires accepted rows for the 23 selected gates, public and
constant events, and coverage by the modeled producer scan.

## What the LogUp proof adds

Gate events are compressed into field elements using challenge values. The
interaction AIR checks reciprocal sums of compressed read and yield tuples.
For a fixed trace with bounded per-address counts and canonical addresses,
the formal LogUp argument proves that a zero reciprocal closure at challenges
outside its explicit exceptional sets implies exact Gate multiset balance.
[TextSquare4ChallengeJoin.lean](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4ChallengeJoin.lean)
composes this with the circuit proof: at good challenges, a forged public
fourth-power claim has **nonzero** closure.

The [source-extracted raw AIR theorem](../../../../../formal/s31/S31/Gadgets/Functional/TextSquare4RawSoundness.lean)
also bounds how many ideal challenge pairs can accept a **fixed forged**
witness. If `s` distinct Gate tuples occur and `n` padded arithmetic rows
occur, the bound is `(5s² + 2s + 3n) · |QM31|` pairs out of `|QM31|²` possible
pairs. This is a count of algebraic exceptional pairs under the theorem's
canonical-address, count, row, public-event and producer premises. It is not
a deployed verifier error rate by itself.
For this source's 512-row AIR, the row-dependent term is `3n = 1536`.

## The remaining proof boundary

The Lean result does not yet establish that native committed trace columns
correspond to every modeled event and row, that verifier openings and
polynomial commitments are sound, or that Fiat-Shamir yields the ideal
challenge distribution. The source compiler's general parser and specializer
also need a proof beyond this regenerated concrete certificate. These are
substantive obligations; [the formal package README](../../../../../formal/s31/README.md)
tracks the other proved components and the full audit commands.
