# Constructive direct-Gate public boundary

`HonestPublicBoundaryWire.lean` proves `checked_direct_public_boundary_exists`
for **every** admitted bounded direct-Gate source byte stream and **every**
four-lane input. It executes the checked SSA program, then builds one address
map (`extendedWire`) with all of these properties at once:

1. Every source instruction satisfies its local packed addition or pointwise
   multiplication polynomial at the expected native source addresses.
2. The four public input pins, four input copies, and six pack rows satisfy
   `InputBoundary`.
3. The selected source output, four basis masks, three inverse multiplies,
   four output copies, and four public output pins satisfy `OutputBoundary`.
4. The selected source address contains the packed source denotation.

The address construction is concrete. Slots 0–21 hold zero/basis constants,
public scalar words, raw input words, and pack intermediates. Slots
`[22, 22 + final.length)` hold the SSA values from deterministic execution.
The next ten slots hold output mask/inverse/result values. `AcceptsTrace`
proves that `final.length = 1 + instruction_count`; the proof checks each
output address against that equation rather than postulating separation.

For example, if the source is `let y = x * x; return y`, the source wire at
address 23 is the packed square. The four mask rows each read address 23;
their results occupy the first, second, fifth, and eighth slots after the
source interval. Three inverse-basis rows recover lanes 1–3, and the copy
rows write public output addresses 7–10. All of those values come from the
same `extendedWire`, so the public output cannot be chosen independently of
the source execution in this modeled witness.

## Exact limit

This is a **constructive modeled circuit witness**, not yet a full native
512-row honest proof trace. It does not assign values to the production
constant-derivation and padding rows, prove exact Gate event balance, or
prove that native commitments/openings authenticate these cells. The separate
full-roster role proof partitions the 512 row positions but does not yet
establish every constant row's fixed address and value. The theorem also
does not formalize PCS/FRI or the native verifier.

## Production correspondence route

A proof-carrying compiler certificate is feasible here. The emitter can
export source bytes, normalized bytes, the full ordered fixed-row roster,
the relevant address/value event plan, and hashes of the native artifacts.
Lean can independently parse and execute the bytes, calculate the expected
roster, and check each exported fixed cell against it. An honest-witness
theorem can then use that checked roster instead of assuming source/row
correspondence. This is a smaller proof target than verifying the Zig
compiler's implementation. The certificate checker must still be connected
to the *actual committed* preprocessed columns and proof package; an
untrusted export of unrelated columns would prove nothing about the native
proof. Gate lookup authentication and PCS/FRI remain separate obligations.
