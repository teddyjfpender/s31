# N=4 mixed circuit-to-chip handoff audit

Status: **source-bound witness and native base-trace audit; no N=4 mixed
proof admission**. The [four-call source](../../../src/frontends/s31/examples/boundary/mixed_four.s31.json)
and [assignment](../../../src/frontends/s31/examples/boundary/mixed_four.valid.json)
are executable fixtures.

The audit reconstructs the source, canonical IR, compiled call addresses,
versioned component descriptor, registered pair/many AIR handle geometry,
fixed-column root, and circuit topology. It then compiles the assignment into
that topology. The first two calls select pair chip and bridge base writers;
calls two and three select many chip and bridge base writers.

For each of four lanes and each of 16 rows, the test checks the chip's stored
input and output against an independently calculated M31 recurrence:

```text
state[0] = circuit value at source-derived input address
state[t+1] = (state[t]² + call.constant) mod 2147483647
state[16] = circuit value at source-derived output address
```

It also checks that the eight bridge columns contain those four inputs and
four outputs, and that the circuit base trace's eight public output values
match the language evaluator and claimed statement. The fixture chains each
call's output into the next call's input. A controlled bad endpoint value,
changed source, reordered slots, wrong component role, resealed program
binding, and wrong public claim are rejected.

This exercises witness construction and the concrete native base trace
writers. It does **not** commit those columns, evaluate the AIR quotient under
a transcript challenge, or verify a STARK proof. The pinned engine's
`direct_mixed_arithmetic` still fixes `n_calls = 3` and seven components in
its prover, verifier, claimed-sum handling, transcript, and PCS roster.
Admitting N=4 needs a new engine profile with nine components, a distinct
domain-separated transcript and envelope, explicit source/descriptor and
fixed-root reconstruction before decoding, and honest and adversarial proof
tests. Reusing the N=3 wire tag would make profile separation ambiguous.
The audit provides no witness confidentiality guarantee.
