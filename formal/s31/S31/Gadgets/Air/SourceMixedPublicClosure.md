# Mixed source public-output closure

The theorem in `SourceMixedPublicClosure.lean` is a conditional proof for the
reviewed one-to-eight-call source family. The source starts with four private
M31 words `x`, applies each call's 16 rounds of `v := v² + (13 + call)` and
publishes two four-word arrays:

```text
sum[lane]     = final[lane] + x[lane]        (mod 2147483647)
product[lane] = final[lane] * x[lane]        (mod 2147483647)
```

For example, with one call and `x = [1, 2, 3, 4]`, the first round gives
`[14, 17, 22, 29]`. After all 16 rounds the final state is
`[2076908689, 937667208, 532178712, 555828162]`; the public arrays are
`sum = [2076908690, 937667210, 532178715, 555828166]` and
`product = [2076908689, 1875334416, 1596536136, 75829001]`.

## How the proof reaches the public claim

The model uses one independent M31 lane per `lane` index. The first private
input lives at Gate addresses 11–14. The final chip output of call `c`
lives at addresses `23 + 10c` through `26 + 10c`. The verifier's public
feeder publishes eight words at addresses 3–10, with sum at 3–6 and product
at 7–10. A selected tail row for each lane has the following topology:

| Row | First input | Second input | Output | Local opcode |
| --- | --- | --- | --- | --- |
| `sum[lane]` | final chip address | private input address | `3 + lane` | Qm31 add |
| `product[lane]` | final chip address | private input address | `7 + lane` | Qm31 pointwise multiply |

`TailRow` asks for an actual row in the modeled Gate list with those
addresses, the selected opcode, positive output multiplicity, and all nine
Qm31 local AIR residuals zero. It does **not** stipulate the row's operand or
output values. Exact joint Gate/chip event balance makes every row read a
produced Gate tuple. Unique producer values force that tuple to agree with
the bridge's final/private input value; the same rule forces the row output
to agree with the public feeder. The local AIR relation then computes the
public word. `SourceMixedChainSemantics` separately proves that the final
chip state equals the source's `N`-call evaluation. Combining those facts
gives both arrays for all four lanes.

The native compiler-to-model correspondence for the eight tail rows, the
native proof-to-exact-event reduction, Gate producer uniqueness, and
authentication of local AIR rows remain explicit premises. This theorem
does not certify the production verifier or the whole STARK protocol.
