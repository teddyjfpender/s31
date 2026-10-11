# Mixed source public-output closure

`SourceMixedPublicClosure.lean` gives a **conditional** theorem for the
one-to-eight-call direct mixed source family. The source starts with four
private M31 words `x`, applies 16 rounds of `v := v² + (13 + call)` for each
call, and publishes four sums and four products:

```text
sum[lane]     = final[lane] + x[lane]        (mod 2147483647)
product[lane] = final[lane] * x[lane]        (mod 2147483647)
```

For one call and `x = [1, 2, 3, 4]`, the first round gives
`[14, 17, 22, 29]`. After 16 rounds, `final` is
`[2076908689, 937667208, 532178712, 555828162]`. Thus the eight claimed
words are `[2076908690, 937667210, 532178715, 555828166,
2076908689, 1875334416, 1596536136, 75829001]`.

## What the compiler actually emits

The direct compiler performs **packed** four-lane arithmetic, then extracts
one lane at a time. It never emits a scalar add or multiply row directly at
public addresses 3–10. For `N` calls, the reviewed packed tail uses:

| Wire | Gate address | Meaning |
| --- | ---: | --- |
| Packed private input | 22 | `(x₀, x₁, x₂, x₃)` |
| Packed final chip state | `22 + 10N` | `(final₀, final₁, final₂, final₃)` |
| Packed sum | `23 + 10N` | Packed Qm31 add of those two wires |
| Packed product | `24 + 10N` | Packed Qm31 pointwise multiply of those two wires |

Both packed arithmetic rows read the initial packed input at address 22 as
their first operand and the final packed state at `22 + 10N` as their second.
Addition and pointwise multiplication are commutative, so the stated source
results remain `final + x` and `final × x`.

For each public word, `simd.unpackIdx` emits a pointwise mask by the lane's
unit vector. Lanes 1–3 also multiply by the corresponding basis inverse;
lane 0 uses the mask output directly. The direct output path skips
`m31ToU32`. Finally, `Context.setOutputs` emits an add-with-zero copy row
from the extracted scalar to the reserved public address: 3–6 for sums,
7–10 for products.

`AcceptedRow` requires a selected row in the modeled Gate list, its exact
input and output addresses, the expected fixed opcode, positive output
multiplicity, and acceptance of all nine local Qm31 AIR residuals.
`OutputPath` requires the mask, optional inverse, and copy rows, plus their
unit/inverse constant values. The intermediate addresses are existential
because their allocation is not yet proved here. The two packed arithmetic
rows have exact addresses above. No premise states a public result value.

The verifier's public feeder and each bridge endpoint are Gate **uses**. The
Qm31 rows yield the produced wire values. Exact joint Gate/chip event balance
and unique produced values tie every use to its row result. The local AIR
equations compute the packed sum/product and lane extraction. The copy row
and public feeder identify the extracted word with the verifier's public claim.
`SourceMixedChainSemantics` separately ties the final chip state to the
source repeat sequence. The theorem combines these to derive all eight
public words.

## Explicit remaining proof obligations

This theorem takes the packed Gate values at address 22 and `22 + 10N` as
premises. The companion `SourceMixedPackCorrespondence.lean` derives those
values from the scalar bridge events and two selected six-row `simd.pack`
paths. Together, the theorems still require the selected pack, arithmetic,
unpack, constant, and copy rows to match the native compiler output. The
native proof-to-exact-event reduction, producer uniqueness, and all-row AIR
authentication also remain open. This is a conditional source-to-public
computation theorem, not a certificate for the full production STARK verifier.
The companion `SourceMixedProducerCheck.lean` derives the uniqueness premise
from a successful scan of all modeled logical producer addresses, provided
the native producer roster is shown to match that modeled list.
