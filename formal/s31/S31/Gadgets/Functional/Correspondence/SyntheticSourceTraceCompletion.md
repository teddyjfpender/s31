# Synthetic 512-row source completion

`SyntheticSourceTraceCompletion.lean` turns the general honest source-cell
assignment into an actual `Trace 9` with 512 decoded fixed rows and 512 main
rows. It is an **arithmetic completion** of the source slice, not the native
prover's complete direct-Gate witness.

For each checked source cell, the constructor places its projected selector
and addresses at the source-determined physical row. Its twelve main cells
read two QM31 operand values and one output value from the **same** honest
SSA wire assignment. Each of the other physical rows is a synthetic add row
with zero operands and zero output. The proof `arithmetic_complete` checks
the installed nine arithmetic polynomials on **all 512 rows**, using the
source-cell equations for selected rows and `0 + 0 = 0` for the rest.

`accepted_direct_arithmetic_trace_exists` needs only exact accepted source
and normalized bytes plus an input. It constructs a wire function, parsed
output, and 512-row trace whose local arithmetic roots vanish. It does not
assume that a trace or any arithmetic roots exist. The source output wire
equals the language denotation. `selected_source_fixed_of_canonical_bounds`
also proves exact selected fixed-cell equality if the projected Nat addresses
and multiplicities are canonical M31 integers. Byte admission already proves
the selected row positions are distinct and below 512; a general Lean proof
of those address/count bounds remains separate.

For `let y = x .* x; y`, its pointwise source cell is placed at row 503.
The constructor reads wire 22 twice and writes wire 23, so input
`[0, 1, 2, 7]` produces `[0, 1, 4, 49]` at that row. All other synthetic
rows satisfy their local addition equation with zero values.

The native 512-row fixed roster contains a large source-independent
constant network plus input packing, output unpacking, public copy rows,
and padding. This module replaces all of those with zero add rows, so it
**does not establish native fixed-roster fidelity, public input/output
binding, Gate producer/use balance, or interaction/PCS correctness**. The
next constructive step is to replace the synthetic rows with a general
source-independent backbone and prove its values, canonical addresses,
and event multiplicities.

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.SyntheticSourceTraceCompletion)
(cd formal/s31 && lake env leanchecker -v S31.Gadgets.Functional.Correspondence.SyntheticSourceTraceCompletion)
```
