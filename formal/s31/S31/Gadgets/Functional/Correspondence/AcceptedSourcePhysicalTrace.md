# Checked source rows in a 512-row trace

`AcceptedSourcePhysicalTrace.lean` composes the constructive source-cell
witness, synthetic 512-row arithmetic completion, and independently proved
canonical address bounds.

For **every** accepted direct program and **every** four-lane input,
`checked_direct_source_trace_exists` constructs one decoded 512-row trace and
one source wire assignment such that:

- all nine installed local arithmetic polynomials vanish on every row;
- every projected source fixed cell matches its physical row, opcode,
  operand addresses, output address, and output multiplicity exactly;
- the selected source wire equals the result parsed from the source bytes.

The source row count, physical positions, and numeric address bounds come
from exact accepted source and normalized bytes. The theorem does not take
an externally supplied trace, wire map, row count, or canonicality premise.
It covers all admitted source instruction counts from one through sixteen.

The remaining rows of this constructed trace are deliberately synthetic
`0 + 0 = 0` padding. In the actual direct-Gate compiler they contain
constant generation, basis values, public input packing, public output
unpacking, copies, and padding. Therefore this theorem **does not prove**
native full-roster equality, input/output public pins, ideal Gate balance,
or interaction/PCS verification. It establishes nonvacuity for the complete
local arithmetic relation with exact source fixed cells, and isolates the
source-independent backbone as the next constructive obligation.

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.AcceptedSourcePhysicalTrace)
(cd formal/s31 && lake env leanchecker -v S31.Gadgets.Functional.Correspondence.AcceptedSourcePhysicalTrace)
```
