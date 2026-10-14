# A source `add_const` through the physical AIR

The `physical_add_const` fixture has a private five-lane M31 input
`a = [1,2,3,4,5]` and the source node `shifted = a + 7`. A second source
name repeats the same expression. Canonical optimization merges those two
names into one node. The public result is `[8,9,10,11,12]`.

The compiler interns one QM31 broadcast constant `(7,7,7,7)` and emits one
add gate for each packed word. The first gate processes lanes 0–3. The second
processes lane 4; its other three lanes are padding and do not become source
results. The v3 physical certificate names the canonical node, its source
operand node, the source constant, the interned constant wire address, both
lists of packed input/output addresses, the first physical gate's `in1`
address, and the exact physical add interval.
In the accepted fixture, the constant address is **13** and the two rows are:

| AIR row | Input address | Constant address | Output address | Active lanes |
| ---: | ---: | ---: | ---: | --- |
| 0 | 11 | 13 | 14 | 0–3 |
| 1 | 12 | 13 | 15 | 4 |

`shifted` and `same_shifted` both resolve to canonical node **1** and the
same physical interval `[0,2)`. There are only two source-owned binary rows.
The native audit checks every gate in that interval, in order, against those
addresses and the installed preprocessed selector/address columns. It also
checks that the interval contains exactly `ceil(length / 4)` rows and that
the node owns no subtract, multiply, or pointwise multiply rows.

For each row, the installed AIR has four fixed selector columns and nine
local residuals. This node's selector is `(1,0,0,0)`. The four output
residuals are `z_i - (x_i + y_i) = 0`, one for each QM31 coordinate. The
constant wire is the row's `y` input. Once its **value** is established as
`(7,7,7,7)` and Gate lookup joins it with the row, the fifth active lane
necessarily satisfies `z_0 = x_0 + 7`, regardless of the other three lanes.

`GateAddConstComposition.lean` proves this for any source length, not just
five. It composes the exact native residual tree from
`NativeQm31AirProof.lean` with the source lane-to-packed-row map and the
M31-to-field embedding. The theorem's assumptions state the fixed operation
selector, the local AIR residuals, each active source input/output lane's
trace-cell mapping, and the broadcast constant trace value. It concludes
`output[j] = input[j] + c` in S31 M31 arithmetic for every active `j`.

For literal `7`, [the finalization join](GateAddConstSevenFinalization.md)
derives the broadcast cell's **value** from 15 native finalization rows and
the public `u` anchor. Its Lean theorem replaces this module's constant-value
assumption with the finalization AIR premises. The row operand/output cells,
Gate lookup join, and PCS/FRI proof-cell authentication still have explicit
premises. The audit reconstructs one accepted proof from a supplied witness;
it does not prove that every accepted proof has those same cells.

The controls change the certificate's constant, constant address (including
an in-range 13→12 edit), input address, and row count; all are rejected.
Python checks that the reported physical `in1` equals the interned constant
address, so the single-field 13→12 edit fails structurally. A joint edit of
both addresses disagrees with the finalization path or the native receipt's
SHA-256 binding to the exact emitted certificate bytes. The native diagnostic
is the authority for these physical
values: it compares every gate's `in1` with the interned constant and the
installed fixed input column. Python does not independently reconstruct the
physical Gate trace or prove its semantics. The controls also change the
source constant while keeping the proof and statement fixed; native
reconstruction rejects that combination.

```sh
python3 src/frontends/s31/python/s31.py build \
  scripts/compiler/fixtures/physical_add_const.s31.json \
  --out /tmp/s31-add-const --lowering gate
python3 src/frontends/s31/python/s31.py prove \
  /tmp/s31-add-const \
  scripts/compiler/fixtures/physical_add_const.valid.json \
  /tmp/s31-add-const.proof
python3 scripts/compiler/gate_claim_trace_controls.py \
  /tmp/s31-add-const /tmp/s31-add-const.proof \
  /tmp/s31-add-const.proof.statement.json \
  scripts/compiler/fixtures/physical_add_const.valid.json
(cd formal/s31 && lake build S31.Gadgets.Air.GateAddConstComposition)
```
