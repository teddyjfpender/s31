# Mixed-chain main-cell and shape certificate

`SourceMixedPinnedMainCells.lean` replaces the ten abstract `ValueAt`
assumptions in each pinned N=1/N=8 schedule with exact output-main-cell
equalities in a decoded 512-row trace. `valueAt_of_decoded_output` is the
general bridge: a row whose fixed output address is `a`, whose fixed output
multiplicity is positive, and whose decoded output main value is `v` supplies
`ValueAt boundary a v` when that trace is the boundary's Gate row list. It
uses no Gate AIR, lookup balance, or challenge assumption.

The N1 and N8 fixed exports kernel-check the address and positive
multiplicity for these producer rows (all indices are zero based):

| Value | N1 row → address | N8 row → address |
| --- | --- | --- |
| Packed initial state | 2 → 22 | 2 → 22 |
| Packed final state | 5 → 32 | 26 → 102 |
| Zero | 15 → 0 | 36 → 0 |
| Unit lanes 0, 1, 2, 3 | 16 → 1, 461 → 15, 474 → 2, 489 → 16 | 37 → 1, 412 → 15, 446 → 2, 461 → 16 |
| Inverse unit lanes 1, 2, 3 | 488 → 37, 494 → 40, 484 → 43 | 460 → 107, 466 → 110, 456 → 113 |

`N1MainPins` and `N8MainPins` state the corresponding output-main-value
equalities. The `n1_local_schedule_of_main_pins` and
`n8_local_schedule_of_main_pins` theorems then construct the full
`LocalPublicSchedule` from those pins, exact fixed-column equality, and an
empty baseline-yield list. The pinned boundary already supplies the row list,
round count, addresses, constants, and first input state by construction.

`n1_pinned_source_shape` and `n8_pinned_source_shape` additionally derive
the full 512-row count, total output multiplicity, and 16-round conditions
from the fixed export and constructed boundary. They assume only that the
template has no extra baseline uses or yields. This supplies the
`SourceShape` required by the later challenge-count bound.

The main-cell equalities are **premises about committed trace values**, not
consequences of local arithmetic AIR. For example, a Gate row with all three
addresses equal to zero and `.add` opcode can have input values 2 and 3 and
output value 5 while satisfying its local arithmetic equation. Equating
those three values needs lookup coherence, whose failure is exactly what the
challenge-bound argument studies. Assuming exact lookup balance here would
make that argument circular. A native proof-to-decoded-trace authentication
and source-to-boundary event correspondence are also still required.

Focused checks:

```sh
(cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedPinnedMainCells)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Air.SourceMixedPinnedMainCells)
```
