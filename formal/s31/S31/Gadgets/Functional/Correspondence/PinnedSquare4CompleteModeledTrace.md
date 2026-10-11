# Pinned square4 complete modeled trace

`PinnedSquare4CompleteModeledTrace.lean` applies the reusable physical-trace
composition to the checked-in `functional_square4` source. The source and
normalized JSON are converted to literal `UInt8` lists and checked against the
source parser. The 485 native constant and padding rows pass the executable
island certificate. The complete 512-row address ledger passes with feeder
addresses `2..10` and no external yields.

For **every four-lane M31 input**, Lean then constructs one coherent modeled
trace. All 512 row positions are covered; every fixed cell matches the checked
roster; all nine local arithmetic equations per row vanish; the selected
output equals the source evaluation; and the trace's own ideal Gate event lists
balance. The proof discharges the three Boolean premises of the generic
composition for this source, rather than assuming them in its final theorem.

This is an honest synthetic witness. The fixed rows and value table came from
native diagnostic exports, but this theorem does not establish that a prover's
PCS commitment opens to the constructed rows. It also does not prove LogUp
collision bounds, Fiat–Shamir security, or FRI soundness. The nine feeder
addresses are the pinned direct-Gate public component's addresses; a general
native feeder correspondence theorem is still open.
