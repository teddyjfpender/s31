# Physical Gate rows to source arithmetic

[`StructuralPhysicalAirBridge.lean`](StructuralPhysicalAirBridge.lean) connects
the general bounded source theorem to **physical row cells**. A row contains
four fixed opcode selectors, three fixed variable addresses, the fixed LogUp
multiplicity, and three four-coordinate base values. The theorem requires each
source-owned add, subtraction, or pointwise multiplication gate to have a row
whose selector, addresses, and twelve base coordinates match the checked
native graph. It then derives the graph's `NativeAirRows` premise from the
nine local AIR residuals evaluated on those physical cells.

For example, consider two active lanes of `z = (x - y) .* (x - y)` with
`x = [5, 8]` and `y = [1, 3]`. The inactive packed coordinates are zero.
Suppose the checked graph assigns addresses 11 and 12 to `x` and `y`, address
13 to `d`, and address 14 to `z`. The two source gates require these cells:

| Row | Selectors `(add, sub, QM31 mul, pointwise mul)` | Addresses `(left, right, result)` | Base left | Base right | Base result |
| --- | --- | --- | --- | --- | --- |
| Sub | `(0, 1, 0, 0)` | `(11, 12, 13)` | `[5, 8, 0, 0]` | `[1, 3, 0, 0]` | `[4, 5, 0, 0]` |
| Mul | `(0, 0, 0, 1)` | `(13, 13, 14)` | `[4, 5, 0, 0]` | `[4, 5, 0, 0]` | `[16, 25, 0, 0]` |

The first five residuals require one one-hot selector and four Boolean
selectors. The remaining four require the result to equal the selected
arithmetic operation in every coordinate. Thus the Sub row proves
`d = x - y`, and the pointwise row proves `z = d .* d` for any satisfying
values at those addresses. If a source gate is reused by common subexpression
elimination, several source steps can cite the same row. The multiplicity
cell is carried in the physical row but belongs to the separate Gate LogUp
argument.

The executable [public](../../../../tests/audit/structural_committed_air_join.py)
and [private](../../../../tests/audit/structural_private_committed_air_join.py)
audits now check the source gate rows directly from physical columns, including
one-hot selectors, exact addresses, canonical operands, and the arithmetic
equation. The public audit compares all 8 × 512 fixed and 12 × 512 base cells
to the native `writeBase` export and recommits them to the accepted proof's
roots. The private audit keeps witness-bearing graph and cells in a temporary
test-only scope and checks them through its noninstalled native audit path.

The theorem is conditional on exact graph-to-row coverage and local AIR
acceptance. Neither the theorem nor these finite honest-prover audits derives
those premises from an arbitrary accepted proof. The missing joins remain
native Gate lookup authentication, public/private producer ownership for all
compiler profiles, and PCS/FRI soundness of committed cells and residuals.
