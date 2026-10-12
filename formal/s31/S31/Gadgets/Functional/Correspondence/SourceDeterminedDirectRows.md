# Source determined direct Gate rows

For the bounded four-lane direct Gate source fragment, the 512 arithmetic
rows have a fixed budget. One row is subtraction, 27 are ordinary
multiplication, and eight are fixed pointwise multiplication. Each checked
source `.*` instruction consumes one further pointwise row. The rest are
addition rows, including constants and padding. Thus the source certificate
fixes the add partition at `476 − sourceMulCount`.

`SourceDeterminedDirectRows.lean` proves this count and the exact 512-row
partition from accepted direct source and normalized bytes. The canonical
alias checker gets the same result because aliases and parentheses emit no
arithmetic producers. A second count satisfying the profile equation must
equal the source-derived count. The direct-source theorem then establishes
that all projected source, input-pack and output-unpack rows are distinct and
within 512 positions, without accepting an independent row-count parameter.
Canonical alias bytes also determine a complete source instruction plan and
distinct modeled source and public row positions.

For a one-product source such as `let y = x .* x; y`, the source-derived count
is 475 additions, and the source product occupies physical row
`475 + 28 = 503`. For two products it is 474 additions, putting the source
products at rows 502 and 503. The physical order is grouped by operation,
not necessarily by source order.

The theorem is about the checked source and modeled compiler schedule. It
does not show that the native emitter produced those rows, that a fixed-column
commitment equals the modeled schedule, or that the verifier authenticates
row values. Those remain explicit correspondence and proof-system premises.

Focused checks:

```sh
(cd formal/s31 && lake build S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows)
(cd formal/s31 && lake env leanchecker S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows)
```
