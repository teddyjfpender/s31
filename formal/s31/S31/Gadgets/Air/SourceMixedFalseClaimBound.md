# False public word in the mixed source family

`SourceMixedFalseClaimBound.lean` composes two existing conditional results:
the source-level public-output theorem and the bounded ideal lookup error
set. Choose one of the eight public words by `product : Bool` and
`lane : Fin 4`. The source function starts from a four-word private state,
applies sixteen square-plus-constant rounds per call, and publishes the
wordwise sum or product of the final state with the initial state.

For example, with one call and `product = false`, lane zero should publish

```text
x₀ + iterate₁₆(s ↦ s² + 13, x)₀    (mod 2³¹−1).
```

`false_word_excludes_exact_balance` says a different value is incompatible
with exact joint Gate/chip event balance **when** the local path facts hold.
Those facts include canonical source addresses, a unique produced value per
Gate address, the selected packed input/final rows, both selected arithmetic
rows and all eight unpack/copy output paths, correct chip row transitions,
and the source-shaped 16-round count. `SourceShape` additionally requires
the 512-row source roster and its exact multiplicity total.

`false_word_closed_pair_is_exceptional` then assumes equality of the two
ideal reciprocal lookup sums at fixed challenges `(alpha, z)`. It proves
three facts together:

1. The exact joint event lists cannot balance.
2. The challenge pair belongs to `imbalancePairs7`.
3. That set has at most `36,491,868 · |QM31|` pairs among `|QM31|²`.

The bound is a conservative algebraic bound for fixed event lists and ideal
independent challenges. The module does not derive its local facts, event
lists, or reciprocal closure from accepted native AIR/PCS/FRI openings, and
does not prove independence of transcript challenges. In an honest exact
balance, `imbalancePairs7` is empty.
