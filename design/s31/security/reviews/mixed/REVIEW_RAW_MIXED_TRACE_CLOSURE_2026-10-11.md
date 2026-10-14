# Raw mixed trace closure: independent algebraic review

Scope: `SourceMixedPoleClosure.lean`, `SourceMixedBridgePoleClosure.lean`,
`SourceMixedRawTraceClosure.lean`, and `SourceMixedAuthenticatedTrace.lean`, checked
against the native `tagged_many_bridge.zig` and its tuple definitions. This was
a read-only source audit; I did not run Lean, Zig, or a proof verifier.

## What the theorem establishes

`raw_false_word_is_exceptional` assumes `N ≤ 8`, `0 < N`, a `SourceShape`
boundary, `LocalPublicPath` for the ideal native rows and initial state, a
`FalsePublicWord`, and a `RawAuthenticatedMixedTrace` at a selected
`(alpha, z)`. The raw trace supplies all 512 Gate arithmetic and LogUp row
residuals, checked chip rows, raw bridge main and interaction residuals,
identity of the Gate rows with the boundary roster, identity of the public
words, **two complete event-list permutations**, and the zero claim fold.
Under these premises, the theorem places the challenge pair in
`mixedErrorPairs` and bounds that set by `36,494,846 · |QM31|` pairs.
`SourceShape` fixes the 512-row count, multiplicity sum, empty baseline
events, and sixteen rounds per call. `LocalPublicPath` assumes canonical
addresses, unique producers, the initial state, source constants and chip
steps, packed endpoint values, the zero value, and accepted rows for the
public add, multiply, and output paths.

The error set is the union of ideal event-imbalance pairs, poles of **every
emitted ideal event**, and poles of all 512 physical Gate output denominators.
The last term is needed when a Gate row has zero output multiplicity and emits
no yield event. Gate input poles are covered by the ideal uses once
`gateRowsEq` holds. Chip input and output poles are excluded directly by its
interaction residuals, whose numerators are `+1` and `-1`. The bridge's eight
Gate factors and two chip endpoint factors all occur in its anchor event
lists; the two event permutations place those lists in the ideal support.
The eight main-row equalities make the bridge words, and hence these ten
denominators, constant across all sixteen physical rows. I found no omitted
pole case in this conditional reduction.

## Native bridge tuple check

`tagged_many_bridge.zig` pairs lanes `(2s, 2s+1)` for `s = 0..3`. Each Gate
denominator compresses the native six-word tuple
`[GATE_RELATION_ID, address, word, 0, 0, 0]`; Lean pads it with a zero seventh
coordinate. The chip start tuple is
`[relation_id, call_id, 0, words[0..4]]`, and the finish tuple is
`[relation_id, call_id, rounds, words[4..8]]`. These match
`sourceBridgeGateTuple`, `sourceBridgeStartTuple`, and
`sourceBridgeFinishTuple`. Native `rowConstraints` uses four residuals
`delta * d0 * d1 - (d0 + d1)/16` and one residual
`(delta - current[3] + claim/16) * first * last - (first - last)/16`;
the signs and scaling match `BridgeAccepted`. Its eight `word - next_word`
constraints match the Lean main-row premise. The same tuple layout appears in
the earlier `tagged_pair_bridge.zig`.

## Boundary of the result

The theorem closes the **Gate and bridge LogUp claim algebra** once the raw
rows, event permutations, and claim fold are supplied. It does not derive the
event permutations from AIR or accepted commitments. Bridge addresses, call
ID, and round count are fields of `RawBridgeRows`; their trusted-plan binding
is not established by the raw bridge structure. `LocalPublicPath` separately
assumes the step transition, unique producers, and accepted public-output
arithmetic rows. The false-word contradiction consumes those premises rather
than deriving them from the raw Gate or chip arithmetic residuals. Finally,
the finite-set bound is for a fixed boundary and Gate row roster; commitment timing,
Fiat–Shamir sampling, and PCS/FRI trace extraction remain separate. I found
no false theorem statement in the inspected algebra, subject to the lack of
a Lean build in this review.
