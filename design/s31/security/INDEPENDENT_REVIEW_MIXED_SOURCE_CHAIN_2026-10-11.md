# Independent review: mixed source chain and generated verifier

Scope: the experimental `direct-mixed-general` one-to-eight-call chain,
`source_pinned_general.py`, `typed_boundary_correspondence.py`,
`SourceMixedAddressSchedule.lean`, `SourceMixedChainSemantics.lean`, and the
source-embedded native verifier. This is an adversarial review of their stated
claims, not an assertion of whole-prover soundness.

## Native boundary and acceptance checks

`general_verifier_main.zig` embeds the program and AIR bytes. For V1 it parses
the public statement, calls `verifyEmbeddedAndInspect`, and then compares the
statement's source/manifest/registry/circuit identity with the verified
inspection. `general_package.zig` reconstructs source topology, the call
schedule, component registry and live geometry. It checks count, roster and
three header digests before bounded postcard decoding, then invokes the native
engine with the selected source, public words, claimed sums and STARK proof.
The JSON inspector is an audit view; it is not supplied to this verifier.

The N1/N3/N8 changed-source control in `source_pinned_general.py` was recently
repaired to build a separate verifier for each count and to check the changed
inspector's exact source digest and roster. That control appends whitespace.
It establishes source-*byte* binding while keeping program arithmetic fixed.
The companion `semantic_source_reseal.py` changes the first repeat constant
from 13 to 14, keeps the same call count and component roster, independently
computes changed public words, and proves both programs. It then rewrites the
old proof's source, registry and circuit identity header fields and saved
statement metadata to match the new verifier. Rejection past the outer
envelope/statement checks tests that generated verifier binding reaches the
native proof for a semantically different source.

## What the Lean results establish

`SourceMixedAddressSchedule` proves the canonical hand-derived address
formula: first inputs 11–14, first outputs 23–26, and successive outputs ten
addresses apart; an adjacent input address equals the preceding output
address. With a *separate* one-value-per-produced-Gate-address premise, it
proves equal handoff words. `SourceMixedChainSemantics` then composes each
16-round chip path into the exact source prefix `x ↦ x² + 13 + call` for every
modeled call. Its corollary can derive those paths from an exact joint event
permutation and every chip row's local recurrence.

These are conditional, typed model theorems. `Boundary.addresses` is assumed
equal to the canonical formula; `Boundary.start 0` is assumed equal to an
arbitrary `initial`; Gate producer uniqueness is assumed; and exact event
balance/local row recurrences are premises. The compiled native plan and proof
commitments do not appear in those hypotheses as authenticated objects. The
native N1/N8 inspector fixture compares exact addresses, but reads neither
committed bridge words nor all Gate rows. The handoff theorem cannot by itself
establish a full compiler-to-native-proof refinement.

There is also a precise **public-closure gap** in this theorem: its conclusion
only identifies each `Boundary.finish call`. `Boundary.publicOutputs` is a
separate field, and neither `every_call_matches_source_prefix` nor
`source_prefix_of_joint_event_balance` concludes that the eight public words
are the last chip result plus/times the source input. Likewise, the `initial`
parameter is not shown to be the actual committed private input. The Python
fixture checks one concrete N1/N8 public projection, and native verification
checks selected public words. A formal end-to-end theorem still needs the
compiler's Gate arithmetic, input assignment and public output rows linked to
these typed values. This is a missing proof obligation, not a demonstrated
accepted false proof.

Finally, `uniqueProduced` ranges over `allYields`, which includes the modeled
bridge Gate events as external yields. It is stronger than address arithmetic
or the chip AIR alone. A future proof-to-model theorem must derive it from the
committed Gate/lookup relation; treating it as automatic would make the
adjacent-value result circular.

## Reproduction and conclusion

```sh
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --static
python3 src/frontends/s31/tests/acceptance/mixed_boundary/typed_boundary_correspondence.py
python3 src/frontends/s31/tests/acceptance/mixed_boundary/semantic_source_reseal.py --counts 1 3 8
```

The semantic source control is a focused native negative test, not a proof of
LogUp collision resistance, PCS/FRI soundness, Fiat–Shamir security, native
trace extraction, or witness confidentiality. No concrete false-proof path was
identified in this bounded source-embedded entrypoint. The critical remaining
formal work is to connect native verifier acceptance to authenticated Gate and
chip rows, derive the exact joint event equation and producer uniqueness with
their error bounds, and connect source input/public rows to the typed chain.

Local N1/N3/N8 native runs: each original and changed-source proof verified
under its own generated verifier. The original proofs, resealed to the changed
source/manifest/registry/circuit header and statement, each rejected with
`InvalidMixedInteractionNonce` inside the native engine. The static N1/N3/N8
source mapping and N1/N8 typed-boundary controls also passed. This is evidence
of transcript binding for this mutation, not a universal semantic soundness
claim. In particular, the changed proof never reaches lookup closure or FRI
verification, so this control cannot establish those properties.
