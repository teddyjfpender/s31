# Independent review: mixed LogUp pole closure

Reviewed the mixed source event bound, the all-row Gate interaction contract,
the new pole-closure lemmas, and the native singleton LogUp equation on
2026-10-11. This review concerns the fixed one-to-eight-call, 512-Gate-row
family. It does not establish soundness of accepted native proof bytes.

## Finding and repair

The old `imbalancePairs7` set controls compression collisions for an
*unbalanced* ideal event multiset. It need not contain a pole of an emitted
tuple when the multiset is balanced. More sharply, a physical Gate row with
zero output multiplicity emits no output yield, but its singleton AIR equation
still uses that output denominator. At its compression pole, both numerator
and denominator are zero, so `diff * denominator - numerator = 0` for every
interaction-column difference. The native regression constructs the pole by
compressing a Gate-shaped tuple and checks two different differences. This is
an algebraic loss of constraint, not a forged-proof example.

`SourceMixedPoleClosure.lean` now forms `mixedErrorPairs` as the union of:

1. the existing imbalance/collision set for the two ideal event lists;
2. compression poles for **every emitted ideal tuple**, on both sides;
3. output-denominator poles for **all 512 physical Gate rows**, including
   zero-multiplicity rows whose outputs are absent from the ideal lists.

`event_nonzero_outside` and `gate_output_nonzero_outside` give the direct
nonzero-denominator facts. With `List.ofFn raw.rows` identified with the
source Gate rows, `gate_inputs_nonzero_outside_mixed_error` covers both input
denominators. `RawGateRows.toChecked` then converts raw Gate arithmetic and
LogUp residual data into the existing `GateRows` reciprocal contract outside
the widened set. The row identity is an explicit premise; it is not inferred
from a succinct proof header.

The finite-set calculation adds at most 2,466 emitted tuple poles and 512
physical output poles per `alpha` to the prior bound of 36,491,868. Thus
`false_word_trace_is_extended_exceptional` gives a cardinality bound of
**36,494,846 × |GateSecure|** challenge pairs, conditional on its fixed
source shape, local public path, false word, and `AuthenticatedMixedTrace`
premises. The theorem uses that trace's already checked Gate contract to
obtain ideal reciprocal closure; `RawGateRows.toChecked` is a separate local
conversion lemma, not a construction of a full authenticated trace.

## Scope of the claim

The enlarged set covers every denominator pole represented by an emitted
ideal tuple and every physical Gate output denominator. The implemented raw
AIR conversion is for the Gate rows. There is no analogous theorem here
extracting chip and bridge reciprocal contracts from arbitrary raw native AIR
rows, nor a theorem constructing the alignment, fixed-column identity, or
claim-fold fields of `AuthenticatedMixedTrace` from verifier acceptance.
In particular, `BridgeRows.nonzeroD0` and `nonzeroD1` state nonzero facts at
`sourceBridgeAnchor`; the underlying bridge AIR fraction lemma needs the
denominators nonzero across all sixteen rows. The source bridge claim theorem
uses accepted main-column constancy to transfer anchor values to every row.
`SourceMixedPoleClosure` does not connect its ideal anchor-event pole coverage
to those bridge fields or perform that raw-AIR-to-checked bridge conversion.

The cardinality bound only has a probability interpretation for an ideal
independent uniform pair sampled after a fixed witness. There is no native
Fiat--Shamir independence or pre-challenge commitment theorem here. Merkle
binding, PCS/FRI extraction or soundness, and native bytecode-to-Lean trace
refinement remain necessary for an accepted-proof rejection theorem. The
native test demonstrates the local zero-over-zero hazard, not exploitability
of an accepted proof.

## Focused checks

From `formal/s31`:

```sh
lake build S31.Gadgets.Air.SourceMixedPoleClosure
```

Passed (3,385 jobs, target compiled). From `deps/stwo-zig`:

```sh
zig build --build-file src/frontends/circuit/build.zig test -Dtest-filter='Gate tuple Horner order and LogUp residual equations' -j1 --summary all
```

Passed (21 filtered tests in the circuit frontend build).
