# Mixed trace to event-list bridge

`SourceMixedAuthenticatedTrace.lean` is a deliberately narrow contract for the
one-to-eight-call, 512 Gate row mixed profile. It states exactly what an
authenticated trace extractor would have to establish before the conditional
false-public-word bound can describe a native proof.

The verifier's signed claim equation is:

```text
Gate claim + sum over calls (chip claim + bridge claim)
           + 8 public-output Gate reads + fixed-u Gate read = 0.
```

The module keeps three component claims separate. `GateRows` carries the 512
Gate row interaction residuals and explicit nonzero denominators. It derives
the Gate claim as the reciprocal sum of its two input events minus its
multiplicity-weighted output events. Each `ChipRows` carries all 16 arithmetic
and interaction row residuals and derives the input-event sum minus the
output-event sum. Each `BridgeRows` carries 16 constant-row constraints and
five interaction residuals per row. Its claim reduces to eight Gate reads,
minus the initial chip endpoint, plus the final chip endpoint. The latter
reduction uses the factor `1/16` and cyclic telescoping, so it must not be
treated as sixteen independent endpoint events.

`AuthenticatedMixedTrace.gateRowsEq` binds every decoded Gate row, including
its raw canonical addresses and fixed multiplicity, to the source roster.
`AuthenticatedMixedTrace.positiveAligned` and `.negativeAligned` identify
those decoded component events with the ideal lists in `SourceMixedPath`.
This is a strong and explicit source/compiler/trace correspondence premise:
it includes every Gate row, fixed multiplicity, every chip step, both bridge
endpoints, all eight public outputs, and the fixed `u` event. The theorem
`closed_ideal_event_lists` combines the component residual results, the
alignment equalities, and the zero native claim fold into the exact ideal
reciprocal identity. It does not assume a good challenge and does not turn
the identity into exact multiset balance; the existing bounded-exception
theorems handle that conditional step.

## Native proof gap

The production `general_package.verifySourceBound` rebuilds the source
schedule and AIR roster, checks the source-derived fixed commitment root,
checks the public words and reciprocal claim fold, then invokes the Stwo
PCS/FRI verifier. It does not return an all-row trace. Therefore no theorem
currently takes `verifyEmbeddedAndInspect` success and constructs an
`AuthenticatedMixedTrace`. The native main commitment precedes the lookup
challenge; the interaction commitment follows it. A proof of that missing
implication needs a stated PCS/FRI extraction or soundness assumption and
must bind **both** committed trees, column order and row permutations to the
formal model. Honest-writer row fixtures and a proof-root mutation test are
useful checks, but do not discharge this implication.

The smallest independently auditable native next step is an optional full
trace certificate: export the exact main and interaction columns for a proof,
recompute their commitment roots, check every component AIR row with the
same source-derived handles, decode the two event lists, and compare them
with the modeled lists. This would validate a trace-carrying audit mode.
The ordinary succinct verifier still requires a separate cryptographic
argument to extract that same all-row evidence from arbitrary accepted
proofs. Fiat–Shamir challenge distribution is a further, separate obligation.

## Soundness details that must survive implementation

- Gate and chip relation tags differ; Gate tuples have a zero seventh word.
- All Gate addresses and chip call/round tags must be canonical M31 values.
- The bridge's row-order/previous masks must be bijections of the 16 logical
  rows, and its eight endpoint words must be constant across them.
- Gate paired residuals need explicit nonzero denominators; at a double pole
  the residual is zero for an arbitrary interaction difference.
- The source owns the fixed Gate multiplicity column. The 512-row count and
  the total `1033 + 8N` multiplicity do not by themselves identify row values.
- The `1 + 2N` claim order is circuit, then chip and bridge for each call.
- Event lists must be fixed by the pre-challenge main commitment before using
  the fixed-witness exceptional-pair bound. Fiat–Shamir adaptivity is not
  settled by the list-cardinality calculation alone.
