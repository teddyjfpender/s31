# Independent review: mixed false public word bound

Reviewed `formal/s31/S31/Gadgets/Air/SourceMixedFalseClaimBound.lean` and its
lookup, path, public-tail, and native-verifier dependencies on 2026-10-11.
This review checks the theorem's stated implication. It does not claim that
accepted native proofs satisfy its premises.

## Result

I found no counterexample to the **conditional** theorem or reversed lookup
sign. `false_word_excludes_exact_balance` (`SourceMixedFalseClaimBound.lean:61`)
uses `all_public_outputs_match_source` (`SourceMixedPublicClosure.lean:208`):
given exact joint event balance and the local path facts, each of the eight
public words equals the source computation. A selected false word contradicts
that equality. `false_word_closed_pair_is_exceptional` (`:91`) then applies
`source_closed_or_error` (`SourceMixedLookupBound.lean:286`) to the *same*
left/right lists and pair `(alpha,z)`, eliminates the exact-balance case, and
applies `source_false_closure_pair_bound` (`:202`). Its conclusion is membership
in a bounded **ideal fixed-list** exception set; it does not assert a native
verifier rejection probability.

The signs are the native zero-sum order: `circuitUses ++ jointUses` on the
positive side, `circuitYields ++ jointYields` on the negative side
(`SourceMixedFalseClaimBound.lean:70-73,101-120`). The circuit list includes
row-input, public-output, and bridge Gate reads; the chip list includes row
inputs and bridge final endpoints. The native verifier checks the sum of
component claims and public output reciprocals for zero in
`deps/stwo-zig/src/integrations/circuit_cpu/direct_mixed_general_arithmetic.zig:603-607`.
This is consistent with the repaired sign ledger in
`INDEPENDENT_REVIEW_MIXED_EVENT_SIGN_2026-10-11.md`.

## Nonvacuity and numerical scope

The theorem does not require an honest witness to avoid the old `badPairs7`
set. `imbalancePairs7` is empty for an exact permutation by
`TaggedPairConditionalCorrespondence.lean:34-39`, and
`SourceMixedPath.exact_joint_has_no_imbalance_pairs` (`:168`) instantiates
this for the source boundary. Thus the good-challenge condition is compatible
with any exact *modeled* trace. There is no Lean theorem yet constructing a
`Boundary`, `NativeRow` array, `SourceShape`, and `LocalPublicPath` from a
verified native proof; the native tests below are separate existence evidence
for the intended honest emitter.

`LocalPublicPath` (`SourceMixedFalseClaimBound.lean:30-49`) supplies canonical
addresses, unique Gate producers, source initial state and constants, all
chip row recurrences, the packed initial/final values, selected local Gate
arithmetic, and all eight unpack/copy paths. It does **not** assume the claimed
public words equal the source words. Their equality follows only after exact
event balance ties the public feeder to produced rows. `SourceShape`
(`SourceMixedLookupBound.lean:34-40`) separately supplies 512 rows, total
output multiplicity `1033+8N`, empty baseline lists, and 16 rounds per call.
These are strong source-to-trace assumptions, not facts obtained from an
accepted proof by this theorem.

`joint_lengths` (`SourceMixedLookupBound.lean:120`) gives `1033+25N` events
on **each** side, at most 1,233 for `1≤N≤8`. Its combined distinct support is
at most 2,466, so `6·2466²+2·2466 = 36,491,868`, as used at `:225-235`.
`badPairs7_card_le` (`TaggedPairChallenge.lean:367`) requires each list length
below the M31 characteristic; the source count discharges both requirements.
For an independent uniform pair in `QM31²`, the conditional fraction is at
most `36,491,868/|QM31|`. No Fiat–Shamir theorem licenses applying that
fraction to production transcript challenges. The theorem's `N>0` and `N≤8`
premises match the admitted one-to-eight-call family.

## Remaining end-to-end proof obligations

1. `FalsePublicWord` is relative to an arbitrary `initial` (`:53-57`).
   `LocalPublicPath.first` binds it to the modeled first bridge input, but no
   accepted-proof theorem identifies that state with an authenticated private
   assignment. `packedInitial`, `packedFinal`, selected `AcceptedRow`s, all
   `OutputPath`s, and `uniqueProduced` likewise need compiler/trace refinement.
   Since `initial` is private, another valid private input may legitimately
   produce different public words; this theorem speaks about the particular
   modeled witness, not invalidity of an output for every possible witness.
2. `hclosed` (`:101-106`) is equality of ideal reciprocal sums over the exact
   modeled event lists. Native verification instead checks public terms plus
   claimed component sums (`direct_mixed_general_arithmetic.zig:603-607`),
   then checks the STARK proof at `:654`. AIR/LogUp evaluation, PCS openings,
   FRI soundness, and the bridge's sixteen-row telescope have not been
   composed into a theorem that yields `hclosed` or authenticates those lists.
3. The exception set depends on the complete witness event lists. The native
   main commitment precedes challenge drawing (`direct_mixed_general_arithmetic.zig:597-604`),
   but this Lean theorem does not prove binding of those lists before the
   challenge, independent uniform sampling, or a composed production error
   bound. A challenge-dependent false roster would invalidate the fixed-list
   probability reading.

The existing `trace_correspondence.zig` fixture checks all 512 emitted fixed
rows and 512×12 main cells for N=1..8 and obtains honest native proofs for
N=1/N=8. It rejects a changed public word on those proofs (`:512-516`),
which tests replay binding, not a fresh forged proof. The command acceptance
test `source_pinned_general.py:289-295,328-336` tests all eight changed
statement words for N=1/N=3/N=8 and rejects an inconsistent prover assignment.
Such tests do not establish impossibility of a malicious prover recomputing
commitments, transcript, and proof for a false word. A changed public word
normally fails the native equality check at
`direct_mixed_general_arithmetic.zig:570-575`, before the lookup and STARK
checks, so its rejection must not be credited to this algebraic bound.

## Reproduction

From the repository root:

```sh
cd formal/s31 && lake build S31.Gadgets.Air.SourceMixedFalseClaimBound
LEAN_NUM_THREADS=1 lake env leanchecker -v S31.Gadgets.Air.SourceMixedFalseClaimBound
cd ../..
python3 src/frontends/s31/tests/acceptance/mixed_boundary/typed_boundary_correspondence.py
zig build --build-file src/frontends/s31/build.zig test-mixed-trace-correspondence -Doptimize=ReleaseFast -j1 --summary all
python3 src/frontends/s31/tests/acceptance/mixed_boundary/source_pinned_general.py --counts 1
```

All four checks passed locally: 3,383 Lean build jobs and targeted kernel
replay; eight static counts with five rejected mutations each; 3/3 Zig tests;
and one honest N=1 command proof accepted while its statement, proof, and
inconsistent-assignment controls were rejected. This is evidence about those
concrete packages and mutations only.
