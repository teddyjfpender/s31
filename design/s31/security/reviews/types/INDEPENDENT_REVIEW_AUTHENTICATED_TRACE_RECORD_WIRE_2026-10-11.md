# Independent review: mixed trace and record wire bridges

Reviewed `SourceMixedAuthenticatedTrace.lean`, the extended
`RecordDescriptorWireRefinementV2.lean`, their imported claim-reduction
theorems, and the corresponding native mixed verifier and record ABI loops on
2026-10-11. This is a premise-to-conclusion review, not a proof of native
verifier correspondence.

## Result

I found no reversed event sign, row-count mismatch, missing denominator
condition in the stated claim reductions, or hidden theorem that promotes a
native proof acceptance into a Lean premise. The two bridges remain
**conditional**. The main scope correction is that the mixed trace contract
does **not** cover all 512 Gate *arithmetic* row equations. It covers all 512
Gate **interaction** row equations. The false-word theorem separately assumes
the selected source path's arithmetic and value facts through
`LocalPublicPath`; it does not prove every Gate arithmetic row correct.

## Mixed trace contract

- `GateRows` has exactly 512 logical rows (`Fin 512`), a predecessor
  permutation, two input denominators and one output denominator per row,
  plus the pair and singleton interaction residuals. The explicit nonzero
  requirements are necessary: a paired LogUp residual can vanish at a double
  pole without determining its claimed fraction. `claim_eq_events` uses the
  cyclic sum theorem to derive two positive input occurrences and a
  multiplicity-weighted negative output occurrence per row. It does not
  require or derive the Gate main-column opcode arithmetic residuals.
- `ChipRows 8` has 16 rows per call and supplies four-lane square-plus-constant
  arithmetic and both interaction residuals. Its interaction equations imply
  nonzero input/output denominators. `BridgeRows` supplies eight constant-row
  equalities and five interaction residuals on 16 rows; its four paired
  denominator and two endpoint denominator checks at one anchor extend to all
  rows after constant-column reduction. The bridge telescope therefore
  contributes eight Gate reads, one negative initial chip endpoint, and one
  positive final endpoint, not 16 copies of either endpoint.
- `call_claim_eq_events` and `closed_ideal_event_lists` carry these signs into
  the ideal source lists. `publicOutputYields` consists of eight public Gate
  reads at addresses 3–10 and the fixed `u` read at address 2. The native
  verifier adds these to the circuit claim and then each chip/bridge claim
  (`direct_mixed_general_arithmetic.zig`, `verifySourceBoundBorrowed`). The
  per-call `chip + bridge` sum in the Lean fold has the same commutative sum
  as the native slot order.
- `gateRowsEq` identifies the modeled Gate row list with the source roster,
  but is not used by `closed_ideal_event_lists` itself. That theorem relies on
  the two *full list equalities* `positiveAligned` and `negativeAligned`.
  These equalities are stronger than aggregate count or header equality:
  they identify each modeled Gate/chip/bridge event with the source-shaped
  lists. They remain premises. `claimFoldZero` is also a premise; it is not
  a theorem about `verifySourceBoundBorrowed` returning success. The model
  does not bind its arbitrary Gate predecessor permutation, chip row
  permutation, fixed/main/interaction commitments, or event-list alignment
  to arbitrary accepted native proof bytes.
- `false_word_trace_is_exceptional` applies the pre-existing source theorem
  for a *fixed* false public word, `SourceShape`, and `LocalPublicPath`. Its
  conclusion is membership in the bounded exceptional pair set for those
  fixed ideal lists. There is no Fiat–Shamir independence result or native
  rejection probability here. `LocalPublicPath` ties `initial` to the modeled
  first bridge state and supplies selected arithmetic/public path facts, but
  it does not authenticate a private assignment from a native proof.

The phrase “all-row trace” should be read as all modeled component
interaction rows plus chip and bridge main residuals. Calling it an all-row
**Gate arithmetic** check, or saying it proves native acceptance implies a
false-word bound, would overstate the theorem. A future accepted-proof
correspondence needs the native Gate main AIR checks as well as PCS/FRI trace
authentication, the fixed column binding, and transcript challenge analysis.

## Record descriptor and statement bridge

- `expectedDescriptorLeaves` filters the descriptor's input roots by public
  visibility in their original order and appends every result-root leaf.
  This matches the claim-check walk in native `record_abi.zig::claimedWords`.
  The complete-list equality in `checkDescriptorBinding` rejects an inserted
  private leaf, omitted result, reordering, or changed path/kind/width/wire
  relative to the supplied reference maps. The checked lexical descriptor
  supplies shape, local valid widths, and names. The whole-descriptor checker
  has no selected-root membership premise; the older single-root theorem
  still explicitly needs `root ∈ descriptor.inputs`.
- `admitClaims` checks positional path/width/range agreement and pairwise
  equal payloads for repeated relation wires. Thus aliases across public
  input roots and the result root cannot carry conflicting words in this
  model. `firstWireWords_admitted` justifies first-occurrence lookup for any
  occurrence in the accepted `zip`; there is no missing-leaf case after
  `List.Forall₂` admission.
- The relation-wire reference functions are caller supplied. The module does
  not prove that the native descriptor parser or first-order relation
  produces these maps; it does not establish canonical JSON/digest equality,
  the native `program.inputs`/`program.public_outputs` final wire selection,
  the general eight-word projection, or proof authentication. The example
  `whole_statement_projection` establishes one concrete projection only.
  A broader claim that `checkDescriptorClaims` by itself verifies the final
  eight public words would be too strong.

## Recommended next proof edges

1. Bind the 512 Gate main arithmetic residuals and the fixed-row
   multiplicity/address columns to the same authenticated trace represented
   by `GateRows`; then derive the two event-list alignments from compiler and
   decoded-trace correspondence rather than supplying them as equalities.
2. State the cryptographic extraction/soundness assumption connecting the
   native PCS/FRI verifier's acceptance to all modeled row residuals and
   pre-challenge event-list commitment; prove the native claim fold mapping.
3. Relate parsed ABI v2 leaf `wire` strings to first-order relation indices
   and prove the general native final-word projection after digest/canonical
   byte checks.
