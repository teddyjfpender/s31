import S31.Gadgets.Functional.Correspondence.GeneratedOrderedSubtractionRelease

/-!
The checked-in `release_sub4/manual.s31` source bytes and production normalized
bytes denote exactly the three ordered packed rows proved in
`OrderedSubtractionRelease`. The row premises include coherent wire reads;
authentication of native proof openings is not asserted here.
-/

namespace S31.Functional.Correspondence.OrderedSubtractionConcrete

open OrderedSubtractionBytes
open GeneratedOrderedSubtractionRelease

theorem release_rows_accepted (x doubled difference result : Lanes)
    (tailA tailB : Tail)
    (h : OrderedSubtractionRelease.accepts x doubled difference result tailA tailB) :
    Accepts tailA tailB [x] expectedParsed.instructions
      [x, doubled, difference, result] := by
  obtain ⟨hadd, hsub1, hsub2⟩ := h
  let s1 : Instruction := { id := 1, lhs := 0, rhs := 0, op := .add }
  let s2 : Instruction := { id := 2, lhs := 0, rhs := 1, op := .sub }
  let s3 : Instruction := { id := 3, lhs := 2, rhs := 0, op := .sub }
  change Accepts tailA tailB [x] [s1, s2, s3]
    [x, doubled, difference, result]
  refine Accepts.cons [x] s1 [s2, s3] x x doubled
    [x, doubled, difference, result] (by rfl) (by rfl) (by rfl) hadd ?_
  refine Accepts.cons [x, doubled] s2 [s3] x doubled difference
    [x, doubled, difference, result] (by rfl) (by rfl) (by rfl) hsub1 ?_
  refine Accepts.cons [x, doubled, difference] s3 [] difference x result
    [x, doubled, difference, result] (by rfl) (by rfl) (by rfl) hsub2 ?_
  exact Accepts.nil [x, doubled, difference, result]

/-- Exact checked-in source and normalized bytes plus any accepted witness
force the result to equal the source program's denotation. -/
theorem concrete_source_sound (x doubled difference result : Lanes)
    (tailA tailB : Tail)
    (h : OrderedSubtractionRelease.accepts x doubled difference result tailA tailB) :
    denotation sourceBytes x = some result := by
  exact checked_air_sound sourceBytes normalizedBytes expectedParsed x result
    [x, doubled, difference, result] tailA tailB source_relation_bytes_exact
    (release_rows_accepted x doubled difference result tailA tailB h) (by rfl)

/-- The public value is forced by the source bytes, for arbitrary satisfying
intermediate row values and arbitrary inactive tail cells. -/
theorem concrete_public_claim (x doubled difference result : Lanes)
    (tailA tailB : Tail)
    (h : OrderedSubtractionRelease.accepts x doubled difference result tailA tailB) :
    denotation sourceBytes x =
      some (fun i => (0 : S31.M31) - (x i + x i)) := by
  rw [← OrderedSubtractionRelease.arbitrary_witness_sound x doubled difference
    result tailA tailB h]
  exact concrete_source_sound x doubled difference result tailA tailB h

end S31.Functional.Correspondence.OrderedSubtractionConcrete
