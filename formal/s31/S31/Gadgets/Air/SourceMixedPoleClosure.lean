import S31.Gadgets.Air.SourceMixedAuthenticatedTrace

/-!
The ideal event multiset omits a Gate row's output when its fixed output
multiplicity is zero. Its LogUp singleton still has that output denominator.
At a pole, numerator and denominator are both zero and the AIR residual loses
the claimed-sum equation for that row. This module records all 512 output
denominator poles separately from the ideal event imbalance set.

A probability reading of the finite-set bound assumes ideal independent
challenge pairs. Native Fiat--Shamir sampling and PCS/FRI extraction remain
separate obligations.
-/

namespace S31.Gadgets.Air.SourceMixedPoleClosure

open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.SourceMixedFalseClaimBound
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace

/-- Include the output denominator of every physical Gate row, even one with
zero output multiplicity and therefore no emitted yield event. -/
noncomputable def gateOutputPolePairs (rows : Fin 512 → Row) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact (Finset.univ : Finset GateSecure).biUnion fun alpha =>
    (Finset.univ : Finset (Fin 512)).image fun i =>
      (alpha, compressed7 alpha
        (embedGateEvent ((rows i).outAddress, (rows i).output)))

theorem gate_output_pole_mem (rows : Fin 512 → Row) (i : Fin 512)
    (alpha : GateSecure) :
    (alpha, compressed7 alpha
      (embedGateEvent ((rows i).outAddress, (rows i).output))) ∈
      gateOutputPolePairs rows := by
  classical
  unfold gateOutputPolePairs
  apply Finset.mem_biUnion.mpr
  refine ⟨alpha, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem gate_output_nonzero_outside (rows : Fin 512 → Row)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ gateOutputPolePairs rows) (i : Fin 512) :
    combine7 (embedGateEvent
      ((rows i).outAddress, (rows i).output)) alpha z ≠ 0 := by
  intro hzero
  have hz : z = compressed7 alpha
      (embedGateEvent ((rows i).outAddress, (rows i).output)) := by
    exact (sub_eq_zero.mp hzero).symm
  exact hgood (hz ▸ gate_output_pole_mem rows i alpha)

theorem gate_output_pole_card_le (rows : Fin 512 → Row) :
    (gateOutputPolePairs rows).card ≤
      512 * Fintype.card GateSecure := by
  classical
  unfold gateOutputPolePairs
  calc
    ((Finset.univ : Finset GateSecure).biUnion fun alpha =>
      (Finset.univ : Finset (Fin 512)).image fun i =>
        (alpha, compressed7 alpha
          (embedGateEvent ((rows i).outAddress, (rows i).output)))).card ≤
        ∑ alpha ∈ (Finset.univ : Finset GateSecure),
          ((Finset.univ : Finset (Fin 512)).image fun i =>
            (alpha, compressed7 alpha
              (embedGateEvent ((rows i).outAddress, (rows i).output)))).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _alpha ∈ (Finset.univ : Finset GateSecure), 512 := by
      apply Finset.sum_le_sum
      intro alpha _
      have hcard :
          ((Finset.univ : Finset (Fin 512)).image fun i =>
            (alpha, compressed7 alpha
              (embedGateEvent ((rows i).outAddress, (rows i).output)))).card ≤
            (Finset.univ : Finset (Fin 512)).card := Finset.card_image_le
      simpa using hcard
    _ = 512 * Fintype.card GateSecure := by simp [Nat.mul_comm]

/-- All emitted ideal tuples need unconditional pole coverage. In particular,
`imbalancePairs7` is empty for an exactly balanced witness and cannot exclude
even a pole of an emitted input event in that case. -/
noncomputable def eventPolePairs (events : List JointTuple) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact (Finset.univ : Finset GateSecure).biUnion fun alpha =>
    (Finset.univ : Finset (Fin events.length)).image fun i =>
      (alpha, compressed7 alpha (events.get i))

theorem event_pole_mem (events : List JointTuple) (event : JointTuple)
    (hmem : event ∈ events) (alpha : GateSecure) :
    (alpha, compressed7 alpha event) ∈ eventPolePairs events := by
  classical
  obtain ⟨i, hi⟩ := List.mem_iff_get.mp hmem
  unfold eventPolePairs
  apply Finset.mem_biUnion.mpr
  refine ⟨alpha, Finset.mem_univ _, ?_⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hi]⟩

theorem event_nonzero_outside (events : List JointTuple)
    (event : JointTuple) (hmem : event ∈ events)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ eventPolePairs events) :
    combine7 event alpha z ≠ 0 := by
  intro hzero
  have hz : z = compressed7 alpha event :=
    (sub_eq_zero.mp hzero).symm
  exact hgood (hz ▸ event_pole_mem events event hmem alpha)

theorem event_pole_card_le (events : List JointTuple) :
    (eventPolePairs events).card ≤
      events.length * Fintype.card GateSecure := by
  classical
  unfold eventPolePairs
  calc
    ((Finset.univ : Finset GateSecure).biUnion fun alpha =>
      (Finset.univ : Finset (Fin events.length)).image fun i =>
        (alpha, compressed7 alpha (events.get i))).card ≤
        ∑ alpha ∈ (Finset.univ : Finset GateSecure),
          ((Finset.univ : Finset (Fin events.length)).image fun i =>
            (alpha, compressed7 alpha (events.get i))).card :=
          Finset.card_biUnion_le
    _ ≤ ∑ _alpha ∈ (Finset.univ : Finset GateSecure), events.length := by
      apply Finset.sum_le_sum
      intro alpha _
      have hcard :
          ((Finset.univ : Finset (Fin events.length)).image fun i =>
            (alpha, compressed7 alpha (events.get i))).card ≤
            (Finset.univ : Finset (Fin events.length)).card := Finset.card_image_le
      simpa using hcard
    _ = events.length * Fintype.card GateSecure := by simp [Nat.mul_comm]

/-- The fixed-witness error event used by a future raw-AIR-to-reciprocal
argument. The second summand is necessary even when an output's multiplicity
is zero and the tuple is absent from the ideal event lists. -/
noncomputable def mixedErrorPairs {N : Nat} (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (gateRows : Fin 512 → Row) : Finset (GateSecure × GateSecure) :=
  (imbalancePairs7
    (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
    (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start) ∪
   eventPolePairs
     ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
      (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))) ∪
  gateOutputPolePairs gateRows

theorem gate_output_nonzero_outside_mixed_error {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (gateRows : Fin 512 → Row)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ mixedErrorPairs boundary rows gateRows)
    (i : Fin 512) :
    combine7 (embedGateEvent
      ((gateRows i).outAddress, (gateRows i).output)) alpha z ≠ 0 := by
  apply gate_output_nonzero_outside gateRows alpha z
  intro hpole
  exact hgood (Finset.mem_union_right _ hpole)

/-- Both Gate input denominators belong to the ideal event support once all
physical source rows are identified. `eventPolePairs` covers their poles;
zero-multiplicity outputs additionally require `gateOutputPolePairs`. -/
theorem gate_inputs_nonzero_outside_mixed_error {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (gateRows : Fin 512 → Row)
    (hrows : List.ofFn gateRows = boundary.jointGateSource.gateRows)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ mixedErrorPairs boundary rows gateRows)
    (i : Fin 512) :
    (useTerm ((gateRows i).in0Address, (gateRows i).in0) alpha z).denominator ≠ 0 ∧
    (useTerm ((gateRows i).in1Address, (gateRows i).in1) alpha z).denominator ≠ 0 := by
  have hrow : gateRows i ∈ boundary.jointGateSource.gateRows := by
    rw [← hrows]
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hgoodEvents : (alpha, z) ∉ eventPolePairs
      ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
        (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)) := by
    intro hpole
    exact hgood (Finset.mem_union_left _ (Finset.mem_union_right _ hpole))
  have hinput (event : GateLookup.Event) (huse : event ∈ (gateRows i).uses) :
      (useTerm event alpha z).denominator ≠ 0 := by
    have hsource : event ∈ allUses boundary.jointGateSource.gateRows
        boundary.jointGateSource.gateExternalUses := by
      apply List.mem_append_left
      exact List.mem_flatMap.mpr ⟨gateRows i, hrow, huse⟩
    have htuple : embedGateEvent event ∈
        boundary.jointGateSource.circuitUses :=
      List.mem_map.mpr ⟨event, hsource, rfl⟩
    have hideal : embedGateEvent event ∈
        (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
        (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start) :=
      List.mem_append_left _ (List.mem_append_left _ htuple)
    have hnonzero := event_nonzero_outside _
      (embedGateEvent event) hideal alpha z hgoodEvents
    have hcombine : combine7 (embedGateEvent event) alpha z =
        (useTerm event alpha z).denominator := by
      simp only [combine7, useTerm, combineTerm, eventTuple,
        embedGateEvent]
      rw [padded_gate_compression_eq_native_six]
    rwa [hcombine] at hnonzero
  constructor
  · exact hinput _ (by simp [Row.uses])
  · exact hinput _ (by simp [Row.uses])

/-- Raw all-row Gate AIR data with no denominator assumptions. Algebraic AIR
acceptance alone does not supply them at a zero/zero singleton pole. -/
structure RawGateRows (alpha z : GateSecure) where
  rows : Fin 512 → Row
  arithmeticResidual : ∀ i,
    Qm31Ops.accepts (rows i).flags (rows i).in0 (rows i).in1
      (rows i).output
  previous : Equiv.Perm (Fin 512)
  first : Fin 512 → GateSecure
  last : Fin 512 → GateSecure
  claim : GateSecure
  pairResidual : ∀ i,
    LogUpInteraction.pairResidual (rowPair (rows i) alpha z).1
      (rowPair (rows i) alpha z).2 (first i) = 0
  yieldResidual : ∀ i,
    LogUpInteraction.singleResidual (yieldTerm (rows i) alpha z)
      (last i - last (previous i) - first i + claim / (512 : GateSecure)) = 0

/-- Outside the *raw* pole set, the AIR residuals can be interpreted as the
reciprocal Gate claim. This is the missing local step for a future accepted-
proof theorem; fixed-row, trace-authentication and Fiat--Shamir assumptions
remain separate. -/
def RawGateRows.toChecked {N : Nat} {alpha z : GateSecure}
    (raw : RawGateRows alpha z)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (hrows : List.ofFn raw.rows = boundary.jointGateSource.gateRows)
    (hgood : (alpha, z) ∉ mixedErrorPairs boundary rows raw.rows) :
    GateRows alpha z :=
  { rows := raw.rows
    arithmeticResidual := raw.arithmeticResidual
    previous := raw.previous
    first := raw.first
    last := raw.last
    claim := raw.claim
    use0Nonzero := fun i =>
      (gate_inputs_nonzero_outside_mixed_error boundary rows raw.rows
        hrows alpha z hgood i).1
    use1Nonzero := fun i =>
      (gate_inputs_nonzero_outside_mixed_error boundary rows raw.rows
        hrows alpha z hgood i).2
    yieldNonzero := fun i => by
      have hnonzero := gate_output_nonzero_outside_mixed_error
        boundary rows raw.rows alpha z hgood i
      have hcombine : combine7 (embedGateEvent
          ((raw.rows i).outAddress, (raw.rows i).output)) alpha z =
          (yieldTerm (raw.rows i) alpha z).denominator := by
        simp only [combine7, yieldTerm, combineTerm, eventTuple,
          embedGateEvent]
        rw [padded_gate_compression_eq_native_six]
      rwa [hcombine] at hnonzero
    pairResidual := raw.pairResidual
    yieldResidual := raw.yieldResidual }

/-- The previous fixed-false-word theorem still supplies the imbalance
membership. The widened budget includes every emitted ideal tuple pole and
all 512 Gate output poles, including non-emitted zero-multiplicity outputs.
This theorem does not yet derive the trace contract from raw AIR acceptance. -/
theorem false_word_trace_is_extended_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (hlocal : LocalPublicPath hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (trace : AuthenticatedMixedTrace boundary rows alpha z) :
    (alpha, z) ∈ mixedErrorPairs boundary rows trace.gate.rows ∧
      (mixedErrorPairs boundary rows trace.gate.rows).card ≤
        36494846 * Fintype.card GateSecure := by
  have hsource := false_word_closed_pair_is_exceptional hN hpositive
    boundary rows initial hshape hlocal product lane hfalse alpha z
    (closed_ideal_event_lists trace)
  have hlength := joint_lengths boundary rows hshape
  have hrawLength :
      ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
        (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)).length ≤
      2466 := by
    rw [List.length_append, hlength.1, hlength.2]
    omega
  have hpoleCard :
      (eventPolePairs
        ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
          (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))).card ≤
        2466 * Fintype.card GateSecure :=
    (event_pole_card_le _).trans (Nat.mul_le_mul_right _ hrawLength)
  constructor
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hsource.2.1)
  · calc
      (mixedErrorPairs boundary rows trace.gate.rows).card ≤
          ((imbalancePairs7
            (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
            (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)) ∪
            eventPolePairs
              ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
                (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))).card +
            (gateOutputPolePairs trace.gate.rows).card := Finset.card_union_le _ _
      _ ≤ ((imbalancePairs7
            (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
            (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)).card +
            (eventPolePairs
              ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
                (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))).card) +
            (gateOutputPolePairs trace.gate.rows).card :=
          Nat.add_le_add_right (Finset.card_union_le _ _) _
      _ ≤ (36491868 * Fintype.card GateSecure +
            2466 * Fintype.card GateSecure) +
            512 * Fintype.card GateSecure :=
          Nat.add_le_add
            (Nat.add_le_add hsource.2.2 hpoleCard)
            (gate_output_pole_card_le trace.gate.rows)
      _ = 36494846 * Fintype.card GateSecure := by ring

/-- A physical-row pole can exist when the ideal event lists have no error
pairs at all. It is therefore not derivable from the old error-set complement. -/
theorem zero_multiplicity_pole_outside_empty_imbalance
    (row : Row) (hm : row.multiplicity = 0) (alpha : GateSecure) :
    row.yields = [] ∧
    (alpha, compressed7 alpha
      (embedGateEvent (row.outAddress, row.output))) ∉
        imbalancePairs7 [] [] ∧
    combine7 (embedGateEvent (row.outAddress, row.output)) alpha
      (compressed7 alpha
        (embedGateEvent (row.outAddress, row.output))) = 0 := by
  constructor
  · simp [Row.yields, hm]
  constructor
  · simp [imbalancePairs7]
  · simp [combine7, compressed7]

end S31.Gadgets.Air.SourceMixedPoleClosure
