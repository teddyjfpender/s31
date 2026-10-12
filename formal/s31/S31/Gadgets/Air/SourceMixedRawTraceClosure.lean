import S31.Gadgets.Air.SourceMixedBridgePoleClosure
import S31.Gadgets.Air.SourceMixedScheduledPublicPath

/-!
This module combines the raw Gate and bridge AIR residual contracts. Outside
one source-specific exceptional challenge set, the emitted event alignment
turns those raw rows into `AuthenticatedMixedTrace`, so the existing
false-public-word bound applies. Chip rows still use their checked AIR model:
its paired interaction residuals imply input/output nonzero denominators.

The remaining security boundary is explicit: neither committed trace
extraction, compiler-to-event alignment, nor Fiat--Shamir/PCS/FRI soundness is
inferred from a native verifier's acceptance here.
-/

namespace S31.Gadgets.Air.SourceMixedRawTraceClosure

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.SourceMixedFalseClaimBound
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace
open S31.Gadgets.Air.SourceMixedPoleClosure
open S31.Gadgets.Air.SourceMixedBridgePoleClosure
open S31.Gadgets.Air.SourceMixedEventAlignment
open S31.Gadgets.Air.SourceMixedScheduledPublicPath

def rawGateUses {alpha z : GateSecure}
    (gate : RawGateRows alpha z) : List JointTuple :=
  (allUses (List.ofFn gate.rows) []).map embedGateEvent

def rawGateYields {alpha z : GateSecure}
    (gate : RawGateRows alpha z) : List JointTuple :=
  (allYields (List.ofFn gate.rows) []).map embedGateEvent

/-- All-row algebraic data and source event alignment before Gate/bridge
denominator conditions are supplied. The chip contract follows the existing
paired-interaction theorem, which derives its own nonzero conditions. -/
structure RawAuthenticatedMixedTrace {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure) where
  gate : RawGateRows alpha z
  chip : Fin N → ChipRows 8 (by decide) alpha z
  bridge : Fin N → RawBridgeRows alpha z
  gateRowsEq : List.ofFn gate.rows = boundary.jointGateSource.gateRows
  publicWords : List Quad
  publicWordsEq : publicWords =
    List.ofFn (fun output : Fin 8 => base (boundary.publicOutputs output))
  positiveAligned :
    ((rawGateUses gate ++ publicOutputYields publicWords) ++
      (List.finRange N).flatMap (fun call =>
        (bridge call).gateEvents ++ (chip call).inputEvents ++
          (bridge call).finishEvents)).Perm
      (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
  negativeAligned :
    (rawGateYields gate ++ (List.finRange N).flatMap (fun call =>
      (chip call).outputEvents ++ (bridge call).startEvents)).Perm
      (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)
  claimFoldZero :
    gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields publicWords) alpha z = 0

private theorem bridge_local_event_in_ideal {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (call : Fin N) (event : JointTuple)
    (hlocal : event ∈
      (((raw.bridge call).gateEvents ++ (raw.bridge call).startEvents) ++
        (raw.bridge call).finishEvents)) :
    event ∈
      ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
        (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)) := by
  rcases List.mem_append.mp hlocal with hgateStart | hfinish
  · rcases List.mem_append.mp hgateStart with hgate | hstart
    · have hcall : event ∈
          (raw.bridge call).gateEvents ++ (raw.chip call).inputEvents ++
            (raw.bridge call).finishEvents := by
        simp only [List.mem_append]
        exact Or.inl (Or.inl hgate)
      have hleft : event ∈
          ((rawGateUses raw.gate ++ publicOutputYields raw.publicWords) ++
            (List.finRange N).flatMap (fun call =>
              (raw.bridge call).gateEvents ++ (raw.chip call).inputEvents ++
                (raw.bridge call).finishEvents)) :=
        List.mem_append_right _
          (List.mem_flatMap.mpr ⟨call, by simp, hcall⟩)
      exact List.mem_append_left _ ((raw.positiveAligned.mem_iff).mp hleft)
    · have hcall : event ∈
          (raw.chip call).outputEvents ++ (raw.bridge call).startEvents :=
        List.mem_append_right _ hstart
      have hleft : event ∈
          rawGateYields raw.gate ++ (List.finRange N).flatMap (fun call =>
            (raw.chip call).outputEvents ++ (raw.bridge call).startEvents) :=
        List.mem_append_right _
          (List.mem_flatMap.mpr ⟨call, by simp, hcall⟩)
      exact List.mem_append_right _ ((raw.negativeAligned.mem_iff).mp hleft)
  · have hcall : event ∈
        (raw.bridge call).gateEvents ++ (raw.chip call).inputEvents ++
          (raw.bridge call).finishEvents :=
      List.mem_append_right _ hfinish
    have hleft : event ∈
        ((rawGateUses raw.gate ++ publicOutputYields raw.publicWords) ++
          (List.finRange N).flatMap (fun call =>
            (raw.bridge call).gateEvents ++ (raw.chip call).inputEvents ++
              (raw.bridge call).finishEvents)) :=
      List.mem_append_right _
        (List.mem_flatMap.mpr ⟨call, by simp, hcall⟩)
    exact List.mem_append_left _ ((raw.positiveAligned.mem_iff).mp hleft)

/-- One widened challenge exclusion supplies all Gate and bridge denominator
conditions and yields the previously checked all-row trace contract. -/
def RawAuthenticatedMixedTrace.toChecked {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (hgood : (alpha, z) ∉
      mixedErrorPairs boundary rows raw.gate.rows) :
    AuthenticatedMixedTrace boundary rows alpha z := by
  let gate := raw.gate.toChecked boundary rows raw.gateRowsEq hgood
  let bridge : Fin N → BridgeRows alpha z := fun call =>
    (raw.bridge call).toCheckedOutsideMixed boundary rows raw.gate.rows
      (bridge_local_event_in_ideal raw call) hgood
  refine {
    gate := gate
    chip := raw.chip
    bridge := bridge
    gateRowsEq := ?_
    publicWords := raw.publicWords
    publicWordsEq := raw.publicWordsEq
    positiveAligned := ?_
    negativeAligned := ?_
    claimFoldZero := ?_ }
  · exact raw.gateRowsEq
  · exact raw.positiveAligned
  · exact raw.negativeAligned
  · simpa [gate, bridge] using raw.claimFoldZero

/-- Keep the raw-to-checked construction behind a theorem constant when the
source-level false-claim argument uses reciprocal closure. -/
theorem raw_closed_ideal_event_lists {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (hgood : (alpha, z) ∉ mixedErrorPairs boundary rows raw.gate.rows) :
    productionReciprocalSum7
      (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
      alpha z =
    productionReciprocalSum7
      (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)
      alpha z :=
  closed_ideal_event_lists (raw.toChecked hgood)

/-- The widened exceptional set is fixed by the source-shaped rows and has
at most one field's worth of choices per at most 36,494,846 coefficients.
This bound does not require a false claim or a nonpole challenge. -/
theorem mixed_error_card_bound {N : Nat} (hN : N ≤ 8)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (gateRows : Fin 512 → Row)
    (hshape : SourceShape boundary) :
    (mixedErrorPairs boundary rows gateRows).card ≤
      36494846 * Fintype.card GateSecure := by
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
  calc
    (mixedErrorPairs boundary rows gateRows).card ≤
        ((imbalancePairs7
          (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
          (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)) ∪
          eventPolePairs
            ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
              (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))).card +
          (gateOutputPolePairs gateRows).card := Finset.card_union_le _ _
    _ ≤ ((imbalancePairs7
          (boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish)
          (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start)).card +
          (eventPolePairs
            ((boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish) ++
              (boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start))).card) +
          (gateOutputPolePairs gateRows).card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (36491868 * Fintype.card GateSecure +
          2466 * Fintype.card GateSecure) +
          512 * Fintype.card GateSecure :=
        Nat.add_le_add
          (Nat.add_le_add
            (source_imbalance_pair_bound hN boundary rows hshape) hpoleCard)
          (gate_output_pole_card_le gateRows)
    _ = 36494846 * Fintype.card GateSecure := by ring

set_option maxHeartbeats 1000000
/-- A false public word under *raw* Gate/bridge AIR residuals and source
event alignment forces the verifier challenge into the widened pole/imbalance
set. This is conditional on the chip row model and full-trace premises, not
an accepted-STARK-proof theorem. -/
theorem raw_false_word_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (hlocal : LocalPublicPath hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z) :
    (alpha, z) ∈ mixedErrorPairs boundary rows raw.gate.rows ∧
      (mixedErrorPairs boundary rows raw.gate.rows).card ≤
        36494846 * Fintype.card GateSecure := by
  have hbound := mixed_error_card_bound hN boundary rows raw.gate.rows hshape
  constructor
  · by_cases hbad : (alpha, z) ∈ mixedErrorPairs boundary rows raw.gate.rows
    · exact hbad
    · have hclosed := raw_closed_ideal_event_lists raw hbad
      have herror := false_word_closed_pair_is_exceptional hN hpositive
        boundary rows initial hshape hlocal product lane hfalse
        alpha z hclosed
      exact False.elim (hbad (Finset.mem_union_left _
        (Finset.mem_union_left _ herror.2.1)))
  · exact hbound

/-- The scheduled variant obtains the local Gate arithmetic facts from the
raw all-row Gate residuals after nonpole conversion, and the chip step from
the checked chip AIR plus an explicit event projection. It does not assume
`LocalPublicPath` independently. The projection and compiler-owned schedule
remain trace correspondence premises. -/
theorem raw_scheduled_false_word_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (schedule : LocalPublicSchedule hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (raw : RawAuthenticatedMixedTrace boundary rows alpha z)
    (projection : ∀ hgood :
      (alpha, z) ∉ mixedErrorPairs boundary rows raw.gate.rows,
      EventProjection boundary rows alpha z
        (raw.toChecked hgood).gate
        (raw.toChecked hgood).chip
        (raw.toChecked hgood).bridge
        (raw.toChecked hgood).publicWords)
    (hconstant : ∀ call,
      (raw.chip call).constant = boundary.constants call) :
    (alpha, z) ∈ mixedErrorPairs boundary rows raw.gate.rows ∧
      (mixedErrorPairs boundary rows raw.gate.rows).card ≤
        36494846 * Fintype.card GateSecure := by
  have hbound := mixed_error_card_bound hN boundary rows raw.gate.rows hshape
  constructor
  · by_cases hbad : (alpha, z) ∈ mixedErrorPairs boundary rows raw.gate.rows
    · exact hbad
    · let trace : AuthenticatedMixedTrace boundary rows alpha z :=
        raw.toChecked hbad
      have hlocal : LocalPublicPath hN hpositive boundary rows initial :=
        schedule.toLocalPublicPath trace (projection hbad) hconstant
      have hclosed := raw_closed_ideal_event_lists raw hbad
      have herror := false_word_closed_pair_is_exceptional hN hpositive
        boundary rows initial hshape hlocal product lane hfalse
        alpha z hclosed
      exact False.elim (hbad (Finset.mem_union_left _
        (Finset.mem_union_left _ herror.2.1)))
  · exact hbound

set_option maxHeartbeats 200000

end S31.Gadgets.Air.SourceMixedRawTraceClosure
