import S31.Gadgets.Air.TaggedPairSourceComposition

/-!
First exact-event projection step for the staged tagged pair: the two
relation IDs are disjoint, so filtering a joint seven-word permutation by
the chip tag discards all Gate-only events and preserves all chip events.
Decoding call IDs, field steps, and four-lane values into per-call paths is
a separate theorem obligation.
-/

namespace S31.Gadgets.Air.TaggedPairEventProjection

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition

noncomputable def chipTaggedEvents (events : List JointTuple) :
    List JointTuple := by
  classical
  exact events.filter (fun event => decide (IsChipEvent event))

theorem chipTaggedEvents_append (left right : List JointTuple) :
    chipTaggedEvents (left ++ right) =
      chipTaggedEvents left ++ chipTaggedEvents right := by
  classical
  simp [chipTaggedEvents]

theorem chipTaggedEvents_perm {left right : List JointTuple}
    (hperm : left.Perm right) :
    (chipTaggedEvents left).Perm (chipTaggedEvents right) := by
  classical
  exact hperm.filter _

theorem chipTaggedEvents_gate_only (events : List JointTuple)
    (hgate : ∀ event, event ∈ events → IsGateEvent event) :
    chipTaggedEvents events = [] := by
  classical
  have hnot : ∀ event ∈ events, ¬IsChipEvent event := by
    intro event hmem
    exact gate_chip_tags_disjoint event (hgate event hmem)
  simpa [chipTaggedEvents] using hnot

theorem chipTaggedEvents_chip_only (events : List JointTuple)
    (hchip : ∀ event, event ∈ events → IsChipEvent event) :
    chipTaggedEvents events = events := by
  classical
  simpa [chipTaggedEvents] using hchip

/-- Generic exact multiset projection: a Gate-only prefix on each side is
removed, leaving the same chip-tagged multiset. The soundness-critical
classification of circuit events is an explicit premise. -/
theorem chip_balance_of_joint_gate_prefixes
    (gateYields gateUses leftEvents rightEvents : List JointTuple)
    (hgateYields : ∀ event,
      event ∈ gateYields → IsGateEvent event)
    (hgateUses : ∀ event,
      event ∈ gateUses → IsGateEvent event)
    (hjoint : (gateYields ++ leftEvents).Perm
      (gateUses ++ rightEvents)) :
    (chipTaggedEvents leftEvents).Perm
      (chipTaggedEvents rightEvents) := by
  classical
  have hfiltered := chipTaggedEvents_perm hjoint
  simpa only [chipTaggedEvents_append,
    chipTaggedEvents_gate_only gateYields hgateYields,
    chipTaggedEvents_gate_only gateUses hgateUses,
    List.nil_append] using hfiltered

/-- A seven-word chip tuple belongs to one verifier-fixed call. -/
def IsChipCallEvent (call : F) (event : JointTuple) : Prop :=
  IsChipEvent event ∧ event 1 = liftBase call

noncomputable def callTaggedEvents (call : F)
    (events : List JointTuple) : List JointTuple := by
  classical
  exact events.filter (fun event => decide (IsChipCallEvent call event))

theorem callTaggedEvents_append (call : F)
    (left right : List JointTuple) :
    callTaggedEvents call (left ++ right) =
      callTaggedEvents call left ++ callTaggedEvents call right := by
  classical
  simp [callTaggedEvents]

theorem callTaggedEvents_perm {left right : List JointTuple}
    (call : F) (hperm : left.Perm right) :
    (callTaggedEvents call left).Perm (callTaggedEvents call right) := by
  classical
  exact hperm.filter _

theorem callTaggedEvents_gate_only (call : F)
    (events : List JointTuple)
    (hgate : ∀ event, event ∈ events → IsGateEvent event) :
    callTaggedEvents call events = [] := by
  classical
  have hnot : ∀ event ∈ events, ¬IsChipCallEvent call event := by
    intro event hmem hcall
    exact gate_chip_tags_disjoint event (hgate event hmem) hcall.1
  simpa [callTaggedEvents] using hnot

theorem callTaggedEvents_own_call (call : F)
    (events : List JointTuple)
    (hown : ∀ event, event ∈ events → IsChipCallEvent call event) :
    callTaggedEvents call events = events := by
  classical
  simpa [callTaggedEvents] using hown

theorem callTaggedEvents_other_call (call other : F)
    (hne : call ≠ other) (events : List JointTuple)
    (hother : ∀ event,
      event ∈ events → IsChipCallEvent other event) :
    callTaggedEvents call events = [] := by
  classical
  have hnot : ∀ event ∈ events, ¬IsChipCallEvent call event := by
    intro event hmem hcall
    have htag := (hcall.2).symm.trans (hother event hmem).2
    exact hne (liftBase_injective htag)
  simpa [callTaggedEvents] using hnot

/-- Exact per-call tuple balance follows from a joint permutation when
Gate events are classified, the other call has a distinct fixed tag, and
all four chip sublists have their stated tags. This does not yet decode
step/state coordinates into `RawChipIndexCoverage` events. -/
theorem selected_call_balance_of_joint
    (call other : F) (hne : call ≠ other)
    (gateYields gateUses ownYields ownUses otherYields otherUses :
      List JointTuple)
    (hgateYields : ∀ event,
      event ∈ gateYields → IsGateEvent event)
    (hgateUses : ∀ event,
      event ∈ gateUses → IsGateEvent event)
    (hownYields : ∀ event,
      event ∈ ownYields → IsChipCallEvent call event)
    (hownUses : ∀ event,
      event ∈ ownUses → IsChipCallEvent call event)
    (hotherYields : ∀ event,
      event ∈ otherYields → IsChipCallEvent other event)
    (hotherUses : ∀ event,
      event ∈ otherUses → IsChipCallEvent other event)
    (hjoint :
      (gateYields ++ ownYields ++ otherYields).Perm
        (gateUses ++ ownUses ++ otherUses)) :
    ownYields.Perm ownUses := by
  have hfiltered := callTaggedEvents_perm call hjoint
  simpa only [callTaggedEvents_append,
    callTaggedEvents_gate_only call gateYields hgateYields,
    callTaggedEvents_gate_only call gateUses hgateUses,
    callTaggedEvents_own_call call ownYields hownYields,
    callTaggedEvents_own_call call ownUses hownUses,
    callTaggedEvents_other_call call other hne otherYields hotherYields,
    callTaggedEvents_other_call call other hne otherUses hotherUses,
    List.nil_append, List.append_nil] using hfiltered

theorem sourceChipInputTuple_own_call {R : Nat} (call : F)
    (step : Fin R → F) (input : Fin R → Fin 4 → F)
    (row : Fin R) :
    IsChipCallEvent call
      (sourceChipInputTuple call step input row) := ⟨rfl, rfl⟩

theorem sourceChipOutputTuple_own_call {R : Nat} (call : F)
    (step : Fin R → F) (output : Fin R → Fin 4 → F)
    (row : Fin R) :
    IsChipCallEvent call
      (sourceChipOutputTuple call step output row) := ⟨rfl, rfl⟩

theorem sourceBridgeStartTuple_own_call (call : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    IsChipCallEvent call
      (sourceBridgeStartTuple call words row) := ⟨rfl, rfl⟩

theorem sourceBridgeFinishTuple_own_call (call rounds : F)
    (words : Fin 8 → Fin 16 → F) (row : Fin 16) :
    IsChipCallEvent call
      (sourceBridgeFinishTuple call rounds words row) := ⟨rfl, rfl⟩

theorem chip_inputEvents_own_call {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    ∀ event, event ∈ chip.inputEvents →
      IsChipCallEvent chip.call event := by
  intro event hmem
  simp only [ChipRows.inputEvents, List.mem_ofFn] at hmem
  obtain ⟨row, rfl⟩ := hmem
  exact sourceChipInputTuple_own_call chip.call chip.step chip.input row

theorem chip_outputEvents_own_call {m : Nat} {hm : 0 < m}
    {alpha z : GateSecure} (chip : ChipRows m hm alpha z) :
    ∀ event, event ∈ chip.outputEvents →
      IsChipCallEvent chip.call event := by
  intro event hmem
  simp only [ChipRows.outputEvents, List.mem_ofFn] at hmem
  obtain ⟨row, rfl⟩ := hmem
  exact sourceChipOutputTuple_own_call chip.call chip.step chip.output row

theorem bridge_startEvents_own_call {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    ∀ event, event ∈ bridge.startEvents →
      IsChipCallEvent bridge.call event := by
  intro event hmem
  simp only [BridgeRows.startEvents, sourceBridgeStartEvents,
    List.mem_singleton] at hmem
  subst event
  exact sourceBridgeStartTuple_own_call bridge.call bridge.words
    sourceBridgeAnchor

theorem bridge_finishEvents_own_call {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    ∀ event, event ∈ bridge.finishEvents →
      IsChipCallEvent bridge.call event := by
  intro event hmem
  simp only [BridgeRows.finishEvents, sourceBridgeFinishEvents,
    List.mem_singleton] at hmem
  subst event
  exact sourceBridgeFinishTuple_own_call bridge.call bridge.rounds
    bridge.words sourceBridgeAnchor

theorem outputEventsAux_gate_only (index : Nat)
    (outputs : List Quad) :
    ∀ event, event ∈ outputEventsAux index outputs →
      IsGateEvent event := by
  induction outputs generalizing index with
  | nil => simp [outputEventsAux]
  | cons value rest ih =>
      intro event hmem
      simp only [outputEventsAux, List.mem_cons] at hmem
      rcases hmem with rfl | hrest
      · exact paddedGateTuple_isGate _ _
      · exact ih (index + 1) event hrest

theorem publicOutputYields_gate_only (outputs : List Quad) :
    ∀ event, event ∈ publicOutputYields outputs →
      IsGateEvent event := by
  intro event hmem
  simp only [publicOutputYields, List.mem_append,
    List.mem_singleton] at hmem
  rcases hmem with haux | rfl
  · exact outputEventsAux_gate_only 0 outputs event haux
  · exact paddedGateTuple_isGate _ _

theorem bridge_gateEvents_gate_only {alpha z : GateSecure}
    (bridge : BridgeRows alpha z) :
    ∀ event, event ∈ bridge.gateEvents →
      IsGateEvent event := by
  intro event hmem
  simp only [BridgeRows.gateEvents, sourceBridgeGateEvents,
    List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact sourceBridgeGateTuple_isGate _ _ _ _

/-- Project the source-shaped exact seven-word permutation to call 0's
value-bearing chip and bridge events. Circuit Gate classification and both
bridge-to-chip call ID equalities are explicit compiler/verifier premises.
Distinct call IDs prevent events from the other call from cancelling here. -/
theorem source_joint_implies_first_call_balance
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    {alpha z : GateSecure}
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad)
    (hcircuitYields : ∀ event,
      event ∈ circuitYields → IsGateEvent event)
    (hcircuitUses : ∀ event,
      event ∈ circuitUses → IsGateEvent event)
    (hcall₀ : bridge₀.call = chip₀.call)
    (hcall₁ : bridge₁.call = chip₁.call)
    (hdistinct : chip₀.call ≠ chip₁.call)
    (hjoint :
      ((circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
        (chip₀.inputEvents ++ chip₁.inputEvents) ++
        (bridge₀.finishEvents ++ bridge₁.finishEvents)).Perm
        (circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
          (bridge₀.startEvents ++ bridge₁.startEvents))) :
    (chip₀.inputEvents ++ bridge₀.finishEvents).Perm
      (chip₀.outputEvents ++ bridge₀.startEvents) := by
  have hgateLeft : ∀ event,
      event ∈ (circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) →
      IsGateEvent event := by
    intro event hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((hcy | hpublic) | (hb₀ | hb₁))
    · exact hcircuitYields event hcy
    · exact publicOutputYields_gate_only outputs event hpublic
    · exact bridge_gateEvents_gate_only bridge₀ event hb₀
    · exact bridge_gateEvents_gate_only bridge₁ event hb₁
  have hfinish₀ : ∀ event, event ∈ bridge₀.finishEvents →
      IsChipCallEvent chip₀.call event := by
    simpa only [hcall₀] using bridge_finishEvents_own_call bridge₀
  have hfinish₁ : ∀ event, event ∈ bridge₁.finishEvents →
      IsChipCallEvent chip₁.call event := by
    simpa only [hcall₁] using bridge_finishEvents_own_call bridge₁
  have hstart₀ : ∀ event, event ∈ bridge₀.startEvents →
      IsChipCallEvent chip₀.call event := by
    simpa only [hcall₀] using bridge_startEvents_own_call bridge₀
  have hstart₁ : ∀ event, event ∈ bridge₁.startEvents →
      IsChipCallEvent chip₁.call event := by
    simpa only [hcall₁] using bridge_startEvents_own_call bridge₁
  have hfiltered := callTaggedEvents_perm chip₀.call hjoint
  simpa only [callTaggedEvents_append,
    callTaggedEvents_gate_only chip₀.call _ hgateLeft,
    callTaggedEvents_gate_only chip₀.call circuitUses hcircuitUses,
    callTaggedEvents_own_call chip₀.call chip₀.inputEvents
      (chip_inputEvents_own_call chip₀),
    callTaggedEvents_own_call chip₀.call chip₀.outputEvents
      (chip_outputEvents_own_call chip₀),
    callTaggedEvents_own_call chip₀.call bridge₀.finishEvents hfinish₀,
    callTaggedEvents_own_call chip₀.call bridge₀.startEvents hstart₀,
    callTaggedEvents_other_call chip₀.call chip₁.call hdistinct
      chip₁.inputEvents (chip_inputEvents_own_call chip₁),
    callTaggedEvents_other_call chip₀.call chip₁.call hdistinct
      chip₁.outputEvents (chip_outputEvents_own_call chip₁),
    callTaggedEvents_other_call chip₀.call chip₁.call hdistinct
      bridge₁.finishEvents hfinish₁,
    callTaggedEvents_other_call chip₀.call chip₁.call hdistinct
      bridge₁.startEvents hstart₁,
    List.nil_append, List.append_nil] using hfiltered

/-- The symmetric projection for call 1. The source event order remains
unchanged; filtering by the second fixed call tag discards call 0. -/
theorem source_joint_implies_second_call_balance
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    {alpha z : GateSecure}
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad)
    (hcircuitYields : ∀ event,
      event ∈ circuitYields → IsGateEvent event)
    (hcircuitUses : ∀ event,
      event ∈ circuitUses → IsGateEvent event)
    (hcall₀ : bridge₀.call = chip₀.call)
    (hcall₁ : bridge₁.call = chip₁.call)
    (hdistinct : chip₀.call ≠ chip₁.call)
    (hjoint :
      ((circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
        (chip₀.inputEvents ++ chip₁.inputEvents) ++
        (bridge₀.finishEvents ++ bridge₁.finishEvents)).Perm
        (circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
          (bridge₀.startEvents ++ bridge₁.startEvents))) :
    (chip₁.inputEvents ++ bridge₁.finishEvents).Perm
      (chip₁.outputEvents ++ bridge₁.startEvents) := by
  have hgateLeft : ∀ event,
      event ∈ (circuitYields ++ publicOutputYields outputs) ++
        (bridge₀.gateEvents ++ bridge₁.gateEvents) →
      IsGateEvent event := by
    intro event hmem
    simp only [List.mem_append] at hmem
    rcases hmem with ((hcy | hpublic) | (hb₀ | hb₁))
    · exact hcircuitYields event hcy
    · exact publicOutputYields_gate_only outputs event hpublic
    · exact bridge_gateEvents_gate_only bridge₀ event hb₀
    · exact bridge_gateEvents_gate_only bridge₁ event hb₁
  have hfinish₀ : ∀ event, event ∈ bridge₀.finishEvents →
      IsChipCallEvent chip₀.call event := by
    simpa only [hcall₀] using bridge_finishEvents_own_call bridge₀
  have hfinish₁ : ∀ event, event ∈ bridge₁.finishEvents →
      IsChipCallEvent chip₁.call event := by
    simpa only [hcall₁] using bridge_finishEvents_own_call bridge₁
  have hstart₀ : ∀ event, event ∈ bridge₀.startEvents →
      IsChipCallEvent chip₀.call event := by
    simpa only [hcall₀] using bridge_startEvents_own_call bridge₀
  have hstart₁ : ∀ event, event ∈ bridge₁.startEvents →
      IsChipCallEvent chip₁.call event := by
    simpa only [hcall₁] using bridge_startEvents_own_call bridge₁
  have hfiltered := callTaggedEvents_perm chip₁.call hjoint
  simpa only [callTaggedEvents_append,
    callTaggedEvents_gate_only chip₁.call _ hgateLeft,
    callTaggedEvents_gate_only chip₁.call circuitUses hcircuitUses,
    callTaggedEvents_own_call chip₁.call chip₁.inputEvents
      (chip_inputEvents_own_call chip₁),
    callTaggedEvents_own_call chip₁.call chip₁.outputEvents
      (chip_outputEvents_own_call chip₁),
    callTaggedEvents_own_call chip₁.call bridge₁.finishEvents hfinish₁,
    callTaggedEvents_own_call chip₁.call bridge₁.startEvents hstart₁,
    callTaggedEvents_other_call chip₁.call chip₀.call hdistinct.symm
      chip₀.inputEvents (chip_inputEvents_own_call chip₀),
    callTaggedEvents_other_call chip₁.call chip₀.call hdistinct.symm
      chip₀.outputEvents (chip_outputEvents_own_call chip₀),
    callTaggedEvents_other_call chip₁.call chip₀.call hdistinct.symm
      bridge₀.finishEvents hfinish₀,
    callTaggedEvents_other_call chip₁.call chip₀.call hdistinct.symm
      bridge₀.startEvents hstart₀,
    List.nil_append, List.append_nil] using hfiltered

end S31.Gadgets.Air.TaggedPairEventProjection
