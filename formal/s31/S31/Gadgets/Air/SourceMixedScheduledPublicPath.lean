import S31.Gadgets.Air.SourceMixedAuthenticatedTrace

/-!
The public-path contract can select source rows by their fixed addresses,
opcode, and positive output multiplicity without separately assuming their
arithmetic AIR checks. All nine residuals come from the all-512-row Gate
trace contract. The row schedule, producer uniqueness, and authentication of
the trace are still explicit premises.
-/

namespace S31.Gadgets.Air.SourceMixedScheduledPublicPath

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedChainSemantics
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedFalseClaimBound
open S31.Gadgets.Air.SourceMixedAuthenticatedTrace
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-- The same source-owned unpack/copy schedule as `OutputPath`, with row
arithmetic supplied by the authenticated Gate trace. -/
def ScheduledOutputPath {N : Nat} (boundary : Boundary N)
    (callCount : Nat) (product : Bool) (lane : Fin 4) : Prop :=
  ∃ unitAddress maskedAddress inverseAddress scalarAddress : Nat,
    ValueAt boundary unitAddress (unit lane) ∧
    ScheduledRow boundary (packedOutputAddress callCount product)
      unitAddress maskedAddress .pointwiseMul ∧
    (if lane.val = 0 then scalarAddress = maskedAddress else
      ValueAt boundary inverseAddress (unitInverse lane) ∧
      ScheduledRow boundary maskedAddress inverseAddress scalarAddress .mul) ∧
    ScheduledRow boundary scalarAddress 0
      (3 + (outputSlot product lane).val) .add

theorem scheduled_output_path_accepted {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (trace : AuthenticatedMixedTrace boundary rows alpha z)
    (callCount : Nat) (product : Bool) (lane : Fin 4)
    (hpath : ScheduledOutputPath boundary callCount product lane) :
    OutputPath boundary callCount product lane := by
  obtain ⟨unitAddress, maskedAddress, inverseAddress, scalarAddress,
    hunit, hmask, hinverse, hcopy⟩ := hpath
  refine ⟨unitAddress, maskedAddress, inverseAddress, scalarAddress,
    hunit, trace.scheduled_row_accepted _ _ _ _ hmask, ?_,
    trace.scheduled_row_accepted _ _ _ _ hcopy⟩
  by_cases hlane : lane.val = 0
  · simpa [hlane] using hinverse
  · simp only [hlane, ↓reduceIte] at hinverse ⊢
    exact ⟨hinverse.1,
      trace.scheduled_row_accepted _ _ _ _ hinverse.2⟩

/-- Source/public correspondence data with no selected-row AIR premise.
The global Gate AIR contract supplies those residuals when converting to
`LocalPublicPath`. -/
structure LocalPublicSchedule {N : Nat} (hN : N ≤ 8)
    (hpositive : 0 < N) (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State) : Prop where
  addresses : ∀ call slot,
    boundary.addresses call slot = canonicalAddress hN call slot
  unique : uniqueProduced (produced boundary)
  first : boundary.start ⟨0, hpositive⟩ = initial
  constants : ∀ call, boundary.constants call = (13 + call.val : F)
  step : ∀ call row,
    (rows call row).output = boundary.step call (rows call row).input
  packedInitial : ValueAt boundary 22 (packState initial)
  packedFinal : ValueAt boundary (22 + 10 * N)
    (packState (boundary.finish ⟨N - 1, by omega⟩))
  zero : ValueAt boundary 0 (base 0)
  add : ScheduledRow boundary 22 (22 + 10 * N)
    (23 + 10 * N) .add
  mul : ScheduledRow boundary 22 (22 + 10 * N)
    (24 + 10 * N) .pointwiseMul
  outputs : ∀ product lane, ScheduledOutputPath boundary N product lane

theorem LocalPublicSchedule.toLocalPublicPath {N : Nat}
    {hN : N ≤ 8} {hpositive : 0 < N}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {initial : State} {alpha z : GateSecure}
    (schedule : LocalPublicSchedule hN hpositive boundary rows initial)
    (trace : AuthenticatedMixedTrace boundary rows alpha z) :
    LocalPublicPath hN hpositive boundary rows initial := by
  exact {
    addresses := schedule.addresses
    unique := schedule.unique
    first := schedule.first
    constants := schedule.constants
    step := schedule.step
    packedInitial := schedule.packedInitial
    packedFinal := schedule.packedFinal
    zero := schedule.zero
    add := trace.scheduled_row_accepted _ _ _ _ schedule.add
    mul := trace.scheduled_row_accepted _ _ _ _ schedule.mul
    outputs := fun product lane =>
      scheduled_output_path_accepted trace N product lane
        (schedule.outputs product lane)
  }

/-- A false public word in a source-shaped, all-row-AIR checked trace can
close only at an exceptional challenge pair. Unlike the earlier path theorem,
the local schedule carries no independent arithmetic AIR assumptions. -/
theorem false_word_trace_from_schedule_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceMixedLookupBound.SourceShape boundary)
    (schedule : LocalPublicSchedule hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (trace : AuthenticatedMixedTrace boundary rows alpha z) :
    (alpha, z) ∈ TaggedPairConditionalCorrespondence.imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start) := by
  exact false_word_trace_is_exceptional hN hpositive boundary rows initial
    hshape (schedule.toLocalPublicPath trace) product lane hfalse
    alpha z trace

end S31.Gadgets.Air.SourceMixedScheduledPublicPath
