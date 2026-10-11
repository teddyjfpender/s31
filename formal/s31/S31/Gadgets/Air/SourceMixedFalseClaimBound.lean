import S31.Gadgets.Air.SourceMixedLookupBound
import S31.Gadgets.Air.SourceMixedPublicClosure

/-!
A conditional source-level rejection statement for a false public output of
the 512-row mixed family. The theorem keeps local arithmetic, unique Gate
producers, source address/packing correspondence, and the ideal reciprocal
closure as explicit premises. It does not derive those premises from native
verifier acceptance or make a Fiat--Shamir sampling claim.
-/

namespace S31.Gadgets.Air.SourceMixedFalseClaimBound

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedAddressSchedule
open S31.Gadgets.Air.SourceMixedChainSemantics
open S31.Gadgets.Air.SourceMixedPublicClosure
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

/-- The local semantic facts required by the existing packed/public path
theorem. These are source/trace/AIR correspondence premises, not consequences
of an accepted native proof in this module. -/
structure LocalPublicPath {N : Nat} (hN : N ≤ 8)
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
  add : AcceptedRow boundary 22 (22 + 10 * N)
    (23 + 10 * N) .add
  mul : AcceptedRow boundary 22 (22 + 10 * N)
    (24 + 10 * N) .pointwiseMul
  outputs : ∀ product lane, OutputPath boundary N product lane

/-- A chosen public output word is false relative to the exact source
repeat-chain meaning. The chosen Boolean selects sum or product. -/
def FalsePublicWord {N : Nat} (boundary : Boundary N)
    (initial : State) (product : Bool) (lane : Fin 4) : Prop :=
  boundary.publicOutputs (outputSlot product lane) ≠
    if product then sourcePrefix N initial lane * initial lane
    else sourcePrefix N initial lane + initial lane

/-- Under local source/row facts, a false public word rules out exact ideal
Gate-plus-chip event balance. This is the deterministic part of rejection. -/
theorem false_word_excludes_exact_balance {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (hlocal : LocalPublicPath hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane) :
    ¬ (boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).Perm
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start) := by
  intro hjoint
  have houtputs := all_public_outputs_match_source hN hpositive
    boundary rows initial hlocal.addresses hlocal.unique hlocal.first
    hshape.rounds hlocal.constants hjoint hlocal.step
    hlocal.packedInitial hlocal.packedFinal hlocal.zero
    hlocal.add hlocal.mul hlocal.outputs
  cases product with
  | false =>
      exact hfalse (by simpa [FalsePublicWord] using (houtputs lane).1)
  | true =>
      exact hfalse (by simpa [FalsePublicWord] using (houtputs lane).2)

/-- For a fixed false public word and fixed ideal event lists, a closed
reciprocal identity must use one of at most `36,491,868·|QM31|` exceptional
challenge pairs. The exact balance contradiction and the exceptional-set
membership are both explicit in the conclusion. AIR/PCS/FRI authentication
and independent challenge sampling remain open obligations. -/
theorem false_word_closed_pair_is_exceptional {N : Nat}
    (hN : N ≤ 8) (hpositive : 0 < N)
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (initial : State)
    (hshape : SourceShape boundary)
    (hlocal : LocalPublicPath hN hpositive boundary rows initial)
    (product : Bool) (lane : Fin 4)
    (hfalse : FalsePublicWord boundary initial product lane)
    (alpha z : GateSecure)
    (hclosed : productionReciprocalSum7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish) alpha z =
      productionReciprocalSum7
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start) alpha z) :
    (¬ (boundary.jointGateSource.circuitUses ++
      jointUses rows boundary.finish).Perm
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)) ∧
    ((alpha, z) ∈ imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)) ∧
    (imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start)).card ≤
      36491868 * Fintype.card GateSecure := by
  have hnot := false_word_excludes_exact_balance hN hpositive
    boundary rows initial hshape hlocal product lane hfalse
  have herror := (source_closed_or_error boundary rows alpha z hclosed)
    |>.resolve_left hnot
  have hbound :
      (imbalancePairs7
        (boundary.jointGateSource.circuitUses ++
          jointUses rows boundary.finish)
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start)).card ≤
        36491868 * Fintype.card GateSecure := by
    simpa [imbalancePairs7, hnot] using
      source_false_closure_pair_bound hN boundary rows hshape hnot
  exact ⟨hnot, herror, hbound⟩

end S31.Gadgets.Air.SourceMixedFalseClaimBound
