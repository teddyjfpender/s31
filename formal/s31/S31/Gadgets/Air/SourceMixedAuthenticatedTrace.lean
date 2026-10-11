import S31.Gadgets.Air.SourceMixedFalseClaimBound
import S31.Gadgets.Air.Qm31GateInteraction
import S31.Gadgets.Air.TaggedPairSourceComposition

/-!
An explicit all-row trace contract for the one-to-eight-call mixed family.
It identifies which data would have to be authenticated by the native
commitments and PCS/FRI verifier before the source-level false-claim theorem
can be applied. The contract is **not** derived from native proof acceptance.

The Gate, chip, and bridge residuals below are the already formalized logical
row equations. `positiveAligned` and `negativeAligned` are separate exact
compiler/trace-to-event-list correspondence premises. Neither a passing
honest-writer fixture nor a matching proof header establishes those premises
for an arbitrary prover-selected committed trace.
-/

namespace S31.Gadgets.Air.SourceMixedAuthenticatedTrace

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.Qm31GateInteraction
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Gadgets.Air.SourceMixedRoster
open S31.Gadgets.Air.SourceMixedPath
open S31.Gadgets.Air.SourceMixedLookupBound
open S31.Gadgets.Air.SourceMixedFalseClaimBound
open S31.Gadgets.Air.IndexedManyTaggedTupleBridge

private theorem gate_sum_embedded (events : List GateLookup.Event)
    (alpha z : GateSecure) :
    productionReciprocalSum7 (events.map embedGateEvent) alpha z =
      productionReciprocalSum events alpha z := by
  induction events with
  | nil => simp [productionReciprocalSum7, productionReciprocalSum]
  | cons event rest ih =>
      simp only [List.map_cons, productionReciprocalSum7,
        productionReciprocalSum, List.sum_cons] at ih ⊢
      rw [ih]
      have hcombine :
          combine7 (embedGateEvent event) alpha z =
            combineTerm (eventTuple event) alpha z := by
        simp only [combine7, combineTerm, eventTuple, embedGateEvent]
        rw [padded_gate_compression_eq_native_six]
      rw [hcombine]

/-- Every logical Gate row, including its preprocessed multiplicity, has
both native LogUp residuals checked. Nonzero denominators are explicit:
the paired residual alone is vacuous at two poles. -/
structure GateRows (alpha z : GateSecure) where
  rows : Fin 512 → Row
  previous : Equiv.Perm (Fin 512)
  first : Fin 512 → GateSecure
  last : Fin 512 → GateSecure
  claim : GateSecure
  use0Nonzero : ∀ i,
    (useTerm ((rows i).in0Address, (rows i).in0) alpha z).denominator ≠ 0
  use1Nonzero : ∀ i,
    (useTerm ((rows i).in1Address, (rows i).in1) alpha z).denominator ≠ 0
  yieldNonzero : ∀ i, (yieldTerm (rows i) alpha z).denominator ≠ 0
  pairResidual : ∀ i,
    LogUpInteraction.pairResidual (rowPair (rows i) alpha z).1
      (rowPair (rows i) alpha z).2 (first i) = 0
  yieldResidual : ∀ i,
    LogUpInteraction.singleResidual (yieldTerm (rows i) alpha z)
      (last i - last (previous i) - first i + claim / (512 : GateSecure)) = 0

def GateRows.uses {alpha z : GateSecure} (gate : GateRows alpha z) :
    List JointTuple :=
  (allUses (List.ofFn gate.rows) []).map embedGateEvent

def GateRows.yields {alpha z : GateSecure} (gate : GateRows alpha z) :
    List JointTuple :=
  (allYields (List.ofFn gate.rows) []).map embedGateEvent

/-- The Gate component's claim is the signed reciprocal sum of all 512
rows' exact events. No public or bridge use is silently added here. -/
theorem GateRows.claim_eq_events {alpha z : GateSecure}
    (gate : GateRows alpha z) :
    gate.claim = productionReciprocalSum7 gate.uses alpha z -
      productionReciprocalSum7 gate.yields alpha z := by
  have hrows := qm31_ops_claimed_sum 9 gate.previous gate.rows
    gate.first gate.last alpha z gate.claim gate.use0Nonzero
    gate.use1Nonzero gate.yieldNonzero gate.pairResidual gate.yieldResidual
  have hlist : gate.claim =
      ((List.ofFn gate.rows).map fun row => rowContribution row alpha z).sum := by
    simpa only [List.map_ofFn, List.sum_ofFn] using hrows
  have hgate := allGateContribution (List.ofFn gate.rows) [] [] alpha z
  have hzero : productionReciprocalSum ([] : List GateLookup.Event)
      alpha z = 0 := rfl
  rw [hzero] at hgate
  simp only [add_zero, sub_zero] at hgate
  rw [hlist, ← hgate]
  simp only [GateRows.uses, GateRows.yields, gate_sum_embedded]

private theorem reciprocal_append (left right : List JointTuple)
    (alpha z : GateSecure) :
    productionReciprocalSum7 (left ++ right) alpha z =
      productionReciprocalSum7 left alpha z +
        productionReciprocalSum7 right alpha z := by
  simp [productionReciprocalSum7]

/-- A concrete chip plus its bridge contributes Gate endpoint reads, chip
row inputs, and the bridge final endpoint positively; chip row outputs and
the bridge initial endpoint occur negatively. -/
theorem call_claim_eq_events {alpha z : GateSecure}
    (chip : ChipRows 8 (by decide) alpha z)
    (bridge : BridgeRows alpha z) :
    chip.claim + bridge.claim =
      productionReciprocalSum7
        (bridge.gateEvents ++ chip.inputEvents ++ bridge.finishEvents)
        alpha z -
      productionReciprocalSum7
        (chip.outputEvents ++ bridge.startEvents) alpha z := by
  rw [chip.claim_eq_events, bridge.claim_eq_events]
  repeat rw [reciprocal_append]
  ring

/-- This is the exact all-row evidence that a proof extractor or full-trace
audit verifier would need to return. `chip` and `bridge` carry arithmetic,
constant-row, interaction, and denominator residual premises; `gate` carries
the Gate interaction residuals. The two alignment fields must be established
from the source compiler and *committed* trace columns. `claimFoldZero` is
the native verifier's algebraic claim check. -/
structure AuthenticatedMixedTrace {N : Nat}
    (boundary : Boundary N)
    (rows : ∀ call, Fin (boundary.rounds call) → NativeRow)
    (alpha z : GateSecure) where
  gate : GateRows alpha z
  chip : Fin N → ChipRows 8 (by decide) alpha z
  bridge : Fin N → BridgeRows alpha z
  gateRowsEq : List.ofFn gate.rows = boundary.jointGateSource.gateRows
  publicWords : List Quad
  publicWordsEq : publicWords =
    List.ofFn (fun output : Fin 8 => base (boundary.publicOutputs output))
  positiveAligned :
    (gate.uses ++ publicOutputYields publicWords) ++
      (List.finRange N).flatMap (fun call =>
        (bridge call).gateEvents ++ (chip call).inputEvents ++
          (bridge call).finishEvents) =
      boundary.jointGateSource.circuitUses ++ jointUses rows boundary.finish
  negativeAligned :
    gate.yields ++ (List.finRange N).flatMap (fun call =>
      (chip call).outputEvents ++ (bridge call).startEvents) =
      boundary.jointGateSource.circuitYields ++ jointYields rows boundary.start
  claimFoldZero :
    gate.claim +
      ((List.finRange N).map (fun call =>
        (chip call).claim + (bridge call).claim)).sum +
      productionReciprocalSum7 (publicOutputYields publicWords) alpha z = 0

private theorem call_claims_sum {N : Nat} (alpha z : GateSecure)
    (chips : Fin N → ChipRows 8 (by decide) alpha z)
    (bridges : Fin N → BridgeRows alpha z)
    (calls : List (Fin N)) :
    (calls.map (fun call =>
      (chips call).claim + (bridges call).claim)).sum =
      productionReciprocalSum7
        (calls.flatMap fun call =>
          (bridges call).gateEvents ++ (chips call).inputEvents ++
            (bridges call).finishEvents) alpha z -
      productionReciprocalSum7
        (calls.flatMap fun call =>
          (chips call).outputEvents ++ (bridges call).startEvents)
        alpha z := by
  induction calls with
  | nil => simp [productionReciprocalSum7]
  | cons call rest ih =>
      simp only [List.map_cons, List.flatMap_cons, List.sum_cons]
      rw [call_claim_eq_events, ih]
      repeat rw [reciprocal_append]
      ring

/-- All component residuals and the native claim fold imply the exact
source-shaped *reciprocal identity* consumed by `SourceMixedLookupBound`.
The two event-list alignment equalities remain explicit, so this theorem
cannot be applied to an accepted succinct proof without a trace-authentication
and compiler-correspondence argument. -/
theorem closed_ideal_event_lists {N : Nat}
    {boundary : Boundary N}
    {rows : ∀ call, Fin (boundary.rounds call) → NativeRow}
    {alpha z : GateSecure}
    (trace : AuthenticatedMixedTrace boundary rows alpha z) :
    productionReciprocalSum7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish) alpha z =
      productionReciprocalSum7
        (boundary.jointGateSource.circuitYields ++
          jointYields rows boundary.start) alpha z := by
  have hgate := trace.gate.claim_eq_events
  have hcalls := call_claims_sum alpha z trace.chip trace.bridge
    (List.finRange N)
  have hfold := trace.claimFoldZero
  rw [hgate, hcalls] at hfold
  rw [← trace.positiveAligned, ← trace.negativeAligned]
  repeat rw [reciprocal_append]
  linear_combination hfold

/-- A false public word on the source-shaped trace can close only at an
exceptional challenge pair. The statement still assumes source shape,
semantic public paths, and an authenticated exact trace contract; no native
verifier success or Fiat--Shamir distribution claim is hidden here. -/
theorem false_word_trace_is_exceptional {N : Nat}
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
    (alpha, z) ∈ imbalancePairs7
      (boundary.jointGateSource.circuitUses ++
        jointUses rows boundary.finish)
      (boundary.jointGateSource.circuitYields ++
        jointYields rows boundary.start) := by
  exact (false_word_closed_pair_is_exceptional hN hpositive boundary rows
    initial hshape hlocal product lane hfalse alpha z
    (closed_ideal_event_lists trace)).2.1

end S31.Gadgets.Air.SourceMixedAuthenticatedTrace
