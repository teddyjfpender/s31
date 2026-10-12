import S31.Gadgets.Air.TaggedPairEventDecode
import S31.Gadgets.Functional.SSAInstalledBytecodePublicInput

/-!
The source-shaped five-component lookup reduction, stated with an exception
set that is meaningful for an honest witness. `badPairs7` contains the pole
and cancellation challenges for *any* fixed event lists. If those lists are
already equal, every non-pole challenge closes, so asking an accepted honest
trace to avoid `badPairs7` is impossible. The error event is instead defined
only when the fixed seven-word multisets differ.

The circuit/chip/bridge row equations, exact circuit claim interpretation,
and final claim fold remain premises of the source-shaped theorem. This file
does not derive them from a native verifier acceptance, nor does it model
Fiat--Shamir sampling, PCS/FRI, or the Zig-to-Lean row correspondence.
-/

namespace S31.Gadgets.Air.TaggedPairConditionalCorrespondence

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.LogUpCount

/-- Fixed-witness lookup error event. An honest exact multiset has no
false-closure event, even though its reciprocal identity holds at ordinary
challenges. The `if` depends only on the two pre-challenge event lists. -/
noncomputable def imbalancePairs7 (left right : List JointTuple) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact if left.Perm right then ∅ else badPairs7 left right

theorem imbalancePairs7_empty_of_balance (left right : List JointTuple)
    (hbalance : left.Perm right) :
    imbalancePairs7 left right = ∅ := by
  simp [imbalancePairs7, hbalance]

/-- No false-closure pairs exist for a balanced witness. For an imbalanced
witness, the prior seven-coordinate polynomial argument gives the old
quadratic collision bound. The sharper bivariate budget is a separate
unformalized result. Both event counts must be below the M31 modulus so an
integer multiplicity cannot vanish upon reduction to the base field. -/
theorem imbalancePairs7_card_le (left right : List JointTuple)
    (hleft : left.length < 2147483647)
    (hright : right.length < 2147483647) :
    (imbalancePairs7 left right).card ≤
      (6 * (left ++ right).toFinset.card ^ 2 +
        2 * (left ++ right).toFinset.card) *
        Fintype.card GateSecure := by
  classical
  by_cases hbalance : left.Perm right
  · simp [imbalancePairs7, hbalance]
  · simpa [imbalancePairs7, hbalance] using
      badPairs7_card_le left right hleft hright hbalance

/-- A closed source-shaped reciprocal identity either reflects exact
integerized tuple-count balance or lands in the fixed-witness error event.
The statement does not call a challenge "good" after seeing acceptance. -/
theorem closed_pair_balance_or_error (left right : List JointTuple)
    (alpha z : GateSecure)
    (hclosed : productionReciprocalSum7 left alpha z =
      productionReciprocalSum7 right alpha z) :
    left.Perm right ∨ (alpha, z) ∈ imbalancePairs7 left right := by
  classical
  by_cases hbalance : left.Perm right
  · exact Or.inl hbalance
  · right
    have hbad : (alpha, z) ∈ badPairs7 left right := by
      by_contra hnot
      exact hbalance
        (exact_joint_events_outside_badPairs7 left right alpha z hnot hclosed)
    simpa [imbalancePairs7, hbalance] using hbad

theorem closed_pair_balance_outside_error (left right : List JointTuple)
    (alpha z : GateSecure)
    (hclosed : productionReciprocalSum7 left alpha z =
      productionReciprocalSum7 right alpha z)
    (hgood : (alpha, z) ∉ imbalancePairs7 left right) :
    left.Perm right := by
  exact (closed_pair_balance_or_error left right alpha z hclosed).resolve_right hgood

/-- Exact signed event lists for the verifier's fixed order:
`[circuit, chip 0, chip 1, bridge 0, bridge 1]`. These definitions expose
the event support on which the pre-challenge error set is measured. -/
def pairLeft {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    {alpha z : GateSecure}
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields : List JointTuple) (outputs : List Quad) :
    List JointTuple :=
  ((circuitYields ++ publicOutputYields outputs) ++
    (bridge₀.gateEvents ++ bridge₁.gateEvents) ++
    (chip₀.inputEvents ++ chip₁.inputEvents) ++
    (bridge₀.finishEvents ++ bridge₁.finishEvents))

def pairRight {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    {alpha z : GateSecure}
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitUses : List JointTuple) : List JointTuple :=
  circuitUses ++ (chip₀.outputEvents ++ chip₁.outputEvents) ++
    (bridge₀.startEvents ++ bridge₁.startEvents)

/-- Compose actual source-shaped chip and bridge interaction-row equations,
the circuit claimed-sum interpretation, and the verifier's five-claim fold.
The error set is empty on an exact witness and is quantitatively bounded on
an inexact one. The resulting permutation is still at seven-word tuple
level; per-call endpoint paths and the generic SSA Gate join require their
respective event-projection premises. -/
theorem source_pair_claims_imply_exact_events_conditional
    {m₀ m₁ : Nat} {hm₀ : 0 < m₀} {hm₁ : 0 < m₁}
    (alpha z : GateSecure)
    (chip₀ : ChipRows m₀ hm₀ alpha z)
    (chip₁ : ChipRows m₁ hm₁ alpha z)
    (bridge₀ bridge₁ : BridgeRows alpha z)
    (circuitYields circuitUses : List JointTuple)
    (outputs : List Quad) (circuitClaim : GateSecure)
    (hcircuit : circuitClaim =
      productionReciprocalSum7 circuitYields alpha z -
      productionReciprocalSum7 circuitUses alpha z)
    (hverify : verifierClaimFold outputs
      (pairClaims circuitClaim chip₀.claim chip₁.claim
        bridge₀.claim bridge₁.claim) alpha z = 0)
    (hgood : (alpha, z) ∉ imbalancePairs7
      (pairLeft chip₀ chip₁ bridge₀ bridge₁ circuitYields outputs)
      (pairRight chip₀ chip₁ bridge₀ bridge₁ circuitUses)) :
    (∀ row lane,
      chip₀.output row lane = chip₀.input row lane ^ 2 + chip₀.constant) ∧
    (∀ row lane,
      chip₁.output row lane = chip₁.input row lane ^ 2 + chip₁.constant) ∧
    (pairLeft chip₀ chip₁ bridge₀ bridge₁ circuitYields outputs).Perm
      (pairRight chip₀ chip₁ bridge₀ bridge₁ circuitUses) := by
  classical
  by_cases hbalance :
      (pairLeft chip₀ chip₁ bridge₀ bridge₁ circuitYields outputs).Perm
        (pairRight chip₀ chip₁ bridge₀ bridge₁ circuitUses)
  · exact ⟨chip₀.arithmetic_sound, chip₁.arithmetic_sound, hbalance⟩
  · have hnot : (alpha, z) ∉ badPairs7
        (pairLeft chip₀ chip₁ bridge₀ bridge₁ circuitYields outputs)
        (pairRight chip₀ chip₁ bridge₀ bridge₁ circuitUses) := by
      simpa [imbalancePairs7, hbalance] using hgood
    simpa only [pairLeft, pairRight] using
      source_pair_claims_imply_exact_events alpha z chip₀ chip₁
        bridge₀ bridge₁ circuitYields circuitUses outputs circuitClaim
        hcircuit hverify (by simpa only [pairLeft, pairRight] using hnot)

/-- Canonical six-word Gate events padded to the seven-word joint relation.
The shape of these words is a separate compiler/manifest invariant. -/
def embedGateEvent (event : GateLookup.Event) : JointTuple :=
  paddedGateTuple (event.1 : F) event.2

theorem embedGateEvent_injective_of_canonical
    (left right : GateLookup.Event)
    (hleft : left.1 < 2147483647)
    (hright : right.1 < 2147483647)
    (heq : embedGateEvent left = embedGateEvent right) :
    left = right := by
  have haddress : (left.1 : F) = (right.1 : F) := by
    apply liftBase_injective
    simpa [embedGateEvent, paddedGateTuple] using
      congrFun heq ⟨1, by decide⟩
  have hnat : left.1 = right.1 := by
    have hval := congrArg ZMod.val haddress
    simpa [ZMod.val_natCast_of_lt hleft,
      ZMod.val_natCast_of_lt hright] using hval
  have ha : left.2.a = right.2.a := by
    apply liftBase_injective
    simpa [embedGateEvent, paddedGateTuple] using
      congrFun heq ⟨2, by decide⟩
  have hb : left.2.b = right.2.b := by
    apply liftBase_injective
    simpa [embedGateEvent, paddedGateTuple] using
      congrFun heq ⟨3, by decide⟩
  have hc : left.2.c = right.2.c := by
    apply liftBase_injective
    simpa [embedGateEvent, paddedGateTuple] using
      congrFun heq ⟨4, by decide⟩
  have hd : left.2.d = right.2.d := by
    apply liftBase_injective
    simpa [embedGateEvent, paddedGateTuple] using
      congrFun heq ⟨5, by decide⟩
  exact Prod.ext hnat (Quad.ext ha hb hc hd)

noncomputable def gateTaggedEvents (events : List JointTuple) :
    List JointTuple := by
  classical
  exact events.filter (fun event => decide (IsGateEvent event))

theorem gateTaggedEvents_append (left right : List JointTuple) :
    gateTaggedEvents (left ++ right) =
      gateTaggedEvents left ++ gateTaggedEvents right := by
  classical
  simp [gateTaggedEvents]

theorem gateTaggedEvents_gate_only (events : List JointTuple)
    (hgate : ∀ event ∈ events, IsGateEvent event) :
    gateTaggedEvents events = events := by
  classical
  simpa [gateTaggedEvents] using hgate

theorem gateTaggedEvents_chip_only (events : List JointTuple)
    (hchip : ∀ event ∈ events, IsChipEvent event) :
    gateTaggedEvents events = [] := by
  classical
  have hnot : ∀ event ∈ events, ¬ IsGateEvent event := by
    intro event hmem hgate
    exact gate_chip_tags_disjoint event hgate (hchip event hmem)
  simpa [gateTaggedEvents] using hnot

/-- The exact joint balance authenticates the ideal Gate relation once the
source compiler has identified the two Gate-tagged sublists with the
physical row event lists. The chip relation ID ensures its events disappear
under Gate projection; canonical addresses prevent `Nat → M31` wraparound.
This theorem isolates the remaining source-to-native roster obligation in
`hyields` and `huses` instead of silently treating joint balance as Gate
balance. -/
theorem exact_joint_balance_implies_gate_balance
    (rows : List Row) (externalUses externalYields : List GateLookup.Event)
    (gateYields gateUses chipYields chipUses : List JointTuple)
    (hgateYields : ∀ event ∈ gateYields, IsGateEvent event)
    (hgateUses : ∀ event ∈ gateUses, IsGateEvent event)
    (hchipYields : ∀ event ∈ chipYields, IsChipEvent event)
    (hchipUses : ∀ event ∈ chipUses, IsChipEvent event)
    (hyields : gateYields =
      (allYields rows externalYields).map embedGateEvent)
    (huses : gateUses =
      (allUses rows externalUses).map embedGateEvent)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (hjoint : (gateYields ++ chipYields).Perm
      (gateUses ++ chipUses)) :
    balanced rows externalUses externalYields := by
  classical
  have hprojected := hjoint.filter (fun event => decide (IsGateEvent event))
  have hgate : gateYields.Perm gateUses := by
    change (gateTaggedEvents (gateYields ++ chipYields)).Perm
      (gateTaggedEvents (gateUses ++ chipUses)) at hprojected
    simpa only [gateTaggedEvents_append,
      gateTaggedEvents_gate_only gateYields hgateYields,
      gateTaggedEvents_gate_only gateUses hgateUses,
      gateTaggedEvents_chip_only chipYields hchipYields,
      gateTaggedEvents_chip_only chipUses hchipUses,
      List.append_nil] using hprojected
  have hmap : ((allUses rows externalUses).map embedGateEvent).Perm
      ((allYields rows externalYields).map embedGateEvent) := by
    rw [← huses, ← hyields]
    exact hgate.symm
  exact mapped_perm_reflects
    (allUses rows externalUses) (allYields rows externalYields)
    embedGateEvent
    (by
      intro left hl right hr heq
      exact embedGateEvent_injective_of_canonical left right
        (hcanonical left hl) (hcanonical right hr) heq)
    hmap

end S31.Gadgets.Air.TaggedPairConditionalCorrespondence
