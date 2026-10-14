import S31.Gadgets.Functional.Correspondence.ControlGadgetGlobalGateJoin
import S31.Gadgets.Air.GatePublicInteraction

/-!
The finite control proof's claim-to-trace join. The native diagnostic checks
that all eleven claimed component sums are recomputed from the committed
base cells, and that the four Gate-producing components exhaust Gate yields.
For arbitrary accepted proofs, that authentication remains an explicit
premise until PCS/FRI and global component LogUp soundness are established.
-/

namespace S31.Functional.Correspondence.ControlGadgetClaimTrace

set_option maxHeartbeats 800000

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GatePublicInteraction
open S31.Gadgets.Air.GateProducerRoster
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceCorrespondence
open S31.Gadgets.Air.TaggedPairConditionalCorrespondence
open S31.Functional.Correspondence.ControlGadgetGlobalGateJoin
open S31.Functional.Correspondence.ControlGadgetAir
open S31.Functional.Correspondence.ControlGadgetPublicPins
open S31.Functional.Correspondence.ControlGadgetStatementPins

abbrev Event := S31.Gadgets.Air.GateLookup.Event

theorem padded_gate_reciprocal (event : Event) (alpha z : GateSecure) :
    1 / combine7 (embedGateEvent event) alpha z =
      1 / combineTerm (eventTuple event) alpha z := by
  have h := padded_gate_compression_eq_native_six
    (event.1 : F) event.2 alpha
  simpa [combine7, combineTerm, embedGateEvent, eventTuple] using
    congrArg (fun x : GateSecure => 1 / (x - z)) h

theorem padded_gate_reciprocal_sum (events : List Event)
    (alpha z : GateSecure) :
    productionReciprocalSum7 (events.map embedGateEvent) alpha z =
      productionReciprocalSum events alpha z := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      simp only [productionReciprocalSum7, productionReciprocalSum,
        List.map_cons, List.sum_cons] at ih ⊢
      rw [padded_gate_reciprocal, ih]

theorem native_public_sum_is_gate_sum (words : Fin 8 → Nat)
    (alpha z : GateSecure) :
    productionReciprocalSum7
      (publicOutputYields
        (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i)))) alpha z =
      productionReciprocalSum (publicUsesWithU words) alpha z := by
  rw [← public_uses_native_events, padded_gate_reciprocal_sum]

/-- The eleven native component claims are required to equal the signed
reciprocal sum reconstructed from the four producing components' committed
rows and all component Gate uses. This is an authentication premise, not a
consequence of public verifier acceptance alone. -/
structure ClaimedTrace (rows : List Row)
    (otherUses tripleYields conversionYields blakeYields : List Event)
    (claims : List GateSecure) (alpha z : GateSecure) : Prop where
  exactCellClaims : ∃ cellClaims : Fin 11 → GateSecure,
    claims = List.ofFn cellClaims ∧
      (List.ofFn cellClaims).sum =
        (rows.map fun row => rowContribution row alpha z).sum +
          productionReciprocalSum otherUses alpha z -
          productionReciprocalSum
            (tripleYields ++ conversionYields ++ blakeYields) alpha z

theorem ClaimedTrace.fromCells (claimed : ClaimedTrace rows otherUses
    triple conversion blake claims alpha z) :
    claims.sum =
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum otherUses alpha z -
        productionReciprocalSum (triple ++ conversion ++ blake) alpha z := by
  obtain ⟨cellClaims, hexact, hsum⟩ := claimed.exactCellClaims
  rw [hexact]
  exact hsum

/-- The complete external producer list is constructed from precisely the
three non-QM31 Gate-yielding components; therefore coverage is definitional.
The fixed address roster and local row AIR remain independently checked. -/
structure TraceBoundary (rows : List Row) (gates : List Gate)
    (otherUses tripleYields conversionYields blakeYields : List Event)
    (words : Fin 8 → Nat) : Prop where
  canonicalWords : ∀ i, words i < 2147483647
  uniqueAddresses :
    ((activeRows rows).map Row.outAddress ++
      (tripleYields ++ conversionYields ++ blakeYields).map Prod.fst).Nodup
  positiveOwner : ∀ gate ∈ gates, ∃ row ∈ rows,
    row.in0Address = gate.lhs ∧ row.in1Address = gate.rhs ∧
      row.outAddress = gate.out ∧
      row.flags = S31.Gadgets.Air.Qm31Ops.encode gate.op ∧
      0 < row.multiplicity ∧
      S31.Gadgets.Air.Qm31Ops.accepts row.flags row.in0 row.in1 row.output

def externalUses (words : Fin 8 → Nat) (otherUses : List Event) : List Event :=
  publicUsesWithU words ++ otherUses

def externalYields (triple conversion blake : List Event) : List Event :=
  triple ++ conversion ++ blake

theorem boundary_of_trace (rows : List Row) (gates : List Gate)
    (otherUses triple conversion blake : List Event)
    (words : Fin 8 → Nat)
    (traceBoundary : TraceBoundary rows gates otherUses triple conversion blake words) :
    GateBoundary rows gates (externalUses words otherUses)
      (externalYields triple conversion blake)
      (externalYields triple conversion blake) words := by
  refine ⟨traceBoundary.canonicalWords, ⟨otherUses, rfl⟩,
    traceBoundary.uniqueAddresses, ?_, traceBoundary.positiveOwner⟩
  intro event h
  exact h

structure GoodTraceChallenges (rows : List Row)
    (otherUses triple conversion blake : List Event)
    (words : Fin 8 → Nat) (alpha z : GateSecure) : Prop where
  canonicalAddresses : ∀ event ∈
    allUses rows (externalUses words otherUses) ++
      allYields rows (externalYields triple conversion blake),
      event.1 < 2147483647
  useCounts : ∀ event ∈
    allUses rows (externalUses words otherUses) ++
      allYields rows (externalYields triple conversion blake),
      (allUses rows (externalUses words otherUses)).count event < 2147483647
  yieldCounts : ∀ event ∈
    allUses rows (externalUses words otherUses) ++
      allYields rows (externalYields triple conversion blake),
      (allYields rows (externalYields triple conversion blake)).count event < 2147483647
  goodAlpha : alpha ∉ badAlpha
    (allUses rows (externalUses words otherUses) ++
      allYields rows (externalYields triple conversion blake))
  goodZ : z ∉ badZ
    (allUses rows (externalUses words otherUses))
    (allYields rows (externalYields triple conversion blake)) alpha

/-- Once the eleven component claims are identified with cell-derived
signed events, the native final sum forces the exact `GoodGateClosure.closed`
equation. There is no independent closure premise in the final theorem. -/
theorem closure_of_claimed_trace (rows : List Row)
    (otherUses triple conversion blake : List Event)
    (words : Fin 8 → Nat) (claims : List GateSecure)
    (alpha z : GateSecure)
    (claimed : ClaimedTrace rows otherUses triple conversion blake claims alpha z)
    (acceptedSum : nativeGateClosure
      (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i)))
      claims alpha z = 0)
    (good : GoodTraceChallenges rows otherUses triple conversion blake words alpha z) :
    GoodGateClosure rows (externalUses words otherUses)
      (externalYields triple conversion blake) alpha z := by
  refine ⟨good.canonicalAddresses, good.useCounts, good.yieldCounts,
    good.goodAlpha, good.goodZ, ?_⟩
  have hsum := nativeGateClosure_eq_event_sum
    (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i)))
    claims alpha z
  rw [native_public_sum_is_gate_sum] at hsum
  rw [claimed.fromCells] at hsum
  simp only [externalUses, externalYields,
    productionReciprocalSum_append] at hsum ⊢
  rw [hsum] at acceptedSum
  linear_combination acceptedSum

theorem control_public_lookup_of_claimed_trace
    (rows : List Row) (gates : List Gate)
    (otherUses triple conversion blake : List Event)
    (words : Fin 8 → Nat) (claims : List GateSecure)
    (alpha z : GateSecure)
    (boundary : TraceBoundary rows gates otherUses triple conversion blake words)
    (claimed : ClaimedTrace rows otherUses triple conversion blake claims alpha z)
    (acceptedSum : nativeGateClosure
      (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i)))
      claims alpha z = 0)
    (good : GoodTraceChallenges rows otherUses triple conversion blake words alpha z) :
    PublicStatementLookup (gateWire rows (externalYields triple conversion blake)) words := by
  exact public_statement_lookup_of_global_gate rows gates
    (externalUses words otherUses) (externalYields triple conversion blake)
    (externalYields triple conversion blake) words alpha z
    (boundary_of_trace rows gates otherUses triple conversion blake words boundary)
    (closure_of_claimed_trace rows otherUses triple conversion blake words
      claims alpha z claimed acceptedSum good)

theorem matched_gate_air_of_claimed_trace
    (rows : List Row) (gates : List Gate)
    (otherUses triple conversion blake : List Event)
    (words : Fin 8 → Nat) (claims : List GateSecure)
    (alpha z : GateSecure)
    (boundary : TraceBoundary rows gates otherUses triple conversion blake words)
    (claimed : ClaimedTrace rows otherUses triple conversion blake claims alpha z)
    (acceptedSum : nativeGateClosure
      (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i)))
      claims alpha z = 0)
    (good : GoodTraceChallenges rows otherUses triple conversion blake words alpha z) :
    AirRows (gateWire rows (externalYields triple conversion blake)) gates := by
  exact matched_gate_air_of_global_gate rows gates
    (externalUses words otherUses) (externalYields triple conversion blake)
    (externalYields triple conversion blake) words alpha z
    (boundary_of_trace rows gates otherUses triple conversion blake words boundary)
    (closure_of_claimed_trace rows otherUses triple conversion blake words
      claims alpha z claimed acceptedSum good)

end S31.Functional.Correspondence.ControlGadgetClaimTrace
