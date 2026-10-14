import S31.Gadgets.Functional.Correspondence.ControlGadgetStatementPins
import S31.Gadgets.Air.GateContributions
import S31.Gadgets.Air.GateProducerRoster
import S31.Gadgets.Air.TaggedPairConditionalCorrespondence

/-!
Conditional global Gate join for the bounded control program. The native
verifier's eight public output events become addressed wire equalities once
the installed Gate reciprocal equation closes outside its exceptional
challenge sets and the producer roster owns each address uniquely. Local
Gate AIR for the matched control rows is then derived from accepted physical
rows rather than supplied as an unrelated predicate. Authentication of those
physical rows and interaction claims by an arbitrary accepted PCS/FRI proof
remains a separate premise.
-/

namespace S31.Functional.Correspondence.ControlGadgetGlobalGateJoin

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.GateProducerRoster
open S31.Functional.Correspondence.ControlGadgetAir
open S31.Functional.Correspondence.ControlGadgetPublicPins
open S31.Functional.Correspondence.ControlGadgetConversionAir
open S31.Functional.Correspondence.ControlGadgetStatementPins

abbrev Event := S31.Gadgets.Air.GateLookup.Event

def publicUses (words : Fin 8 → Nat) : List Event :=
  List.ofFn (fun i : Fin 8 => (claimAddress i, encodeClaimWord (words i)))

def publicUsesWithU (words : Fin 8 → Nat) : List Event :=
  publicUses words ++ [(2, ⟨0, 0, 1, 0⟩)]

/-- The exact eight-then-`u` event list of the modeled native verifier,
including the seventh padding coordinate of the joint lookup tuple. -/
theorem public_uses_native_events (words : Fin 8 → Nat) :
    (publicUsesWithU words).map
      S31.Gadgets.Air.TaggedPairConditionalCorrespondence.embedGateEvent =
    S31.Gadgets.Air.TaggedPairSourceCorrespondence.publicOutputYields
      (List.ofFn (fun i : Fin 8 => encodeClaimWord (words i))) := by
  rfl

noncomputable def gateWire (rows : List Row) (externalYields : List Event) : Wire :=
  producedWire (allYields rows externalYields)

/-- Source-level facts about one fixed Gate event roster. `publicOrder`
places the verifier's eight claimed events and fixed `u` event at the start of external uses;
`positiveOwner` ties each selected semantic Gate to one physical row with
positive output multiplicity and locally accepted arithmetic residuals. -/
structure GateBoundary (rows : List Row) (gates : List Gate)
    (externalUses externalYields externalProducers : List Event)
    (words : Fin 8 → Nat) : Prop where
  canonicalWords : ∀ i, words i < 2147483647
  publicOrder : ∃ rest, externalUses = publicUsesWithU words ++ rest
  producerRoster :
    ((activeRows rows).map Row.outAddress ++ externalProducers.map Prod.fst).Nodup
  externalProducerCoverage : ∀ event ∈ externalYields, event ∈ externalProducers
  positiveOwner : ∀ gate ∈ gates, ∃ row ∈ rows,
    row.in0Address = gate.lhs ∧ row.in1Address = gate.rhs ∧
      row.outAddress = gate.out ∧ row.flags = S31.Gadgets.Air.Qm31Ops.encode gate.op ∧
      0 < row.multiplicity ∧
      S31.Gadgets.Air.Qm31Ops.accepts row.flags row.in0 row.in1 row.output

/-- This is the global LogUp closure and challenge-separation obligation;
the theorem does not manufacture it from native verifier acceptance. -/
structure GoodGateClosure (rows : List Row)
    (externalUses externalYields : List Event) (alpha z : GateSecure) : Prop where
  canonicalAddresses : ∀ event ∈
    allUses rows externalUses ++ allYields rows externalYields,
    event.1 < 2147483647
  useCounts : ∀ event ∈
    allUses rows externalUses ++ allYields rows externalYields,
    (allUses rows externalUses).count event < 2147483647
  yieldCounts : ∀ event ∈
    allUses rows externalUses ++ allYields rows externalYields,
    (allYields rows externalYields).count event < 2147483647
  goodAlpha : alpha ∉ badAlpha
    (allUses rows externalUses ++ allYields rows externalYields)
  goodZ : z ∉ badZ
    (allUses rows externalUses) (allYields rows externalYields) alpha
  closed :
    (rows.map fun row => rowContribution row alpha z).sum +
      productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z = 0

theorem exact_balance (rows : List Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (closure : GoodGateClosure rows externalUses externalYields alpha z) :
    balanced rows externalUses externalYields := by
  exact closed_gate_contribution_balanced_of_counts
    rows externalUses externalYields alpha z
    closure.canonicalAddresses closure.useCounts closure.yieldCounts
    closure.goodAlpha closure.goodZ closure.closed

/-- The eight public lookup events are now equal to their uniquely owned
Gate wires, including the three zero padding words supplied by the ABI. -/
theorem public_statement_lookup_of_global_gate
    (rows : List Row) (gates : List Gate)
    (externalUses externalYields externalProducers : List Event)
    (words : Fin 8 → Nat)
    (alpha z : GateSecure)
    (boundary : GateBoundary rows gates externalUses externalYields
      externalProducers words)
    (closure : GoodGateClosure rows externalUses externalYields alpha z) :
    PublicStatementLookup (gateWire rows externalYields) words := by
  let produced := allYields rows externalYields
  have hbalance := exact_balance rows externalUses externalYields alpha z closure
  have hunique := unique_yields_of_nodup_roster rows externalYields
    externalProducers boundary.producerRoster boundary.externalProducerCoverage
  refine ⟨boundary.canonicalWords, ?_⟩
  intro i
  obtain ⟨rest, horder⟩ := boundary.publicOrder
  have hpublic : (claimAddress i, encodeClaimWord (words i)) ∈
      publicUses words := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have huse : (claimAddress i, encodeClaimWord (words i)) ∈
      allUses rows externalUses := by
    apply List.mem_append_right
    rw [horder]
    exact List.mem_append_left _ (List.mem_append_left _ hpublic)
  have hyield := hbalance.mem_iff.mp huse
  exact producedWire_eq produced hunique _ _ hyield

/-- Every source-matched Gate row's local AIR residuals follow from the
installed physical row residuals, exact balance, and one-producer roster. -/
theorem matched_gate_air_of_global_gate
    (rows : List Row) (gates : List Gate)
    (externalUses externalYields externalProducers : List Event)
    (words : Fin 8 → Nat)
    (alpha z : GateSecure)
    (boundary : GateBoundary rows gates externalUses externalYields
      externalProducers words)
    (closure : GoodGateClosure rows externalUses externalYields alpha z) :
    AirRows (gateWire rows externalYields) gates := by
  have hbalance := exact_balance rows externalUses externalYields alpha z closure
  have hunique := unique_yields_of_nodup_roster rows externalYields
    externalProducers boundary.producerRoster boundary.externalProducerCoverage
  intro gate hgate residual hresidual
  obtain ⟨row, hrow, h0, h1, hout, hflags, hpositive, hair⟩ :=
    boundary.positiveOwner gate hgate
  have hwire := row_accepts_on_wire rows externalUses externalYields
    hbalance hunique row hrow hpositive hair
  have hgateAir : S31.Gadgets.Air.Qm31Ops.accepts
      (S31.Gadgets.Air.Qm31Ops.encode gate.op)
      (gateWire rows externalYields gate.lhs)
      (gateWire rows externalYields gate.rhs)
      (gateWire rows externalYields gate.out) := by
    simpa [gateWire, h0, h1, hout, hflags] using hwire
  have hnative : ∀ r ∈ S31.Gadgets.Air.NativeQm31Air.residuals
      (S31.Gadgets.Air.Qm31Ops.encode gate.op)
      (gateWire rows externalYields gate.lhs)
      (gateWire rows externalYields gate.rhs)
      (gateWire rows externalYields gate.out), r = 0 := by
    rw [S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq]
    exact hgateAir
  exact hnative residual hresidual

/-- A claim different from an independently identified positive Gate
producer at the same address cannot satisfy a good global closure. This
includes a changed word or a reordered pair of unequal words. -/
theorem forged_public_word_rejected
    (rows : List Row) (gates : List Gate)
    (externalUses externalYields externalProducers : List Event)
    (words : Fin 8 → Nat) (alpha z : GateSecure)
    (boundary : GateBoundary rows gates externalUses externalYields
      externalProducers words)
    (i : Fin 8) (actual : Quad)
    (hactual : (claimAddress i, actual) ∈ allYields rows externalYields)
    (hforged : encodeClaimWord (words i) ≠ actual) :
    ¬ GoodGateClosure rows externalUses externalYields alpha z := by
  intro closure
  have hstatement := public_statement_lookup_of_global_gate rows gates
    externalUses externalYields externalProducers words alpha z boundary closure
  have hunique := unique_yields_of_nodup_roster rows externalYields
    externalProducers boundary.producerRoster boundary.externalProducerCoverage
  have hactualWire := producedWire_eq (allYields rows externalYields)
    hunique (claimAddress i) actual hactual
  exact hforged ((hstatement.output_event i).symm.trans hactualWire)

/-- The concrete control-program result now needs no separately assumed
public event-to-cell equality and no separately assumed generic Gate AIR.
Both follow from a good global Gate equation and source-owned positive rows.
Conversion component row/range closure and constant-wire facts remain
explicit, as do authentication of these rows and the global equation. -/
theorem control_program_public_statement_sound_of_global_gate
    (rows : List Row) (gates : List Gate) (conversions : List ConversionGate)
    (externalUses externalYields externalProducers : List Event)
    (words : Fin 8 → Nat) (alpha zChallenge : GateSecure)
    (boundary : GateBoundary rows gates externalUses externalYields
      externalProducers words)
    (closure : GoodGateClosure rows externalUses externalYields alpha zChallenge)
    (x hint z zp zc zd zx za zb : Nat)
    (falseBranch trueBranch selected sc sl sr : Nat)
    (result ip idiff ia mask inputConverted : Nat)
    (basis masked inverseBasis scalar converted : Fin 4 → Nat)
    (zeroRows : ZeroTestRows (gateWire rows externalYields) gates
      x hint z zp zc zd zx za zb)
    (selectRows : SelectRows (gateWire rows externalYields) gates
      z falseBranch trueBranch sc sl sr selected)
    (inverseRows : InverseRows (gateWire rows externalYields) gates
      selected result ip idiff ia mask)
    (inputRows : InputPublicPinRows (gateWire rows externalYields) gates
      conversions x inputConverted)
    (outputRows : ∀ i : Fin 4,
      OutputLaneRows (gateWire rows externalYields) gates conversions result i
        (basis i) (masked i) (inverseBasis i) (scalar i) (converted i))
    (installed : InstalledConversionRows (gateWire rows externalYields) conversions)
    (hmask : ∀ i : Fin 4,
      coord (gateWire rows externalYields mask) i = 1) :
    let wire := gateWire rows externalYields
    let bit := if (wire x).a = 0 then (1 : F) else 0
    words ⟨0, by decide⟩ = (wire x).a.val ∧
      wire selected = (if bit = 0 then wire falseBranch else wire trueBranch) ∧
      (∀ i : Fin 4,
        words ⟨i.val + 1, by omega⟩ = (coord (wire result) i).val ∧
        coord (if bit = 0 then wire falseBranch else wire trueBranch) i *
          (words ⟨i.val + 1, by omega⟩ : F) = 1) := by
  exact control_program_public_statement_sound
    (gateWire rows externalYields) gates conversions words
    x hint z zp zc zd zx za zb falseBranch trueBranch selected sc sl sr
    result ip idiff ia mask inputConverted basis masked inverseBasis scalar converted
    zeroRows selectRows inverseRows inputRows outputRows
    (matched_gate_air_of_global_gate rows gates externalUses externalYields
      externalProducers words alpha zChallenge boundary closure)
    installed hmask
    (public_statement_lookup_of_global_gate rows gates externalUses externalYields
      externalProducers words alpha zChallenge boundary closure)

end S31.Functional.Correspondence.ControlGadgetGlobalGateJoin
