import Mathlib.Tactic

/-!
An ideal multiset model for an arbitrary list of circuit-to-chip boundaries.
Each boundary carries four input and four output Gate addresses and two chip
endpoint tuples. A future multi-chip implementation must give every call a
distinct tag. This file proves what exact lookup balance would authenticate;
it deliberately assumes that balance, producer uniqueness, and matching
expected events. The Fiat–Shamir/LogUp step from actual AIR rows to exact
balance is a separate probabilistic obligation.
-/

namespace S31.Gadgets.Air.GenericChipBoundary

variable {F : Type*}

abbrev Lanes (F : Type*) := Fin 4 → F
abbrev GateEvent (F : Type*) := Nat × F
abbrev ChipKey := Nat × Bool
abbrev ChipEvent (F : Type*) := ChipKey × Lanes F

structure Boundary (F : Type*) where
  call : Nat
  inputAddress : Fin 4 → Nat
  outputAddress : Fin 4 → Nat
  input : Lanes F
  output : Lanes F

def gateEvents (b : Boundary F) : List (GateEvent F) :=
  List.ofFn (fun lane : Fin 4 => (b.inputAddress lane, b.input lane)) ++
  List.ofFn (fun lane : Fin 4 => (b.outputAddress lane, b.output lane))

def chipEvents (b : Boundary F) : List (ChipEvent F) :=
  [((b.call, false), b.input), ((b.call, true), b.output)]

def allGateEvents (boundaries : List (Boundary F)) : List (GateEvent F) :=
  boundaries.flatMap gateEvents

def allChipEvents (boundaries : List (Boundary F)) : List (ChipEvent F) :=
  boundaries.flatMap chipEvents

def uniqueGateProducer (events : List (GateEvent F)) : Prop :=
  ∀ address left right,
    (address, left) ∈ events → (address, right) ∈ events → left = right

def uniqueChipProducer (events : List (ChipEvent F)) : Prop :=
  ∀ key left right,
    (key, left) ∈ events → (key, right) ∈ events → left = right

theorem gate_input_member (boundaries : List (Boundary F))
    (b : Boundary F) (hb : b ∈ boundaries) (lane : Fin 4) :
    (b.inputAddress lane, b.input lane) ∈ allGateEvents boundaries := by
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  exact List.mem_append_left _ (List.mem_ofFn.mpr ⟨lane, rfl⟩)

theorem gate_output_member (boundaries : List (Boundary F))
    (b : Boundary F) (hb : b ∈ boundaries) (lane : Fin 4) :
    (b.outputAddress lane, b.output lane) ∈ allGateEvents boundaries := by
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  exact List.mem_append_right _ (List.mem_ofFn.mpr ⟨lane, rfl⟩)

theorem chip_input_member (boundaries : List (Boundary F))
    (b : Boundary F) (hb : b ∈ boundaries) :
    ((b.call, false), b.input) ∈ allChipEvents boundaries := by
  apply List.mem_flatMap.mpr
  exact ⟨b, hb, by simp [chipEvents]⟩

theorem chip_output_member (boundaries : List (Boundary F))
    (b : Boundary F) (hb : b ∈ boundaries) :
    ((b.call, true), b.output) ∈ allChipEvents boundaries := by
  apply List.mem_flatMap.mpr
  exact ⟨b, hb, by simp [chipEvents]⟩

/-- If the bridge's Gate lookup events balance the circuit's uniquely
produced events, each bridge endpoint equals the circuit wire at its address.
This holds for any number of boundary calls and any field/value type. -/
theorem gate_boundary_authenticated
    (boundaries : List (Boundary F)) (produced : List (GateEvent F))
    (hbalance : (allGateEvents boundaries).Perm produced)
    (hunique : uniqueGateProducer produced)
    (b : Boundary F) (hb : b ∈ boundaries) (lane : Fin 4)
    (expectedInput expectedOutput : F)
    (hin : (b.inputAddress lane, expectedInput) ∈ produced)
    (hout : (b.outputAddress lane, expectedOutput) ∈ produced) :
    b.input lane = expectedInput ∧ b.output lane = expectedOutput := by
  constructor
  · exact hunique _ _ _
      (hbalance.mem_iff.mp (gate_input_member boundaries b hb lane)) hin
  · exact hunique _ _ _
      (hbalance.mem_iff.mp (gate_output_member boundaries b hb lane)) hout

/-- If the bridge's chip endpoint events balance uniquely produced chip
events, both four-lane tuples are the endpoints of that tagged chip call. -/
theorem chip_boundary_authenticated
    (boundaries : List (Boundary F)) (produced : List (ChipEvent F))
    (hbalance : (allChipEvents boundaries).Perm produced)
    (hunique : uniqueChipProducer produced)
    (b : Boundary F) (hb : b ∈ boundaries)
    (expectedInput expectedOutput : Lanes F)
    (hin : ((b.call, false), expectedInput) ∈ produced)
    (hout : ((b.call, true), expectedOutput) ∈ produced) :
    b.input = expectedInput ∧ b.output = expectedOutput := by
  constructor
  · exact hunique _ _ _
      (hbalance.mem_iff.mp (chip_input_member boundaries b hb)) hin
  · exact hunique _ _ _
      (hbalance.mem_iff.mp (chip_output_member boundaries b hb)) hout

/-- The two independent lookup relations meet at the same bridge values.
Given the explicit producer and exact-balance premises, the circuit's four
input/output wires equal the corresponding chip endpoint tuples. -/
theorem circuit_chip_join
    (boundaries : List (Boundary F))
    (gateProduced : List (GateEvent F))
    (chipProduced : List (ChipEvent F))
    (hgateBalance : (allGateEvents boundaries).Perm gateProduced)
    (hchipBalance : (allChipEvents boundaries).Perm chipProduced)
    (hgateUnique : uniqueGateProducer gateProduced)
    (hchipUnique : uniqueChipProducer chipProduced)
    (b : Boundary F) (hb : b ∈ boundaries)
    (circuitInput circuitOutput chipInput chipOutput : Lanes F)
    (hgateInput : ∀ lane, (b.inputAddress lane, circuitInput lane) ∈ gateProduced)
    (hgateOutput : ∀ lane, (b.outputAddress lane, circuitOutput lane) ∈ gateProduced)
    (hchipInput : ((b.call, false), chipInput) ∈ chipProduced)
    (hchipOutput : ((b.call, true), chipOutput) ∈ chipProduced) :
    circuitInput = chipInput ∧ circuitOutput = chipOutput := by
  obtain ⟨hinput, houtput⟩ := chip_boundary_authenticated boundaries
    chipProduced hchipBalance hchipUnique b hb chipInput chipOutput
    hchipInput hchipOutput
  constructor <;> funext lane
  · exact (gate_boundary_authenticated boundaries gateProduced hgateBalance
      hgateUnique b hb lane (circuitInput lane) (circuitOutput lane)
      (hgateInput lane) (hgateOutput lane)).1.symm.trans
      (congrFun hinput lane)
  · exact (gate_boundary_authenticated boundaries gateProduced hgateBalance
      hgateUnique b hb lane (circuitInput lane) (circuitOutput lane)
      (hgateInput lane) (hgateOutput lane)).2.symm.trans
      (congrFun houtput lane)

/-- Exact lookup balance also forces the current sixteen bridge rows to carry
one common endpoint value, although the AIR has no row-to-row equality
constraint for that column. Deriving this exact permutation from the weighted
LogUp identity, including characteristic and challenge bounds, remains a
separate obligation. -/
theorem averaged_bridge_rows_constant {α : Type*}
    (rows : Fin 16 → α) (expected : α)
    (hbalance : (List.ofFn rows).Perm (List.replicate 16 expected)) :
    ∀ row : Fin 16, rows row = expected := by
  intro row
  have hmem : rows row ∈ List.ofFn rows :=
    List.mem_ofFn.mpr ⟨row, rfl⟩
  exact List.eq_of_mem_replicate (hbalance.mem_iff.mp hmem)

end S31.Gadgets.Air.GenericChipBoundary
