import S31.Gadgets.Air.GateProducerCheck

/-!
An exact Gate multiset balance and unique produced values give every address
a coherent packed value. This is the bridge from independently witnessed AIR
row operands to a circuit-style shared wire map. The statements are about
exact balance; LogUp challenge and trace commitments have separate proofs and
remaining source-correspondence obligations.
-/

namespace S31.Gadgets.Air.GateWireMap

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.Qm31Ops

noncomputable def producedWire (produced : List Event) (address : Nat) : Quad :=
  by
    classical
    exact if h : ∃ value, (address, value) ∈ produced then Classical.choose h else base 0

theorem producedWire_eq (produced : List Event)
    (hunique : uniqueProduced produced) (address : Nat) (value : Quad)
    (hvalue : (address, value) ∈ produced) :
    producedWire produced address = value := by
  classical
  unfold producedWire
  split_ifs with h
  · exact hunique address (Classical.choose h) value
      (Classical.choose_spec h) hvalue
  · exact False.elim (h ⟨value, hvalue⟩)

/-- Every operand read and every yielded output of a local row equals the
single value selected for its address by the global Gate multiset. -/
theorem row_values_match_wire (rows : List Row)
    (externalUses externalYields : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (row : Row) (hrow : row ∈ rows) (hm : 0 < row.multiplicity) :
    row.in0 = producedWire (allYields rows externalYields) row.in0Address ∧
    row.in1 = producedWire (allYields rows externalYields) row.in1Address ∧
    row.output = producedWire (allYields rows externalYields) row.outAddress := by
  have hreads := row_input_use rows externalUses row hrow
  have h0 := producedWire_eq (allYields rows externalYields) hunique
    row.in0Address row.in0 (hbalance.mem_iff.mp hreads.1)
  have h1 := producedWire_eq (allYields rows externalYields) hunique
    row.in1Address row.in1 (hbalance.mem_iff.mp hreads.2)
  have hout := producedWire_eq (allYields rows externalYields) hunique
    row.outAddress row.output
    (row_output_yield rows externalYields row hrow hm)
  exact ⟨h0.symm, h1.symm, hout.symm⟩

/-- Local AIR acceptance can be read as a deterministic circuit gate on the
coherent address map. This applies to any row in any balanced Gate list whose
output is yielded at least once. -/
theorem row_accepts_on_wire (rows : List Row)
    (externalUses externalYields : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (row : Row) (hrow : row ∈ rows) (hm : 0 < row.multiplicity)
    (hair : accepts row.flags row.in0 row.in1 row.output) :
    accepts row.flags
      (producedWire (allYields rows externalYields) row.in0Address)
      (producedWire (allYields rows externalYields) row.in1Address)
      (producedWire (allYields rows externalYields) row.outAddress) := by
  obtain ⟨h0, h1, hout⟩ :=
    row_values_match_wire rows externalUses externalYields hbalance hunique row hrow hm
  simpa [← h0, ← h1, ← hout] using hair

/-- Scratch addresses may have several different producers. Declared wires
only need uniqueness below their address bound. -/
def uniqueProducedBelow (produced : List Event) (bound : Nat) : Prop :=
  ∀ address left right, address < bound →
    (address, left) ∈ produced → (address, right) ∈ produced → left = right

theorem uniqueProducedBelow_of_unique (produced : List Event) (bound : Nat)
    (hunique : uniqueProduced produced) :
    uniqueProducedBelow produced bound := by
  intro address left right _ hleft hright
  exact hunique address left right hleft hright

/-- The producer scan can establish declared-address uniqueness even when
the full event list contains scratch duplicates. Coverage only asks that
every low-address event appear in the checked declared list; repeated copies
of one event remain allowed. -/
theorem uniqueProducedBelow_of_checked_declared
    (bound : Nat) (declared produced : List Event)
    (result : Finset Nat)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan bound ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value, address < bound →
      (address, value) ∈ produced → (address, value) ∈ declared) :
    uniqueProducedBelow produced bound := by
  have hunique :=
    (S31.Gadgets.Air.GateProducerCheck.checked_produced_unique
      bound declared result hscan).1
  intro address left right haddress hleft hright
  exact hunique address left right
    (hcovered address left haddress hleft)
    (hcovered address right haddress hright)

/-- The checked list may cover more addresses than the circuit path needs.
Only events below `target` need a source-to-trace correspondence when the
claim uses only those addresses. -/
theorem uniqueProducedBelow_of_checked_declared_prefix
    (bound target : Nat) (htarget : target ≤ bound)
    (declared produced : List Event) (result : Finset Nat)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan bound ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value, address < target →
      (address, value) ∈ produced → (address, value) ∈ declared) :
    uniqueProducedBelow produced target := by
  have hunique :=
    (S31.Gadgets.Air.GateProducerCheck.checked_produced_unique
      bound declared result hscan).1
  intro address left right haddress hleft hright
  exact hunique address left right
    (hcovered address left haddress hleft)
    (hcovered address right haddress hright)

theorem producedWire_eq_below (produced : List Event) (bound : Nat)
    (hunique : uniqueProducedBelow produced bound)
    (address : Nat) (haddress : address < bound)
    (value : Quad) (hvalue : (address, value) ∈ produced) :
    producedWire produced address = value := by
  classical
  unfold producedWire
  split_ifs with h
  · exact hunique address (Classical.choose h) value haddress
      (Classical.choose_spec h) hvalue
  · exact False.elim (h ⟨value, hvalue⟩)

theorem row_values_match_wire_below (rows : List Row)
    (externalUses externalYields : List Event)
    (bound : Nat)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProducedBelow (allYields rows externalYields) bound)
    (row : Row) (hrow : row ∈ rows) (hm : 0 < row.multiplicity)
    (h0 : row.in0Address < bound) (h1 : row.in1Address < bound)
    (hout : row.outAddress < bound) :
    row.in0 = producedWire (allYields rows externalYields) row.in0Address ∧
    row.in1 = producedWire (allYields rows externalYields) row.in1Address ∧
    row.output = producedWire (allYields rows externalYields) row.outAddress := by
  have hreads := row_input_use rows externalUses row hrow
  have hv0 := producedWire_eq_below (allYields rows externalYields) bound
    hunique row.in0Address h0 row.in0 (hbalance.mem_iff.mp hreads.1)
  have hv1 := producedWire_eq_below (allYields rows externalYields) bound
    hunique row.in1Address h1 row.in1 (hbalance.mem_iff.mp hreads.2)
  have hvout := producedWire_eq_below (allYields rows externalYields) bound
    hunique row.outAddress hout row.output
    (row_output_yield rows externalYields row hrow hm)
  exact ⟨hv0.symm, hv1.symm, hvout.symm⟩

theorem row_accepts_on_wire_below (rows : List Row)
    (externalUses externalYields : List Event)
    (bound : Nat)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProducedBelow (allYields rows externalYields) bound)
    (row : Row) (hrow : row ∈ rows) (hm : 0 < row.multiplicity)
    (h0 : row.in0Address < bound) (h1 : row.in1Address < bound)
    (hout : row.outAddress < bound)
    (hair : accepts row.flags row.in0 row.in1 row.output) :
    accepts row.flags
      (producedWire (allYields rows externalYields) row.in0Address)
      (producedWire (allYields rows externalYields) row.in1Address)
      (producedWire (allYields rows externalYields) row.outAddress) := by
  obtain ⟨hv0, hv1, hvout⟩ :=
    row_values_match_wire_below rows externalUses externalYields bound
      hbalance hunique row hrow hm h0 h1 hout
  simpa [← hv0, ← hv1, ← hvout] using hair

/-- A concrete scratch counterexample: address 40 has two values, while all
declared addresses below 35 still have one value. -/
def scratchExample : List Event :=
  [(7, base 5), (40, base 3), (40, base 4)]

theorem scratchExample_unique_below :
    uniqueProducedBelow scratchExample 35 := by
  intro address left right haddress hleft hright
  simp [scratchExample] at hleft hright
  rcases hleft with hleft | hleft | hleft <;>
    rcases hright with hright | hright | hright <;>
    simp_all

theorem scratchExample_not_globally_unique :
    ¬ uniqueProduced scratchExample := by
  intro h
  have heq := h 40 (base 3) (base 4)
    (by simp [scratchExample]) (by simp [scratchExample])
  exact (by decide : (base 3 : Quad) ≠ base 4) heq

end S31.Gadgets.Air.GateWireMap
