import S31.Gadgets.Air.GateLookup

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

end S31.Gadgets.Air.GateWireMap
