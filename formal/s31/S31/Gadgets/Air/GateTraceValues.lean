import S31.Gadgets.Air.GateWireMap

/-!
An address-indexed model of the native `writeTrace` arithmetic gather. For
ordinary QM31-operation rows, the production writer reads all three operand
values from the same finalized value table at preprocessed addresses. This
module proves the resulting row yield events carry that table's value. The
correspondence of this model to the Zig writer is source-bound and reviewed,
not itself a formal proof of Zig execution.
-/

namespace S31.Gadgets.Air.GateTraceValues

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup

/-- Fill the three committed operand columns from one address-indexed value
table, leaving preprocessed addresses, flags and multiplicity unchanged. -/
def gather (values : Nat → Quad) (row : Row) : Row :=
  { row with
    in0 := values row.in0Address
    in1 := values row.in1Address
    output := values row.outAddress }

theorem gather_addresses (values : Nat → Quad) (row : Row) :
    (gather values row).in0Address = row.in0Address ∧
    (gather values row).in1Address = row.in1Address ∧
    (gather values row).outAddress = row.outAddress ∧
    (gather values row).flags = row.flags ∧
    (gather values row).multiplicity = row.multiplicity := by
  simp [gather]

theorem gathered_row_output (values : Nat → Quad)
    (templates : List Row) (row : Row)
    (hrow : row ∈ templates.map (gather values)) :
    row.output = values row.outAddress := by
  obtain ⟨template, _, heq⟩ := List.mem_map.mp hrow
  rw [← heq]
  rfl

/-- Every arithmetic yield from gathered rows has the value at its declared
address. The same property for external yields remains an explicit premise,
because those events are emitted by other components. -/
theorem gathered_yields_match_table
    (values : Nat → Quad) (templates : List Row)
    (externalYields : List Event)
    (hexternal : ∀ event ∈ externalYields,
      event.2 = values event.1)
    (address : Nat) (value : Quad)
    (hmem : (address, value) ∈
      allYields (templates.map (gather values)) externalYields) :
    value = values address := by
  rcases List.mem_append.mp hmem with hrow | hevent
  · obtain ⟨row, hrowmem, hyield⟩ := List.mem_flatMap.mp hrow
    have heq : (address, value) = (row.outAddress, row.output) :=
      List.eq_of_mem_replicate hyield
    have haddress := congrArg Prod.fst heq
    have hvalue := congrArg Prod.snd heq
    exact hvalue.trans ((gathered_row_output values templates row hrowmem).trans
      (congrArg values haddress.symm))
  · exact hexternal (address, value) hevent

end S31.Gadgets.Air.GateTraceValues
