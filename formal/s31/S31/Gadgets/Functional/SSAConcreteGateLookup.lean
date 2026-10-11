import S31.Gadgets.Functional.SSAConcreteGateSchedule
import S31.Gadgets.Air.GateLookup

/-!
One exact Gate-lookup join for the concrete four-lane SSA row schedule.

`NativeRow.matches` normally assumes that both operand values equal the
previously produced SSA wire values. Here those equalities follow from exact
Gate multiset balance, unique values per producer address, and membership of
the row reads and expected producers. The remaining shape and local AIR
premises must still be established for every emitted native row. Production
LogUp supplies only a challenge-based check of balance, and proving its
reduction to this exact premise is a separate obligation.
-/

namespace S31.Functional.SSAConcreteGateLookup

open S31.Functional.SSACertificate
open S31.Functional.SSAConcreteGateSchedule
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Packed

private theorem pack_injective {a b : Lanes}
    (h : packM31 a = packM31 b) : a = b := by
  funext i
  apply S31.Field.toZMod_injective
  simpa only [coord_packM31] using congrArg (fun q => coord q i) h

/-- Exact Gate balance authenticates both packed operand reads against
previously produced SSA wire values. No equality of the row's operand values
is assumed. The producer-membership hypotheses identify the source-owned
address/value pairs in the global Gate yield multiset. -/
theorem row_matches_of_exact_gate
    (addresses : List Nat) (values : List Lanes)
    (instruction : Instruction) (row : NativeRow)
    (reads produced : List Event)
    (hshape : addresses.length = values.length ∧
      instruction.id = values.length ∧
      addresses[instruction.lhs]? = some row.in0Address ∧
      addresses[instruction.rhs]? = some row.in1Address ∧
      row.outAddress ∉ addresses ∧
      row.multiply = instruction.multiply)
    (left right : Lanes)
    (hleft : values[instruction.lhs]? = some left)
    (hright : values[instruction.rhs]? = some right)
    (hread0 : (row.in0Address, packM31 row.in0) ∈ reads)
    (hread1 : (row.in1Address, packM31 row.in1) ∈ reads)
    (hproducer0 : (row.in0Address, packM31 left) ∈ produced)
    (hproducer1 : (row.in1Address, packM31 right) ∈ produced)
    (hbalance : reads.Perm produced)
    (hunique : uniqueProduced produced)
    (hair : accepts (encode (s31Op row.multiply))
      (packM31 row.in0) (packM31 row.in1) (packM31 row.output)) :
    row.matches addresses values instruction := by
  have hpacked0 := balanced_read_matches reads produced hbalance hunique
    row.in0Address (packM31 row.in0) (packM31 left) hread0 hproducer0
  have hpacked1 := balanced_read_matches reads produced hbalance hunique
    row.in1Address (packM31 row.in1) (packM31 right) hread1 hproducer1
  have hvalue0 : row.in0 = left := pack_injective hpacked0
  have hvalue1 : row.in1 = right := pack_injective hpacked1
  obtain ⟨hlen, hid, haddr0, haddr1, hfresh, hop⟩ := hshape
  refine ⟨hlen, hid, haddr0, haddr1, hfresh, hop, ?_, ?_, hair⟩
  · simpa [hvalue0] using hleft
  · simpa [hvalue1] using hright

end S31.Functional.SSAConcreteGateLookup
