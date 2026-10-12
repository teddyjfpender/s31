/-! Generated from circuit/witness/components.zig by scripts/s31_formal.py. -/
namespace S31.Gadgets.Air.NativeGateRoster

inductive AddressSlot where
  | in0 | in1 | dst
deriving DecidableEq, Repr

structure LookupSlot where
  isYield : Bool
  address : AddressSlot
  limbStart : Nat
deriving DecidableEq, Repr

def qm31OpsRoster : List LookupSlot := [
  ⟨false, .in0, 0⟩,
  ⟨false, .in1, 4⟩,
  ⟨true, .dst, 8⟩
]

def eqRoster : List LookupSlot := [
  ⟨false, .in0, 0⟩,
  ⟨false, .in1, 0⟩
]

end S31.Gadgets.Air.NativeGateRoster
