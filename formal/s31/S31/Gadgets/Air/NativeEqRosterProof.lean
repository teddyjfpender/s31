import S31.Gadgets.Air.NativeGateRoster
import S31.Gadgets.Air.EqGateInteraction

namespace S31.Gadgets.Air.NativeEqRosterProof
open S31.Gadgets.Air.NativeGateRoster
open S31.Gadgets.Air.EqRows
open S31.Gadgets.Air.EqGateInteraction
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.LogUpInteraction
open S31.Gadgets.Packed

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- Eq commits one four-limb value and reads it at both preprocessed input
addresses. The generated roster comes from `components.eq.lookups`. -/
def eqTraceLimb (row : EqRow) : Nat → F
  | 0 => row.value.a | 1 => row.value.b
  | 2 => row.value.c | 3 => row.value.d
  | _ => 0

def eqTraceQuad (row : EqRow) (start : Nat) : Quad :=
  ⟨eqTraceLimb row start, eqTraceLimb row (start + 1),
    eqTraceLimb row (start + 2), eqTraceLimb row (start + 3)⟩

def slotAddress (row : EqRow) : AddressSlot → Nat
  | .in0 => row.leftAddress
  | .in1 => row.rightAddress
  | .dst => 0

def slotEvent (row : EqRow) (slot : LookupSlot) : Event :=
  (slotAddress row slot.address, eqTraceQuad row slot.limbStart)

def nativeEqUses (row : EqRow) : List Event :=
  eqRoster.map (slotEvent row)

theorem eq_trace_quad_value (row : EqRow) :
    eqTraceQuad row 0 = row.value := by
  apply Quad.ext <;> rfl

theorem native_eq_uses_eq (row : EqRow) :
    nativeEqUses row = row.uses := by
  simp [nativeEqUses, eqRoster, slotEvent, slotAddress,
    EqRow.uses, eq_trace_quad_value]

theorem native_eq_pair_contribution_eq (row : EqRow)
    (alpha z : GateSecure) :
    pairValue (eqPair row alpha z) =
      productionReciprocalSum (nativeEqUses row) alpha z := by
  rw [native_eq_uses_eq]
  exact eq_pair_value_eq_event_sum row alpha z

end S31.Gadgets.Air.NativeEqRosterProof
