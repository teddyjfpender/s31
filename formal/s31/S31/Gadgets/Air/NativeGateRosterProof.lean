import S31.Gadgets.Air.NativeGateRoster
import S31.Gadgets.Air.GateContributions

namespace S31.Gadgets.Air.NativeGateRosterProof
open S31.Gadgets.Air.NativeGateRoster
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge

abbrev Event := S31.Gadgets.Air.GateLookup.Event

/-- The committed base-trace limb order used by `qm31_ops.row`. The source
extractor checks its three four-limb assignments before generating the roster. -/
def traceLimb (row : Row) : Nat → F
  | 0 => row.in0.a | 1 => row.in0.b
  | 2 => row.in0.c | 3 => row.in0.d
  | 4 => row.in1.a | 5 => row.in1.b
  | 6 => row.in1.c | 7 => row.in1.d
  | 8 => row.output.a | 9 => row.output.b
  | 10 => row.output.c | 11 => row.output.d
  | _ => 0

def traceQuad (row : Row) (start : Nat) : Quad :=
  ⟨traceLimb row start, traceLimb row (start + 1),
    traceLimb row (start + 2), traceLimb row (start + 3)⟩

def slotAddress (row : Row) : AddressSlot → Nat
  | .in0 => row.in0Address
  | .in1 => row.in1Address
  | .dst => row.outAddress

def slotEvent (row : Row) (slot : LookupSlot) : Event :=
  (slotAddress row slot.address, traceQuad row slot.limbStart)

def nativeUseEvents (row : Row) : List Event :=
  (qm31OpsRoster.filter fun slot => !slot.isYield).map (slotEvent row)

def nativeYieldEvents (row : Row) : List Event :=
  (qm31OpsRoster.filter fun slot => slot.isYield).flatMap fun slot =>
    List.replicate row.multiplicity (slotEvent row slot)

theorem trace_quad_in0 (row : Row) : traceQuad row 0 = row.in0 := by
  apply Quad.ext <;> rfl

theorem trace_quad_in1 (row : Row) : traceQuad row 4 = row.in1 := by
  apply Quad.ext <;> rfl

theorem trace_quad_output (row : Row) : traceQuad row 8 = row.output := by
  apply Quad.ext <;> rfl

/-- The three source-extracted native lookup slots have precisely the Gate
event order and output multiplicity used by the Lean row model. -/
theorem native_use_events_eq (row : Row) :
    nativeUseEvents row = row.uses := by
  simp [nativeUseEvents, qm31OpsRoster, slotEvent, slotAddress,
    Row.uses, trace_quad_in0, trace_quad_in1]

theorem native_yield_events_eq (row : Row) :
    nativeYieldEvents row = row.yields := by
  simp [nativeYieldEvents, qm31OpsRoster, slotEvent, slotAddress,
    Row.yields, trace_quad_output]

def nativeRowContribution (row : Row) (alpha z : GateSecure) : GateSecure :=
  productionReciprocalSum (nativeUseEvents row) alpha z -
    productionReciprocalSum (nativeYieldEvents row) alpha z

theorem native_row_contribution_eq (row : Row) (alpha z : GateSecure) :
    nativeRowContribution row alpha z = rowContribution row alpha z := by
  rw [nativeRowContribution, native_use_events_eq, native_yield_events_eq]
  exact (rowContribution_eq_event_sums row alpha z).symm

end S31.Gadgets.Air.NativeGateRosterProof
