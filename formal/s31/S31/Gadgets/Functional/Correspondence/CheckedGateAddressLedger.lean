import S31.Gadgets.Functional.Correspondence.AcceptedPublicFixedCells

/-!
An address-only exact Gate ledger for coherent circuit rows. A finite check
on fixed addresses and multiplicities suffices for ideal QM31-valued Gate
balance once all main row values are read from one wire assignment. This is
not LogUp soundness or a proof that native commitments open to these rows.
-/

namespace S31.Functional.Correspondence.CheckedGateAddressLedger

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSAAirColumnCells

/-- Materialize a logical Gate row from a checked fixed cell and a single
address-coherent value assignment. -/
def gateRow (wire : Nat → Quad) (cell : ColumnCell) : Row :=
  { in0Address := cell.in0,
    in1Address := cell.in1,
    outAddress := cell.out,
    flags := S31.Functional.SSANativePolynomialRows.cellFlags cell,
    in0 := wire cell.in0,
    in1 := wire cell.in1,
    output := wire cell.out,
    multiplicity := cell.mults }

def gateRows (cells : List ColumnCell) (wire : Nat → Quad) : List Row :=
  cells.map (gateRow wire)

def wireEvents (wire : Nat → Quad) (addresses : List Nat) : List Event :=
  addresses.map (fun address => (address, wire address))

/-- The multiplicity ledger depends only on fixed addresses/counts and on
the externally specified public feeder/sink addresses. -/
def readAddresses (cells : List ColumnCell) (externalUses : List Nat) : List Nat :=
  cells.flatMap (fun cell => [cell.in0, cell.in1]) ++ externalUses

def producedAddresses (cells : List ColumnCell)
    (externalYields : List Nat) : List Nat :=
  cells.flatMap (fun cell => List.replicate cell.mults cell.out) ++ externalYields

/-- This exact check is executable on the fixed-row certificate. It never
examines secret QM31 witness values. -/
def bounded (cells : List ColumnCell)
    (externalUses externalYields : List Nat) : Prop :=
  cells.length ≤ 512 ∧
  (cells.map ColumnCell.mults).sum ≤ 2048 ∧
  externalUses.length ≤ 1024 ∧ externalYields.length ≤ 1024

instance (cells : List ColumnCell) (externalUses externalYields : List Nat) :
    Decidable (bounded cells externalUses externalYields) := by
  unfold bounded
  infer_instance

/-- The guard is evaluated before expanding multiplicities. At most 2048
row output events and 1024 events from either external side are allocated.
-/
def check (cells : List ColumnCell) (externalUses externalYields : List Nat) :
    Bool :=
  if decide (bounded cells externalUses externalYields) then
    List.isPerm (readAddresses cells externalUses)
      (producedAddresses cells externalYields)
  else false

theorem check_bounded (cells : List ColumnCell)
    (externalUses externalYields : List Nat)
    (hcheck : check cells externalUses externalYields = true) :
    bounded cells externalUses externalYields := by
  by_cases hb : bounded cells externalUses externalYields
  · exact hb
  · simp [check, hb] at hcheck

theorem uses_eq_wire_events (cells : List ColumnCell) (wire : Nat → Quad)
    (externalUses : List Nat) :
    allUses (gateRows cells wire) (wireEvents wire externalUses) =
      wireEvents wire (readAddresses cells externalUses) := by
  simp [allUses, gateRows, readAddresses, wireEvents,
    Row.uses, gateRow, List.flatMap_map, List.map_flatMap]

theorem yields_eq_wire_events (cells : List ColumnCell) (wire : Nat → Quad)
    (externalYields : List Nat) :
    allYields (gateRows cells wire) (wireEvents wire externalYields) =
      wireEvents wire (producedAddresses cells externalYields) := by
  simp [allYields, gateRows, producedAddresses, wireEvents,
    Row.yields, gateRow, List.flatMap_map, List.map_flatMap]

/-- A successful fixed-address count check proves ideal exact Gate balance
for *any* coherent wire assignment. No `balanced` premise or witness values
are supplied to the checker. -/
theorem check_sound (cells : List ColumnCell) (wire : Nat → Quad)
    (externalUses externalYields : List Nat)
    (hcheck : check cells externalUses externalYields = true) :
    balanced (gateRows cells wire)
      (wireEvents wire externalUses)
      (wireEvents wire externalYields) := by
  have haddresses : (readAddresses cells externalUses).Perm
      (producedAddresses cells externalYields) := by
    have hb := check_bounded cells externalUses externalYields hcheck
    exact List.isPerm_iff.mp (by simpa [check, hb] using hcheck)
  unfold balanced
  rw [uses_eq_wire_events, yields_eq_wire_events]
  exact haddresses.map (fun address => (address, wire address))

/-- A small balanced gate: two externally produced operands feed one add,
and its output is consumed at the public boundary. -/
def sampleCell : ColumnCell :=
  { traceRow := 0, addFlag := 1, subFlag := 0, mulFlag := 0,
    pointwiseMulFlag := 0, in0 := 7, in1 := 8, out := 9, mults := 1 }

theorem sample_check : check [sampleCell] [9] [7, 8] = true := by decide

/-- A second claimed output use without a matching read is rejected by the
address-only ledger before any secret values are inspected. -/
theorem sample_extra_multiplicity_rejected :
    check [{ sampleCell with mults := 2 }] [9] [7, 8] = false := by decide

/-- A canonical M31-sized but hostile multiplicity is rejected by the
resource guard before `producedAddresses` can expand it. -/
theorem huge_multiplicity_rejected :
    check [{ sampleCell with mults := 2147483646 }] [9] [7, 8] = false := by
  decide

end S31.Functional.Correspondence.CheckedGateAddressLedger
