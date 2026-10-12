import S31.Gadgets.Air.GateCounter
import S31.Gadgets.Air.GateContributions

namespace S31.Gadgets.Air.GateCounterCircuit
open S31.Gadgets.Air.GateCounter
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge

theorem address_total_append (left right : List (Nat × Nat))
    (address : Nat) :
    addressTotal (left ++ right) address =
      addressTotal left address + addressTotal right address := by
  induction left with
  | nil => simp [addressTotal]
  | cons step rest ih =>
      obtain ⟨stepAddress, increment⟩ := step
      simp [addressTotal, ih, Nat.add_assoc]

theorem address_count_append (left right : List GateLookup.Event)
    (address : Nat) :
    addressCount (left ++ right) address =
      addressCount left address + addressCount right address := by
  simp [addressCount, List.countP_append]

def rowYieldSteps (rows : List Row) (external : List GateLookup.Event) :
    List (Nat × Nat) :=
  rows.map (fun row => (row.outAddress, row.multiplicity)) ++
    unitSteps external

theorem row_yield_address_total (row : Row) (address : Nat) :
    addressTotal [(row.outAddress, row.multiplicity)] address =
      addressCount row.yields address := by
  simp [addressTotal, addressCount, Row.yields,
    List.countP_replicate]

theorem row_yields_address_total (rows : List Row) (address : Nat) :
    addressTotal
      (rows.map fun row => (row.outAddress, row.multiplicity)) address =
      addressCount (rows.flatMap Row.yields) address := by
  induction rows with
  | nil => simp [addressTotal, addressCount]
  | cons row rest ih =>
      simp only [List.map_cons, List.flatMap_cons]
      rw [show (row.outAddress, row.multiplicity) ::
          (rest.map fun row => (row.outAddress, row.multiplicity)) =
          [(row.outAddress, row.multiplicity)] ++
            (rest.map fun row => (row.outAddress, row.multiplicity)) from rfl]
      rw [address_total_append, row_yield_address_total, ih,
        address_count_append]

theorem compressed_yields_match_events (rows : List Row)
    (external : List GateLookup.Event) (address : Nat) :
    addressTotal (rowYieldSteps rows external) address =
      addressCount (allYields rows external) address := by
  simp only [rowYieldSteps, allYields]
  rw [address_total_append, row_yields_address_total,
    address_total_unit_steps, address_count_append]

theorem checked_compressed_yields_bound
    (rows : List Row) (external : List GateLookup.Event)
    (counts : Nat → Nat)
    (hrun : checkedCounts (rowYieldSteps rows external) = some counts) :
    ∀ address,
      counts address = addressCount (allYields rows external) address ∧
      addressCount (allYields rows external) address < modulus := by
  intro address
  simpa [compressed_yields_match_events] using
    checked_counts_sound (rowYieldSteps rows external) counts hrun address

/-- A successful count of the arithmetic and external input uses, and a
successful compressed count of output yields, discharge the integer
histogram premises needed for the circuit Gate closure. -/
theorem closed_gate_of_checked_counters
    (rows : List Row)
    (externalUses externalYields : List GateLookup.Event)
    (useCounts yieldCounts : Nat → Nat)
    (huseRun : checkedCounts (unitSteps (allUses rows externalUses)) =
      some useCounts)
    (hyieldRun : checkedCounts (rowYieldSteps rows externalYields) =
      some yieldCounts)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < modulus)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0) :
    balanced rows externalUses externalYields := by
  apply closed_gate_contribution_balanced_of_address_counts rows
    externalUses externalYields alpha z hcanonical
    (fun address =>
      (checked_gate_counts_sound (allUses rows externalUses)
        useCounts huseRun address).2)
    (fun address =>
      (checked_compressed_yields_bound rows externalYields
        yieldCounts hyieldRun address).2)
    halpha hz hclosed

end S31.Gadgets.Air.GateCounterCircuit
