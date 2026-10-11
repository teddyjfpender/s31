import S31.Gadgets.Air.GateCounterCircuit

namespace S31.Gadgets.Air.GateUseTraversal
open S31.Gadgets.Air.GateCounter
open S31.Gadgets.Air.GateCounterCircuit
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge

/-- A modeled checked walk counts supplied base Gate reads one by one,
all permutation zero-wire reads in a single increment, then fixed private
SHA boundary reads individually. Zig counts declared-variable reads but
handles permutation scratch reads structurally. -/
def compressedUses (baseUses : List GateLookup.Event)
    (permutationRows : Nat) (shaBoundary : List GateLookup.Event) :
    List (Nat × Nat) :=
  unitSteps baseUses ++ [(0, permutationRows)] ++ unitSteps shaBoundary

/-- Ideal Gate event list corresponding to those compressed counts. -/
def expandedUses (baseUses : List GateLookup.Event)
    (permutationRows : Nat) (shaBoundary : List GateLookup.Event) :
    List GateLookup.Event :=
  baseUses ++
    List.replicate permutationRows (0, S31.Gadgets.Packed.base 0) ++
    shaBoundary

theorem zero_step_matches_permutation_events (rows address : Nat) :
    addressTotal [(0, rows)] address =
      addressCount
        (List.replicate rows (0, S31.Gadgets.Packed.base 0))
        address := by
  simp [addressTotal, addressCount, List.countP_replicate]

theorem compressed_uses_match_events
    (baseUses shaBoundary : List GateLookup.Event)
    (permutationRows address : Nat) :
    addressTotal
      (compressedUses baseUses permutationRows shaBoundary) address =
      addressCount
        (expandedUses baseUses permutationRows shaBoundary) address := by
  simp only [compressedUses, expandedUses]
  rw [address_total_append, address_total_append,
    address_total_unit_steps,
    zero_step_matches_permutation_events,
    address_total_unit_steps,
    address_count_append, address_count_append]

theorem checked_compressed_uses_bound
    (baseUses shaBoundary : List GateLookup.Event)
    (permutationRows : Nat) (counts : Nat → Nat)
    (hrun : checkedCounts
      (compressedUses baseUses permutationRows shaBoundary) = some counts) :
    ∀ address,
      counts address = addressCount
        (expandedUses baseUses permutationRows shaBoundary) address ∧
      addressCount
        (expandedUses baseUses permutationRows shaBoundary) address < modulus := by
  intro address
  simpa [compressed_uses_match_events] using
    checked_counts_sound
      (compressedUses baseUses permutationRows shaBoundary)
      counts hrun address

/-- The circuit closure can consume the actual compressed use and yield
counter shapes once the ordinary component event traversal is identified. -/
theorem closed_gate_of_compressed_counters
    (rows : List Row) (externalUses externalYields : List GateLookup.Event)
    (baseUses shaBoundary : List GateLookup.Event)
    (permutationRows : Nat) (useCounts yieldCounts : Nat → Nat)
    (huses : allUses rows externalUses =
      expandedUses baseUses permutationRows shaBoundary)
    (huseRun : checkedCounts
      (compressedUses baseUses permutationRows shaBoundary) =
        some useCounts)
    (hyieldRun : checkedCounts
      (rowYieldSteps rows externalYields) = some yieldCounts)
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
    (fun address => by
      rw [huses]
      exact (checked_compressed_uses_bound baseUses shaBoundary
        permutationRows useCounts huseRun address).2)
    (fun address =>
      (checked_compressed_yields_bound rows externalYields
        yieldCounts hyieldRun address).2)
    halpha hz hclosed

end S31.Gadgets.Air.GateUseTraversal
