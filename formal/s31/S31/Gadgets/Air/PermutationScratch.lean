import S31.Gadgets.Air.GateUseTraversal

namespace S31.Gadgets.Air.PermutationScratch
open S31.Gadgets.Air.GateCounter
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateLookup

theorem address_count_le_length
    (events : List GateLookup.Event) (address : Nat) :
    addressCount events address ≤ events.length := by
  exact List.countP_le_length

/-- The checked increment of the zero-wire counter by two rows per
permutation pair also bounds the number of shared scratch reads and yields.
It does not require scratch addresses to have unique producer values. -/
theorem scratch_bounds_of_checked_zero_increment
    (current permutationRows next : Nat)
    (scratchReads scratchYields : List GateLookup.Event)
    (hchecked : checkedIncrement current permutationRows = some next)
    (hreads : permutationRows = 2 * scratchReads.length)
    (hyields : permutationRows = 2 * scratchYields.length) :
    ∀ address,
      addressCount scratchReads address < GateCounter.modulus ∧
      addressCount scratchYields address < GateCounter.modulus := by
  have hnext := checked_increment_sound hchecked
  have hrows : permutationRows < GateCounter.modulus := by omega
  intro address
  constructor
  · exact lt_of_le_of_lt (address_count_le_length scratchReads address)
      (by omega)
  · exact lt_of_le_of_lt (address_count_le_length scratchYields address)
      (by omega)

theorem address_count_zero_above
    (events : List GateLookup.Event) (bound address : Nat)
    (hbelow : ∀ event ∈ events, event.1 < bound)
    (haddress : bound ≤ address) :
    addressCount events address = 0 := by
  induction events with
  | nil => simp [addressCount]
  | cons event rest ih =>
      have hneq : event.1 ≠ address := by
        have h := hbelow event (by simp)
        omega
      have htail : ∀ item ∈ rest, item.1 < bound := by
        intro item hmem
        exact hbelow item (by simp [hmem])
      have hrest := ih htail
      simpa [addressCount, List.countP_cons, hneq] using hrest

theorem address_count_zero_below
    (events : List GateLookup.Event) (bound address : Nat)
    (habove : ∀ event ∈ events, bound ≤ event.1)
    (haddress : address < bound) :
    addressCount events address = 0 := by
  induction events with
  | nil => simp [addressCount]
  | cons event rest ih =>
      have hneq : event.1 ≠ address := by
        have h := habove event (by simp)
        omega
      have htail : ∀ item ∈ rest, bound ≤ item.1 := by
        intro item hmem
        exact habove item (by simp [hmem])
      have hrest := ih htail
      simpa [addressCount, List.countP_cons, hneq] using hrest

/-- Declared and scratch addresses live in disjoint numeric ranges, so the
total histogram inherits their individual bounds without adding counts. -/
theorem partitioned_address_bounds
    (declared scratch : List GateLookup.Event) (bound : Nat)
    (hdeclaredRange : ∀ event ∈ declared, event.1 < bound)
    (hscratchRange : ∀ event ∈ scratch, bound ≤ event.1)
    (hdeclaredCount : ∀ address,
      addressCount declared address < GateCounter.modulus)
    (hscratchCount : ∀ address,
      addressCount scratch address < GateCounter.modulus) :
    ∀ address, addressCount (declared ++ scratch) address < GateCounter.modulus := by
  intro address
  rw [GateCounterCircuit.address_count_append]
  by_cases haddress : address < bound
  · rw [address_count_zero_below scratch bound address
      hscratchRange haddress]
    simpa using hdeclaredCount address
  · have hge : bound ≤ address := by omega
    rw [address_count_zero_above declared bound address
      hdeclaredRange hge]
    simpa using hscratchCount address

/-- One checked zero-wire increment controls both scratch-event lists. With
declared-variable bounds and the disjoint address ranges, every full Gate
address count stays below the field characteristic. -/
theorem full_bounds_with_permutation_scratch
    (declaredUses scratchUses declaredYields scratchYields :
      List GateLookup.Event)
    (bound current permutationRows next : Nat)
    (hdeclaredUseRange : ∀ event ∈ declaredUses, event.1 < bound)
    (hdeclaredYieldRange : ∀ event ∈ declaredYields, event.1 < bound)
    (hscratchUseRange : ∀ event ∈ scratchUses, bound ≤ event.1)
    (hscratchYieldRange : ∀ event ∈ scratchYields, bound ≤ event.1)
    (hdeclaredUses : ∀ address,
      addressCount declaredUses address < GateCounter.modulus)
    (hdeclaredYields : ∀ address,
      addressCount declaredYields address < GateCounter.modulus)
    (hchecked : checkedIncrement current permutationRows = some next)
    (hreads : permutationRows = 2 * scratchUses.length)
    (hyields : permutationRows = 2 * scratchYields.length) :
    ∀ address,
      addressCount (declaredUses ++ scratchUses) address <
        GateCounter.modulus ∧
      addressCount (declaredYields ++ scratchYields) address <
        GateCounter.modulus := by
  have hscratch := scratch_bounds_of_checked_zero_increment
    current permutationRows next scratchUses scratchYields
    hchecked hreads hyields
  intro address
  constructor
  · exact partitioned_address_bounds declaredUses scratchUses bound
      hdeclaredUseRange hscratchUseRange hdeclaredUses
      (fun a => (hscratch a).1) address
  · exact partitioned_address_bounds declaredYields scratchYields bound
      hdeclaredYieldRange hscratchYieldRange hdeclaredYields
      (fun a => (hscratch a).2) address

end S31.Gadgets.Air.PermutationScratch
