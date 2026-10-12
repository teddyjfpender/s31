import S31.Gadgets.Air.GateAddressCounts

namespace S31.Gadgets.Air.GateCounter
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge

def modulus : Nat := 2147483647

/-- Arithmetic model of Zig's `addCanonicalMultiplicity`: reject before a
counter can reach the M31 characteristic. -/
def checkedIncrement (current increment : Nat) : Option Nat :=
  if increment < modulus ∧ current < modulus - increment then
    some (current + increment)
  else none

theorem checked_increment_sound {current increment next : Nat}
    (h : checkedIncrement current increment = some next) :
    next = current + increment ∧ next < modulus := by
  unfold checkedIncrement at h
  split at h
  · obtain ⟨_, hcurrent⟩ := ‹increment < modulus ∧ current < modulus - increment›
    have hnext : current + increment < modulus := by omega
    simp at h
    subst next
    exact ⟨rfl, hnext⟩
  · simp at h

theorem penultimate_count_accepted :
    checkedIncrement (modulus - 2) 1 = some (modulus - 1) := by
  decide

theorem characteristic_count_rejected :
    checkedIncrement (modulus - 1) 1 = none := by
  decide

theorem characteristic_increment_rejected :
    checkedIncrement 0 modulus = none := by
  decide

def addressTotal : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | (address, increment) :: rest, query =>
      (if address = query then increment else 0) + addressTotal rest query

def checkedCountsAux : List (Nat × Nat) → (Nat → Nat) → Option (Nat → Nat)
  | [], counts => some counts
  | (address, increment) :: rest, counts => do
      let next ← checkedIncrement (counts address) increment
      checkedCountsAux rest (Function.update counts address next)

theorem checked_counts_aux_sound (steps : List (Nat × Nat))
    (counts final : Nat → Nat)
    (hcurrent : ∀ address, counts address < modulus)
    (hrun : checkedCountsAux steps counts = some final) :
    ∀ address,
      final address = counts address + addressTotal steps address ∧
      final address < modulus := by
  induction steps generalizing counts with
  | nil =>
      simp only [checkedCountsAux, Option.some.injEq] at hrun
      subst final
      intro address
      simp [addressTotal, hcurrent address]
  | cons step rest ih =>
      obtain ⟨address, increment⟩ := step
      cases hinc : checkedIncrement (counts address) increment with
      | none =>
          simp [checkedCountsAux, hinc] at hrun
      | some next =>
          have hnext := checked_increment_sound hinc
          have hupdated : ∀ query,
              Function.update counts address next query < modulus := by
            intro query
            by_cases heq : query = address
            · subst query
              simpa using hnext.2
            · simpa [Function.update, heq] using hcurrent query
          have htail : checkedCountsAux rest
              (Function.update counts address next) = some final := by
            simpa [checkedCountsAux, hinc] using hrun
          intro query
          obtain ⟨hvalue, hbound⟩ := ih _ hupdated htail query
          constructor
          · by_cases heq : query = address
            · subst query
              simp only [addressTotal, ↓reduceIte]
              simpa using hvalue.trans (by simp [hnext.1, Nat.add_assoc])
            · have hneq : address ≠ query := Ne.symm heq
              simpa [addressTotal, hneq, Function.update, heq] using hvalue
          · exact hbound

def checkedCounts (steps : List (Nat × Nat)) : Option (Nat → Nat) :=
  checkedCountsAux steps (fun _ => 0)

theorem checked_counts_sound (steps : List (Nat × Nat))
    (final : Nat → Nat) (hrun : checkedCounts steps = some final) :
    ∀ address,
      final address = addressTotal steps address ∧
      addressTotal steps address < modulus := by
  intro address
  have hinit : ∀ query, (fun _ : Nat => 0) query < modulus := by
    intro query
    simp [modulus]
  obtain ⟨hvalue, hbound⟩ := checked_counts_aux_sound steps
    (fun _ => 0) final hinit hrun address
  constructor
  · simpa using hvalue
  · rw [← (show final address = addressTotal steps address from by
      simpa using hvalue)]
    exact hbound

def unitSteps (events : List Event) : List (Nat × Nat) :=
  events.map fun event => (event.1, 1)

theorem address_total_unit_steps (events : List Event) (address : Nat) :
    addressTotal (unitSteps events) address =
      addressCount events address := by
  induction events with
  | nil => simp [unitSteps, addressTotal, addressCount]
  | cons event rest ih =>
      simp only [unitSteps, List.map_cons, addressTotal,
        addressCount, List.countP_cons]
      have ih' : addressTotal
          (List.map (fun event => (event.1, 1)) rest) address =
          List.countP (fun event => event.1 == address) rest := by
        simpa [unitSteps, addressCount] using ih
      rw [ih']
      by_cases heq : event.1 = address <;> simp [heq, Nat.add_comm]

theorem checked_gate_counts_sound (events : List Event)
    (final : Nat → Nat)
    (hrun : checkedCounts (unitSteps events) = some final) :
    ∀ address,
      final address = addressCount events address ∧
      addressCount events address < modulus := by
  intro address
  simpa [address_total_unit_steps] using
    checked_counts_sound (unitSteps events) final hrun address

/-- A successful checked walk over the Gate reads and yields supplies the
integer histogram premises of the fixed-list LogUp soundness theorem. -/
theorem checked_gate_multiset_rejected
    (uses yields : List Event)
    (useCounts yieldCounts : Nat → Nat)
    (huseRun : checkedCounts (unitSteps uses) = some useCounts)
    (hyieldRun : checkedCounts (unitSteps yields) = some yieldCounts)
    (hcanonical : ∀ event ∈ uses ++ yields,
      event.1 < modulus)
    (hne : ¬ uses.Perm yields)
    (alpha z : GateSecure)
    (halpha : alpha ∉ badAlpha (uses ++ yields))
    (hz : z ∉ badZ uses yields alpha) :
    productionReciprocalSum uses alpha z ≠
      productionReciprocalSum yields alpha z := by
  apply fixed_gate_multiset_rejected_of_address_bounds uses yields
    hcanonical
    (fun address => (checked_gate_counts_sound uses useCounts huseRun address).2)
    (fun address => (checked_gate_counts_sound yields yieldCounts hyieldRun address).2)
    hne alpha z halpha hz

end S31.Gadgets.Air.GateCounter
