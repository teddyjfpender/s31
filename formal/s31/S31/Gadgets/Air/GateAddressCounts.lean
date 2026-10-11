import S31.Gadgets.Air.GateLocalCounts

namespace S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge

def addressCount (events : List Event) (address : Nat) : Nat :=
  events.countP fun event => event.1 == address

theorem event_count_le_address_count
    (events : List Event) (event : Event) :
    events.count event ≤ addressCount events event.1 := by
  rw [List.count_eq_countP]
  apply List.countP_mono_left
  intro candidate _ hmatch
  have heq : candidate = event := (beq_iff_eq).mp hmatch
  subst candidate
  simp

theorem address_bounds_imply_event_bounds
    (left right : List Event)
    (hleft : ∀ address, addressCount left address < 2147483647)
    (hright : ∀ address, addressCount right address < 2147483647) :
    (∀ event ∈ left ++ right,
      left.count event < 2147483647) ∧
    (∀ event ∈ left ++ right,
      right.count event < 2147483647) := by
  constructor
  · intro event _
    exact lt_of_le_of_lt (event_count_le_address_count left event)
      (hleft event.1)
  · intro event _
    exact lt_of_le_of_lt (event_count_le_address_count right event)
      (hright event.1)

theorem fixed_gate_multiset_rejected_of_address_bounds
    (left right : List Event)
    (hcanonical : ∀ event ∈ left ++ right,
      event.1 < 2147483647)
    (hleft : ∀ address, addressCount left address < 2147483647)
    (hright : ∀ address, addressCount right address < 2147483647)
    (hne : ¬ left.Perm right)
    (alpha z : GateSecure)
    (halpha : alpha ∉ badAlpha (left ++ right))
    (hz : z ∉ badZ left right alpha) :
    productionReciprocalSum left alpha z ≠
      productionReciprocalSum right alpha z := by
  obtain ⟨hleftCounts, hrightCounts⟩ :=
    address_bounds_imply_event_bounds left right hleft hright
  exact ((fixed_gate_multiset_sound_of_counts left right hcanonical
    hleftCounts hrightCounts hne).2 alpha halpha).2 z hz

end S31.Gadgets.Air.GateLogUpBridge
