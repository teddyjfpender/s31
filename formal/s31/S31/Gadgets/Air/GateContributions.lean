import S31.Gadgets.Air.GateAddressCounts

namespace S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge

theorem productionReciprocalSum_append
    (left right : List Event) (alpha z : GateSecure) :
    productionReciprocalSum (left ++ right) alpha z =
      productionReciprocalSum left alpha z +
        productionReciprocalSum right alpha z := by
  simp [productionReciprocalSum]

theorem productionReciprocalSum_replicate
    (m : Nat) (event : Event) (alpha z : GateSecure) :
    productionReciprocalSum (List.replicate m event) alpha z =
      (m : GateSecure) *
        (1 / combineTerm (eventTuple event) alpha z) := by
  simp [productionReciprocalSum, nsmul_eq_mul]

def rowContribution (row : Row) (alpha z : GateSecure) : GateSecure :=
  1 / combineTerm (eventTuple (row.in0Address, row.in0)) alpha z +
  1 / combineTerm (eventTuple (row.in1Address, row.in1)) alpha z -
  (row.multiplicity : GateSecure) *
    (1 / combineTerm (eventTuple (row.outAddress, row.output)) alpha z)

theorem rowContribution_eq_event_sums
    (row : Row) (alpha z : GateSecure) :
    rowContribution row alpha z =
      productionReciprocalSum row.uses alpha z -
        productionReciprocalSum row.yields alpha z := by
  simp [rowContribution, Row.uses, Row.yields,
    productionReciprocalSum, nsmul_eq_mul]

theorem productionReciprocalSum_flatMap
    (rows : List Row) (f : Row → List Event) (alpha z : GateSecure) :
    productionReciprocalSum (rows.flatMap f) alpha z =
      (rows.map fun row => productionReciprocalSum (f row) alpha z).sum := by
  induction rows with
  | nil => simp [productionReciprocalSum]
  | cons row rest ih =>
      simp only [List.flatMap_cons, List.map_cons, List.sum_cons]
      rw [productionReciprocalSum_append, ih]

theorem sum_row_contributions (rows : List Row) (alpha z : GateSecure) :
    (rows.map fun row => rowContribution row alpha z).sum =
      (rows.map fun row => productionReciprocalSum row.uses alpha z).sum -
      (rows.map fun row => productionReciprocalSum row.yields alpha z).sum := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [rowContribution_eq_event_sums, ih]
      ring

theorem allGateContribution (rows : List Row)
    (externalUses externalYields : List Event)
    (alpha z : GateSecure) :
    productionReciprocalSum (allUses rows externalUses) alpha z -
      productionReciprocalSum (allYields rows externalYields) alpha z =
    (rows.map fun row => rowContribution row alpha z).sum +
      productionReciprocalSum externalUses alpha z -
      productionReciprocalSum externalYields alpha z := by
  rw [allUses, allYields, productionReciprocalSum_append,
    productionReciprocalSum_append,
    productionReciprocalSum_flatMap,
    productionReciprocalSum_flatMap,
    sum_row_contributions]
  ring

theorem closed_gate_contribution_equal_event_sums
    (rows : List Row) (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0) :
    productionReciprocalSum (allUses rows externalUses) alpha z =
      productionReciprocalSum (allYields rows externalYields) alpha z := by
  apply sub_eq_zero.mp
  rw [allGateContribution]
  exact hclosed

/-- Conditional whole-Gate soundness: the row and external reciprocal
contributions close, challenges avoid the explicit exceptional sets, and
the event geometry obeys canonical-address and count bounds. -/
theorem closed_gate_contribution_balanced
    (rows : List Row) (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (huses : (allUses rows externalUses).length < 2147483647)
    (hyields : (allYields rows externalYields).length < 2147483647)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0) :
    balanced rows externalUses externalYields := by
  by_contra hne
  have hbound := fixed_gate_multiset_sound
    (allUses rows externalUses) (allYields rows externalYields)
    hcanonical huses hyields hne
  have hreject := (hbound.2 alpha halpha).2 z hz
  have heq := closed_gate_contribution_equal_event_sums
    rows externalUses externalYields alpha z hclosed
  exact hreject heq

/-- The same conditional Gate join for large relations: only each event's
own multiplicity must stay below the field characteristic. -/
theorem closed_gate_contribution_balanced_of_counts
    (rows : List Row) (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allUses rows externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      (allYields rows externalYields).count event < 2147483647)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0) :
    balanced rows externalUses externalYields := by
  by_contra hne
  have hbound := fixed_gate_multiset_sound_of_counts
    (allUses rows externalUses) (allYields rows externalYields)
    hcanonical huses hyields hne
  have hreject := (hbound.2 alpha halpha).2 z hz
  exact hreject (closed_gate_contribution_equal_event_sums
    rows externalUses externalYields alpha z hclosed)

/-- Address-level histograms are sufficient to bound every individual Gate
tuple count. This is the form closest to the checked `computeUses` counters. -/
theorem closed_gate_contribution_balanced_of_address_counts
    (rows : List Row) (externalUses externalYields : List Event)
    (alpha z : GateSecure)
    (hcanonical : ∀ event ∈
      allUses rows externalUses ++ allYields rows externalYields,
      event.1 < 2147483647)
    (huses : ∀ address,
      addressCount (allUses rows externalUses) address < 2147483647)
    (hyields : ∀ address,
      addressCount (allYields rows externalYields) address < 2147483647)
    (halpha : alpha ∉ badAlpha
      (allUses rows externalUses ++ allYields rows externalYields))
    (hz : z ∉ badZ
      (allUses rows externalUses) (allYields rows externalYields) alpha)
    (hclosed :
      (rows.map fun row => rowContribution row alpha z).sum +
        productionReciprocalSum externalUses alpha z -
        productionReciprocalSum externalYields alpha z = 0) :
    balanced rows externalUses externalYields := by
  obtain ⟨hleft, hright⟩ := address_bounds_imply_event_bounds
    (allUses rows externalUses) (allYields rows externalYields)
    huses hyields
  exact closed_gate_contribution_balanced_of_counts
    rows externalUses externalYields alpha z hcanonical
    hleft hright halpha hz hclosed

end S31.Gadgets.Air.GateLogUpBridge
