import S31.Gadgets.Air.GateContributions

namespace S31.Gadgets.Air.GateContributions
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

theorem addressed_row_sound_of_closed_gate
    (rows : List Row) (externalUses externalYields : List GateLookup.Event)
    (r : Row) (hr : r ∈ rows)
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
        productionReciprocalSum externalYields alpha z = 0)
    (hunique : uniqueProduced (allYields rows externalYields))
    (left right : Quad)
    (hleft : (r.in0Address, left) ∈ allYields rows externalYields)
    (hright : (r.in1Address, right) ∈ allYields rows externalYields)
    (hair : accepts r.flags r.in0 r.in1 r.output) :
    ∃ op, r.flags = encode op ∧ r.output = evaluate op left right := by
  exact addressed_row_sound rows externalUses externalYields r hr
    (closed_gate_contribution_balanced rows externalUses externalYields
      alpha z hcanonical huses hyields halpha hz hclosed)
    hunique left right hleft hright hair

theorem addressed_row_sound_of_closed_gate_counts
    (rows : List Row)
    (externalUses externalYields : List GateLookup.Event)
    (r : Row) (hr : r ∈ rows)
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
        productionReciprocalSum externalYields alpha z = 0)
    (hunique : uniqueProduced (allYields rows externalYields))
    (left right : Quad)
    (hleft : (r.in0Address, left) ∈ allYields rows externalYields)
    (hright : (r.in1Address, right) ∈ allYields rows externalYields)
    (hair : accepts r.flags r.in0 r.in1 r.output) :
    ∃ op, r.flags = encode op ∧ r.output = evaluate op left right := by
  exact addressed_row_sound rows externalUses externalYields r hr
    (closed_gate_contribution_balanced_of_counts
      rows externalUses externalYields alpha z
      hcanonical huses hyields halpha hz hclosed)
    hunique left right hleft hright hair

/-- A locally valid forged row cannot pass the Gate reciprocal closure
outside the explicit exceptional challenge sets. -/
theorem forged_example_no_good_closure (alpha z : GateSecure)
    (halpha : alpha ∉ badAlpha
      (allUses [forgedExample] forgedExternalUses ++
        allYields [forgedExample] exampleExternalYields))
    (hz : z ∉ badZ
      (allUses [forgedExample] forgedExternalUses)
      (allYields [forgedExample] exampleExternalYields) alpha) :
    (rowContribution forgedExample alpha z +
      productionReciprocalSum forgedExternalUses alpha z -
      productionReciprocalSum exampleExternalYields alpha z) ≠ 0 := by
  intro hclosed
  have hcanonical : ∀ event ∈
      allUses [forgedExample] forgedExternalUses ++
        allYields [forgedExample] exampleExternalYields,
      event.1 < 2147483647 := by decide
  have huses : (allUses [forgedExample] forgedExternalUses).length <
      2147483647 := by decide
  have hyields : (allYields [forgedExample] exampleExternalYields).length <
      2147483647 := by decide
  have hbalanced := closed_gate_contribution_balanced
    [forgedExample] forgedExternalUses exampleExternalYields alpha z
    hcanonical huses hyields halpha hz (by simpa using hclosed)
  exact forged_example_rejected hbalanced

theorem honest_example_contribution_closed (alpha z : GateSecure) :
    rowContribution honestExample alpha z +
      productionReciprocalSum exampleExternalUses alpha z -
      productionReciprocalSum exampleExternalYields alpha z = 0 := by
  have hsum : productionReciprocalSum
      (allUses [honestExample] exampleExternalUses) alpha z =
      productionReciprocalSum
      (allYields [honestExample] exampleExternalYields) alpha z := by
    exact (honest_example_balanced.map
      (fun event => 1 / combineTerm (eventTuple event) alpha z)).sum_eq
  have hzero : productionReciprocalSum
      (allUses [honestExample] exampleExternalUses) alpha z -
      productionReciprocalSum
      (allYields [honestExample] exampleExternalYields) alpha z = 0 :=
    sub_eq_zero.mpr hsum
  rw [allGateContribution] at hzero
  simpa using hzero

end S31.Gadgets.Air.GateContributions
