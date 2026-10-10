import S31.Gadgets.Air.GateWireMap

/-!
Structural producer uniqueness for arbitrary committed row values. A native
arithmetic row is one logical producer when its fixed multiplicity is
positive; the Gate lookup may repeat that row's one output event according to
the multiplicity. Other component producers are supplied as a separate
logical roster. Distinct producer addresses, plus coverage of external yield
events by that roster, imply one value per produced address without assuming
the prover used the honest witness-gathering algorithm.
-/

namespace S31.Gadgets.Air.GateProducerRoster

open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap

def activeRows (rows : List Row) : List Row :=
  rows.filter (fun row => 0 < row.multiplicity)

def logicalProducers (rows : List Row) (externalProducers : List Event) :
    List Event :=
  (activeRows rows).map (fun row => (row.outAddress, row.output)) ++
    externalProducers

theorem logical_address_roster (rows : List Row)
    (externalProducers : List Event) :
    (logicalProducers rows externalProducers).map Prod.fst =
      (activeRows rows).map Row.outAddress ++
        externalProducers.map Prod.fst := by
  simp [logicalProducers, List.map_append, List.map_map]

/-- Replicating one row's output event does not create another logical
producer, even if its lookup multiplicity exceeds one. -/
theorem row_yield_in_logical (rows : List Row)
    (externalProducers : List Event) (event : Event)
    (hmem : event ∈ rows.flatMap Row.yields) :
    event ∈ logicalProducers rows externalProducers := by
  obtain ⟨row, hrow, hyield⟩ := List.mem_flatMap.mp hmem
  have hevent : event = (row.outAddress, row.output) :=
    List.eq_of_mem_replicate hyield
  have hpositive : 0 < row.multiplicity := by
    by_contra h
    have hz : row.multiplicity = 0 := Nat.eq_zero_of_not_pos h
    simp [Row.yields, hz] at hyield
  apply List.mem_append_left
  apply List.mem_map.mpr
  exact ⟨row, List.mem_filter.mpr ⟨hrow, by simpa using hpositive⟩,
    hevent.symm⟩

theorem all_yields_in_logical (rows : List Row)
    (externalYields externalProducers : List Event)
    (hexternal : ∀ event ∈ externalYields,
      event ∈ externalProducers)
    (event : Event)
    (hmem : event ∈ allYields rows externalYields) :
    event ∈ logicalProducers rows externalProducers := by
  rcases List.mem_append.mp hmem with hrow | hext
  · exact row_yield_in_logical rows externalProducers event hrow
  · exact List.mem_append_right _ (hexternal event hext)

/-- A producer-address roster with no repeats gives unique values at every
Gate address for arbitrary arithmetic row and external producer witnesses. -/
theorem unique_yields_of_nodup_roster
    (rows : List Row) (externalYields externalProducers : List Event)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hexternal : ∀ event ∈ externalYields,
      event ∈ externalProducers) :
    uniqueProduced (allYields rows externalYields) := by
  have hlogical : ((logicalProducers rows externalProducers).map Prod.fst).Nodup := by
    simpa only [logical_address_roster] using hroster
  intro address left right hleft hright
  have hleft' := all_yields_in_logical rows externalYields
    externalProducers hexternal (address, left) hleft
  have hright' := all_yields_in_logical rows externalYields
    externalProducers hexternal (address, right) hright
  have heq := (List.inj_on_of_nodup_map hlogical) hleft' hright' rfl
  exact congrArg Prod.snd heq

end S31.Gadgets.Air.GateProducerRoster
