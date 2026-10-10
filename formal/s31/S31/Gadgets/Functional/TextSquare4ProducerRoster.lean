import S31.Gadgets.Functional.TextSquare4TraceRows
import S31.Gadgets.Functional.TextSquare4RawSoundness
import S31.Gadgets.Air.GateProducerRoster

/-!
The fourth-power path for arbitrary committed arithmetic row values.
Producer uniqueness follows from a structural roster of active row output
addresses and other component producers, rather than an honest writer's
address-indexed value table. Exact Gate balance, accepted selected rows and
public/constant events remain premises.
-/

namespace S31.Functional.TextSquare4ProducerRoster

open S31
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateProducerRoster
open S31.Functional.TextSquare4GateJoin
open S31.Functional.TextSquare4TraceRows
open S31.Functional.TextSquare4RawSoundness
open S31.Gadgets.Air.GateChallenge

set_option maxRecDepth 4096 in
/-- The native exporter enumerates the actual padded preprocessed arithmetic
rows with positive output multiplicity. Their output addresses are all
distinct, and this source program has no producer in another component. -/
theorem source_roster_nodup :
    (TextSquare4Native.activeArithmeticProducerAddresses ++
      TextSquare4Native.externalProducerAddresses).Nodup := by
  decide

theorem source_has_no_external_producers :
    TextSquare4Native.externalProducerAddresses = [] := by
  decide

/-- Repeated multiplicity yields from one active arithmetic row do not break
producer uniqueness. This theorem allows arbitrary values in every row. -/
theorem native_claim_of_producer_roster
    (rows : List Row)
    (externalUses externalYields externalProducers : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hroster : ((activeRows rows).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hexternal : ∀ event ∈ externalYields,
      event ∈ externalProducers)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields)
      input claimed) :
    claimed = TextSquare4Air.fourth input := by
  have hunique := unique_yields_of_nodup_roster rows
    externalYields externalProducers hroster hexternal
  exact native_public_claim_of_gate_balance rows externalUses
    externalYields input claimed hbalance hunique hpath hpins

/-- The preprocessed 512-row schedule supplies the 23 selected path rows.
The roster premise covers every active arithmetic row and all other logical
producers; the source exporter checks that the concrete circuit has one
declared producer per address, but this theorem leaves native row/event
correspondence explicit. -/
theorem native_claim_of_padded_producer_roster
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (externalUses externalYields externalProducers : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced (List.ofFn rows)
      externalUses externalYields)
    (hroster : ((activeRows (List.ofFn rows)).map Row.outAddress ++
      externalProducers.map Prod.fst).Nodup)
    (hexternal : ∀ event ∈ externalYields,
      event ∈ externalProducers)
    (hselected : selectedRows rows)
    (hpins : pinnedEvents (allYields (List.ofFn rows) externalYields)
      input claimed) :
    claimed = TextSquare4Air.fourth input :=
  native_claim_of_producer_roster (List.ofFn rows)
    externalUses externalYields externalProducers input claimed
    hbalance hroster hexternal
    (selected_rows_imply_path rows hselected) hpins

/-- For the source-checked fourth-power circuit, arbitrary arithmetic trace
values cannot create two different produced values at one declared address.
The only remaining roster premise says the modeled row addresses and fixed
multiplicities are the native preprocessed columns enumerated by the exporter. -/
theorem native_claim_of_source_roster
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (externalUses : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced (List.ofFn rows) externalUses [])
    (hfixed : (activeRows (List.ofFn rows)).map Row.outAddress =
      TextSquare4Native.activeArithmeticProducerAddresses)
    (hselected : selectedRows rows)
    (hpins : pinnedEvents (allYields (List.ofFn rows) [])
      input claimed) :
    claimed = TextSquare4Air.fourth input := by
  apply native_claim_of_padded_producer_roster rows
    externalUses [] [] input claimed hbalance
  · simpa only [List.map_nil, List.append_nil, hfixed,
      source_has_no_external_producers, List.append_nil] using
      source_roster_nodup
  · intro event hmem
    simp at hmem
  · exact hselected
  · exact hpins

set_option maxRecDepth 4096 in
/-- The source-checked active producer roster rules out a forged public
result for arbitrary fixed arithmetic row values, except at the formally
bounded Gate challenge pairs. This theorem does not assume those values came
from the honest witness writer. Committed column, opening and transcript
correspondence remain separate obligations. -/
theorem forged_source_roster_raw_acceptance_card_le
    (prev : Equiv.Perm
      (Fin TextSquare4Native.paddedArithmeticRowCount))
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (externalUses : List Event)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ TextSquare4Air.fourth input)
    (hfixed : (activeRows (List.ofFn rows)).map Row.outAddress =
      TextSquare4Native.activeArithmeticProducerAddresses)
    (hselected : selectedRows rows)
    (hpins : pinnedEvents (allYields (List.ofFn rows) [])
      input claimed)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) [],
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) [],
      (allUses (List.ofFn rows) externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) [],
      (allYields (List.ofFn rows) []).count event < 2147483647) :
    (nativeAcceptingPairs 9 prev rows externalUses []).card ≤
      (5 * (allUses (List.ofFn rows) externalUses ++
        allYields (List.ofFn rows) []).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn rows) externalUses ++
          allYields (List.ofFn rows) []).toFinset.card +
        1536) * Fintype.card GateSecure := by
  have hwrong : ¬ balanced (List.ofFn rows) externalUses [] := by
    intro hbalance
    exact hforged (native_claim_of_source_roster rows
      externalUses input claimed hbalance hfixed hselected hpins)
  have hden : (S31.Gadgets.Air.GateAirRawSoundness.denominatorEvents
      (List.ofFn rows)).length = 1536 := by
    rw [S31.Gadgets.Air.GateAirRawSoundness.denominator_events_length,
      List.length_ofFn]
    norm_num [TextSquare4Native.paddedArithmeticRowCount]
  have hbound := S31.Gadgets.Air.GateAirRawSoundness.raw_false_acceptance_card_le
    9 prev rows
    externalUses [] hcanonical huses hyields hwrong
  rw [native_accepting_pairs_eq_raw]
  simpa only [hden] using hbound

end S31.Functional.TextSquare4ProducerRoster
