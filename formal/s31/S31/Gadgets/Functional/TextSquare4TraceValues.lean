import S31.Gadgets.Functional.TextSquare4TraceRows
import S31.Gadgets.Functional.TextSquare4RawSoundness
import S31.Gadgets.Air.GateTraceValues

/-!
Join the source-checked fourth-power row schedule to the native arithmetic
trace gather model. All ordinary arithmetic row values come from one address
table by construction. External component yields, exact Gate balance, public
pins and local AIR acceptance remain explicit premises.
-/

namespace S31.Functional.TextSquare4TraceValues

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateTraceValues
open S31.Functional.TextSquare4GateJoin
open S31.Functional.TextSquare4TraceRows
open S31.Functional.TextSquare4RawSoundness
open S31.Gadgets.Air.GateChallenge

private theorem low_declared_event (values : Nat → Quad)
    (address : Nat) (haddress : address < 35) :
    (address, values address) ∈ declaredEvents values := by
  unfold declaredEvents
  apply List.mem_map.mpr
  refine ⟨address, ?_, rfl⟩
  have hbound : address < TextSquare4Native.declaredVarCount :=
    Nat.lt_of_lt_of_le haddress native_compiler_declared_facts.1
  simpa [TextSquare4Native.declaredProducerAddresses] using hbound

theorem gathered_coverage
    (templates : List Row) (values : Nat → Quad)
    (externalYields : List Event)
    (hexternal : ∀ event ∈ externalYields,
      event.2 = values event.1)
    (address : Nat) (value : Quad) (haddress : address < 35)
    (hmem : (address, value) ∈
      allYields (templates.map (gather values)) externalYields) :
    (address, value) ∈ declaredEvents values := by
  have hvalue := gathered_yields_match_table values templates
    externalYields hexternal address value hmem
  rw [hvalue]
  exact low_declared_event values address haddress

/-- For native-style gathered arithmetic rows, no separate value-coverage
premise is needed for their Gate yields. Only external yields require a value
table correspondence; they are emitted by other components. -/
theorem native_claim_of_gathered_rows
    (templates : List Row) (values : Nat → Quad)
    (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced (templates.map (gather values))
      externalUses externalYields)
    (hexternal : ∀ event ∈ externalYields,
      event.2 = values event.1)
    (hpath : nativePathRows (templates.map (gather values)))
    (hpins : pinnedEvents
      (allYields (templates.map (gather values)) externalYields)
      input claimed) :
    claimed = TextSquare4Air.fourth input := by
  exact native_public_claim_of_exported_producers
    (templates.map (gather values)) externalUses externalYields
    values input claimed hbalance
    (gathered_coverage templates values externalYields hexternal)
    hpath hpins

/-- The 512 source-checked padded AIR positions may be supplied as fixed row
templates. Filling their three witness columns from the value table and
checking the 23 selected local rows suffices for the public claim, subject to
the remaining Gate and boundary premises. -/
theorem native_claim_of_gathered_padded_rows
    (templates : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (values : Nat → Quad)
    (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced
      (List.ofFn (fun i => gather values (templates i)))
      externalUses externalYields)
    (hexternal : ∀ event ∈ externalYields,
      event.2 = values event.1)
    (hselected : selectedRows (fun i => gather values (templates i)))
    (hpins : pinnedEvents
      (allYields (List.ofFn (fun i => gather values (templates i)))
        externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  have hrows : List.ofFn (fun i => gather values (templates i)) =
      (List.ofFn templates).map (gather values) := by
    simp only [List.map_ofFn, Function.comp_def]
  apply native_claim_of_gathered_rows
    (List.ofFn templates) values externalUses externalYields input claimed
  · simpa only [← hrows] using hbalance
  · exact hexternal
  · simpa only [← hrows] using
      (selected_rows_imply_path _ hselected)
  · simpa only [← hrows] using hpins

/-- For a fixed forged claim, source-extracted Gate LogUp residuals have the
same explicit ideal-challenge exceptional-pair bound when ordinary arithmetic
trace values are gathered from one table. Only external producer values need
an additional table-correspondence premise. This remains a conditional
algebraic bound, not a native verifier security theorem. -/
theorem forged_claim_gathered_padded_card_le
    (prev : Equiv.Perm
      (Fin TextSquare4Native.paddedArithmeticRowCount))
    (templates : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (values : Nat → Quad)
    (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hforged : claimed ≠ TextSquare4Air.fourth input)
    (hexternal : ∀ event ∈ externalYields,
      event.2 = values event.1)
    (hselected : selectedRows (fun i => gather values (templates i)))
    (hpins : pinnedEvents
      (allYields (List.ofFn (fun i => gather values (templates i)))
        externalYields) input claimed)
    (hcanonical : ∀ event ∈
      allUses (List.ofFn (fun i => gather values (templates i))) externalUses ++
        allYields (List.ofFn (fun i => gather values (templates i))) externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (List.ofFn (fun i => gather values (templates i))) externalUses ++
        allYields (List.ofFn (fun i => gather values (templates i))) externalYields,
      (allUses (List.ofFn (fun i => gather values (templates i)))
        externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (List.ofFn (fun i => gather values (templates i))) externalUses ++
        allYields (List.ofFn (fun i => gather values (templates i))) externalYields,
      (allYields (List.ofFn (fun i => gather values (templates i)))
        externalYields).count event < 2147483647) :
    (nativeAcceptingPairs 9 prev (fun i => gather values (templates i))
      externalUses externalYields).card ≤
      (5 * (allUses (List.ofFn (fun i => gather values (templates i)))
        externalUses ++
        allYields (List.ofFn (fun i => gather values (templates i)))
          externalYields).toFinset.card ^ 2 +
        2 * (allUses (List.ofFn (fun i => gather values (templates i)))
          externalUses ++
          allYields (List.ofFn (fun i => gather values (templates i)))
            externalYields).toFinset.card +
        1536) * Fintype.card GateSecure := by
  have hrows : List.ofFn (fun i => gather values (templates i)) =
      (List.ofFn templates).map (gather values) := by
    simp only [List.map_ofFn, Function.comp_def]
  have hcovered : ∀ address value, address < 35 →
      (address, value) ∈
        allYields (List.ofFn (fun i => gather values (templates i)))
          externalYields →
      (address, value) ∈ declaredEvents values := by
    intro address value haddress hmem
    apply gathered_coverage (List.ofFn templates) values
      externalYields hexternal address value haddress
    simpa only [← hrows] using hmem
  exact forged_claim_emitted_row_acceptance_card_le
    prev (fun i => gather values (templates i))
    externalUses externalYields values input claimed hforged hcovered
    hselected hpins hcanonical huses hyields

end S31.Functional.TextSquare4TraceValues
