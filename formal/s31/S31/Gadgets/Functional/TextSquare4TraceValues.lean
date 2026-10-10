import S31.Gadgets.Functional.TextSquare4TraceRows
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

private theorem low_declared_event (values : Nat → Quad)
    (address : Nat) (haddress : address < 35) :
    (address, values address) ∈ declaredEvents values := by
  unfold declaredEvents
  apply List.mem_map.mpr
  refine ⟨address, ?_, rfl⟩
  have hbound : address < TextSquare4Native.declaredVarCount :=
    Nat.lt_of_lt_of_le haddress native_compiler_declared_facts.1
  simpa [TextSquare4Native.declaredProducerAddresses] using hbound

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
  have hcovered : ∀ address value, address < 35 →
      (address, value) ∈
        allYields (templates.map (gather values)) externalYields →
      (address, value) ∈ declaredEvents values := by
    intro address value haddress hmem
    have hvalue := gathered_yields_match_table values templates
      externalYields hexternal address value hmem
    rw [hvalue]
    exact low_declared_event values address haddress
  exact native_public_claim_of_exported_producers
    (templates.map (gather values)) externalUses externalYields
    values input claimed hbalance hcovered hpath hpins

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

end S31.Functional.TextSquare4TraceValues
