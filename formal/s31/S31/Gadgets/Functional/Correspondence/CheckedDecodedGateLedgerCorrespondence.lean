import S31.Gadgets.Functional.Correspondence.CheckedFullLocalArithmeticComposition
import S31.Gadgets.Functional.Correspondence.CheckedGateAddressLedger

/-!
The checked full modeled roster is listed by source/public cells followed by
constant cells, whereas the decoded physical trace is indexed by row number.
This module proves the row permutation and then transports ideal Gate balance
to the *synthetic decoded trace*. It does not bind that trace to a native
preprocessed commitment, proof opening, or LogUp verifier.
-/

namespace S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.CheckedGateAddressLedger

private theorem findRow_eq_of_nodup (cells : List ColumnCell)
    (hnodup : (cells.map ColumnCell.traceRow).Nodup)
    (cell : ColumnCell) (hmem : cell ∈ cells) :
    findRow cells cell.traceRow = some cell := by
  induction cells with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [findRow]
      by_cases heq : head.traceRow = cell.traceRow
      · simp only [heq, ↓reduceIte]
        have hunique := List.inj_on_of_nodup_map hnodup
        exact congrArg some (hunique (by simp) hmem heq)
      · simp only [heq, ↓reduceIte]
        have htail : cell ∈ tail := by
          rcases List.mem_cons.mp hmem with h | h
          · subst head
            exact False.elim (heq rfl)
          · exact h
        exact ih hnodup.of_cons htail

/-- Reading a selected physical row recovers exactly the ledger row, including
all eight fixed fields and all twelve main values. -/
theorem selected_decoded_row_eq_gateRow (cells : List ColumnCell)
    (wire : Nat → Quad)
    (hnodup : (cells.map ColumnCell.traceRow).Nodup)
    (hbound : ∀ cell ∈ cells, cell.traceRow < 512)
    (hcanonical : ∀ cell ∈ cells,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
      cell.out < 2147483647 ∧ cell.mults < 2147483647)
    (cell : ColumnCell) (hmem : cell ∈ cells) :
    row (trace cells wire) ⟨cell.traceRow, hbound cell hmem⟩ =
      gateRow wire cell := by
  have hfind := findRow_eq_of_nodup cells hnodup cell hmem
  have hc := hcanonical cell hmem
  simp [row, trace, zeroTrace, fixedAt, mainAt, hfind, gateRow,
    S31.Functional.SSANativePolynomialRows.cellFlags,
    Nat.mod_eq_of_lt hc.1, Nat.mod_eq_of_lt hc.2.1,
    Nat.mod_eq_of_lt hc.2.2.1, Nat.mod_eq_of_lt hc.2.2.2]

/-- The checked list of 512 modeled cells is a permutation of physical row
indices 0 through 511. The list itself is deliberately not row-sorted. -/
theorem checked_joined_position_perm
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ((joinedCells certificate island).map ColumnCell.traceRow).Perm
      (List.range 512) := by
  have hroster := checked_joined_roster_complete sourceBytes normalizedBytes
    certificate island values hcheck hisland
  apply (List.perm_ext_iff_of_nodup hroster.1 List.nodup_range).2
  intro row
  constructor
  · intro hmem
    obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hmem
    exact List.mem_range.mpr (heq ▸ hroster.2.1 cell hcell)
  · intro hmem
    obtain ⟨cell, hcell, heq⟩ := hroster.2.2
      ⟨row, List.mem_range.mp hmem⟩
    exact List.mem_map.mpr ⟨cell, hcell, heq⟩

private def physicalRow (cells : List ColumnCell) (wire : Nat → Quad)
    (index : Nat) : Row :=
  row (trace cells wire) ⟨index % 512, Nat.mod_lt _ (by decide)⟩

private theorem physical_row_range (cells : List ColumnCell)
    (wire : Nat → Quad) :
    (List.range 512).map (physicalRow cells wire) =
      nativeRows (trace cells wire) := by
  unfold nativeRows
  rw [List.ofFn_eq_map, ← List.map_coe_finRange_eq_range, List.map_map]
  apply List.map_congr_left
  intro index hindex
  simp [physicalRow, Nat.mod_eq_of_lt index.isLt]

/-- The exact logical ledger rows are a permutation of all 512 decoded rows.
The result is a permutation because `joinedCells` is grouped by role, not
ordered by physical position. -/
theorem decoded_rows_perm (cells : List ColumnCell) (wire : Nat → Quad)
    (hnodup : (cells.map ColumnCell.traceRow).Nodup)
    (hbound : ∀ cell ∈ cells, cell.traceRow < 512)
    (hcanonical : ∀ cell ∈ cells,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
      cell.out < 2147483647 ∧ cell.mults < 2147483647)
    (hposition : (cells.map ColumnCell.traceRow).Perm (List.range 512)) :
    (gateRows cells wire).Perm (nativeRows (trace cells wire)) := by
  have hleft : (cells.map ColumnCell.traceRow).map (physicalRow cells wire) =
      gateRows cells wire := by
    simp only [List.map_map, gateRows]
    apply List.map_congr_left
    intro cell hmem
    simp only [Function.comp_apply, physicalRow,
      Nat.mod_eq_of_lt (hbound cell hmem)]
    exact selected_decoded_row_eq_gateRow cells wire hnodup hbound
      hcanonical cell hmem
  have hright := physical_row_range cells wire
  rw [← hleft, ← hright]
  exact hposition.map (physicalRow cells wire)

/-- The accepted bytes and checked island specialize the generic row
permutation to the complete modeled direct-Gate roster. -/
theorem checked_joined_decoded_rows_perm
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad) (wire : Nat → Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    (gateRows (joinedCells certificate island) wire).Perm
      (nativeRows (trace (joinedCells certificate island) wire)) := by
  have hroster := checked_joined_roster_complete sourceBytes normalizedBytes
    certificate island values hcheck hisland
  have hcanonical : ∀ cell ∈ joinedCells certificate island,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojected | hislandCell
    · exact S31.Functional.Correspondence.AcceptedPublicFixedCells.projected_cells_canonical
        sourceBytes normalizedBytes certificate hcheck cell hprojected
    · have hsound := checked_cells_sound certificate island values
        hisland cell hislandCell
      rcases hsound with ⟨_, _, _, _, _, _, _, h0, h1, ho, hm, _⟩
      exact ⟨h0, h1, ho, hm⟩
  exact decoded_rows_perm (joinedCells certificate island) wire
    hroster.1 hroster.2.1 hcanonical
    (checked_joined_position_perm sourceBytes normalizedBytes certificate
      island values hcheck hisland)

/-- Reordering the rows cannot change the multiset of Gate use/yield
events, even when the two external event lists are retained verbatim. -/
theorem balanced_of_rows_perm (first second : List Row)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (hrows : first.Perm second)
    (hbalanced : balanced first externalUses externalYields) :
    balanced second externalUses externalYields := by
  unfold balanced allUses allYields at *
  have huses := (hrows.flatMap_right Row.uses).append_right externalUses
  have hyields := (hrows.flatMap_right Row.yields).append_right externalYields
  exact huses.symm.trans (hbalanced.trans hyields)

/-- A successful bounded address ledger check therefore balances actual
decoded rows of the constructed 512-row trace, in physical row order. Native
commitment and external-event binding are separate obligations. -/
theorem checked_joined_decoded_gate_balance
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad) (wire : Nat → Quad)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    balanced (nativeRows (trace (joinedCells certificate island) wire))
      (wireEvents wire externalUses) (wireEvents wire externalYields) := by
  exact balanced_of_rows_perm _ _ _ _
    (checked_joined_decoded_rows_perm sourceBytes normalizedBytes certificate
      island values wire hcheck hisland)
    (CheckedGateAddressLedger.check_sound _ wire _ _ hledger)

/-- A synthetic decoded trace whose own two external event lists are exactly
the supplied coherent wire events. The source of these address lists remains
an explicit input; this constructor does not authenticate native feeders. -/
def traceWithExternal (cells : List ColumnCell) (wire : Nat → Quad)
    (externalUses externalYields : List Nat) : Trace 9 :=
  { trace cells wire with
    externalUses := wireEvents wire externalUses,
    externalYields := wireEvents wire externalYields }

/-- In the synthetic trace with explicit external events, Gate balance is
stated over the trace's own decoded rows and event lists. -/
theorem checked_joined_trace_gate_balance
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad) (wire : Nat → Quad)
    (externalUses externalYields : List Nat)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hledger : CheckedGateAddressLedger.check
      (joinedCells certificate island) externalUses externalYields = true) :
    let physical := traceWithExternal (joinedCells certificate island) wire
      externalUses externalYields
    balanced (nativeRows physical) physical.externalUses
      physical.externalYields := by
  change balanced
    (nativeRows (trace (joinedCells certificate island) wire))
    (wireEvents wire externalUses) (wireEvents wire externalYields)
  exact checked_joined_decoded_gate_balance sourceBytes normalizedBytes
    certificate island values wire externalUses externalYields
    hcheck hisland hledger

end S31.Functional.Correspondence.CheckedDecodedGateLedgerCorrespondence
