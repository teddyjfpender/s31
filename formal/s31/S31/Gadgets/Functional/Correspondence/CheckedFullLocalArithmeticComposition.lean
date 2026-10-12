import S31.Gadgets.Functional.Correspondence.AcceptedPublicFixedCells
import S31.Gadgets.Functional.Correspondence.NativeConstantIslandCertificate
import S31.Gadgets.Functional.SSAProjectedRowCompleteness

/-!
Join the byte-admitted source/public arithmetic witness to a checked
constant-island certificate. The two independently constructed value maps
must agree wherever a projected gate reads or writes a constant address.
The theorem constructs one 512-row local-arithmetic trace, but does not
authenticate it against a native commitment or prove Gate lookup balance.
-/

namespace S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAProjectedRowCompleteness
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.HonestPublicBoundaryWire
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.FullDirectGateRowRoles
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

private def addIslandRows (certificate : Certificate) : List Nat :=
  let a := sourceAddCount certificate
  let A := compiledAddRows certificate
  (List.range (A - (11 + a))).map (11 + a + ·)

private def mulIslandRows (certificate : Certificate) : List Nat :=
  (List.range 21).map (compiledAddRows certificate + 7 + ·)

private theorem add_island_band (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16)
    (row : Nat) (hrow : row ∈ addIslandRows certificate) :
    11 + sourceAddCount certificate ≤ row ∧
      row < compiledAddRows certificate := by
  obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hrow
  have hi := List.mem_range.mp hindex
  have hspace := constant_add_start_bounded certificate hbudget
  omega

private theorem mul_island_band (certificate : Certificate)
    (row : Nat) (hrow : row ∈ mulIslandRows certificate) :
    compiledAddRows certificate + 7 ≤ row ∧
      row < compiledAddRows certificate + 28 := by
  obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hrow
  have hi := List.mem_range.mp hindex
  omega

theorem constant_positions_nodup (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) :
    (constantPositions certificate).Nodup := by
  have hadd : (addIslandRows certificate).Nodup := by
    unfold addIslandRows
    exact (List.nodup_map_iff (fun x y (_ : 11 + sourceAddCount certificate + x =
      11 + sourceAddCount certificate + y) => by omega)).2 List.nodup_range
  have hmul : (mulIslandRows certificate).Nodup := by
    unfold mulIslandRows
    exact (List.nodup_map_iff (fun x y (_ : compiledAddRows certificate + 7 + x =
      compiledAddRows certificate + 7 + y) => by omega)).2 List.nodup_range
  change (addIslandRows certificate ++ [compiledAddRows certificate] ++
    mulIslandRows certificate).Nodup
  have hleft : (addIslandRows certificate ++
      [compiledAddRows certificate]).Nodup := by
    apply List.Nodup.append hadd (by simp)
    intro row haddRow hsingle
    have hband := add_island_band certificate hbudget row haddRow
    simp only [List.mem_singleton] at hsingle
    omega
  apply List.Nodup.append hleft hmul
  intro row hleftRow hmulRow
  have hmulBand := mul_island_band certificate row hmulRow
  rcases List.mem_append.mp hleftRow with haddRow | hsingle
  · have haddBand := add_island_band certificate hbudget row haddRow
    omega
  · simp only [List.mem_singleton] at hsingle
    omega

private def PublicBand (certificate : Certificate) (row : Nat) : Prop :=
  row < 3 ∨
  (3 + sourceAddCount certificate ≤ row ∧
    row < 11 + sourceAddCount certificate) ∨
  (compiledAddRows certificate + 1 ≤ row ∧
    row < compiledAddRows certificate + 7) ∨
  (compiledAddRows certificate + 28 + sourceMulCount certificate ≤ row ∧
    row < compiledAddRows certificate + 36 + sourceMulCount certificate)

private theorem projected_public_band (certificate : Certificate) :
    ∀ cell ∈ expectedInputCells certificate (compiledAddRows certificate) ++
        expectedOutputCells certificate (compiledAddRows certificate),
      PublicBand certificate cell.traceRow := by
  intro cell hcell
  simp only [expectedInputCells, expectedOutputCells, expectedMaskCells,
    List.mem_append] at hcell
  rcases hcell with hinput | houtput
  · rcases hinput with hpre | hself
    · rcases hpre with hpre | hcopy
      · rcases hpre with hpackAdd | hpackMul
        · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hpackAdd
          subst cell
          have hi := List.mem_range.mp hindex
          simp [PublicBand, expectedPackAddCell]
          omega
        · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hpackMul
          subst cell
          have hi := List.mem_range.mp hindex
          simp [PublicBand, expectedPackMulCell]
          omega
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hcopy
        subst cell
        have hi := List.mem_range.mp hindex
        simp [PublicBand, expectedInputCopyCell]
        omega
    · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hself
      subst cell
      have hi := List.mem_range.mp hindex
      simp [PublicBand, expectedInputSelfCell]
      omega
  · rcases houtput with hpre | hcopy
    · rcases hpre with hmask | hinverse
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hmask
        subst cell
        have hi := List.mem_range.mp hindex
        simp [PublicBand, expectedMaskCell]
        omega
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hinverse
        subst cell
        have hi := List.mem_range.mp hindex
        simp [PublicBand, expectedInverseCell]
        omega
    · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hcopy
      subst cell
      have hi := List.mem_range.mp hindex
      simp [PublicBand, expectedCopyCell]
      omega

/-- Any bounded source/public row projection is disjoint from the
source-independent constant island. The conclusion depends on the admitted
producer budget, rather than on a particular spelling of the source. -/
theorem projected_constant_rows_disjoint_of_budget
    (certificate : Certificate)
    (hbudget : certificate.instructions.length ≤ 16) :
    List.Disjoint ((projectedCells certificate).map ColumnCell.traceRow)
      (constantPositions certificate) := by
  intro row hprojected hconstant
  have hspace := constant_add_start_bounded certificate hbudget
  have hconstantBand := constant_position_band certificate hbudget
    row hconstant
  obtain ⟨cell, hcell, hrow⟩ := List.mem_map.mp hprojected
  rcases List.mem_append.mp hcell with hsource | hpublic
  · have hsourceRow : cell.traceRow ∈
        (expectedRows certificate (compiledAddRows certificate)).map
          NativeSourceRow.traceRow := by
      rw [← expected_cells_trace_rows_eq]
      exact List.mem_map_of_mem hsource
    obtain ⟨sourceRow, hsourceMember, hsourceEq⟩ :=
      List.mem_map.mp hsourceRow
    have hsourceBand := expected_rows_partition certificate
      (compiledAddRows certificate) sourceRow hsourceMember
    cases hkind : sourceRow.multiply <;>
      simp [hkind] at hsourceBand <;> omega
  · have hpublicBand := projected_public_band certificate cell hpublic
    unfold PublicBand at hpublicBand
    rcases hpublicBand with h | h | h | h <;> omega

/-- Direct byte admission supplies the producer budget for the structural
projection/island disjointness theorem. -/
theorem projected_constant_rows_disjoint
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    List.Disjoint ((projectedCells certificate).map ColumnCell.traceRow)
      (constantPositions certificate) :=
  projected_constant_rows_disjoint_of_budget certificate
    (checked_relation_instruction_bound sourceBytes normalizedBytes
      certificate hcheck)

def joinedCells (certificate : Certificate) (island : List ColumnCell) :
    List ColumnCell := projectedCells certificate ++ island

theorem checked_joined_cells_length
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    (joinedCells certificate island).length = 512 := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hcheck
  have hislandLength := (checked_rows_count certificate island values
    hbudget hisland).2
  have hprojectedLength : (projectedCells certificate).length =
      certificate.instructions.length + 25 := by
    simp [projectedCells, expectedInputCells, expectedOutputCells,
      expectedMaskCells, expected_cells_length]
  simp only [joinedCells, List.length_append]
  omega

/-- The checked island and the checked source/public projection occupy 512
distinct, in-bounds physical positions. Hence every physical row 0..511 has
exactly one modeled cell. This is a roster theorem, independent of values. -/
theorem checked_joined_roster_complete
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ((joinedCells certificate island).map ColumnCell.traceRow).Nodup ∧
    (∀ cell ∈ joinedCells certificate island, cell.traceRow < 512) ∧
    (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
      cell.traceRow = row.val) := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hcheck
  have hconstRows := (check_sound certificate island values hisland).1
  have hprojected := direct_bytes_projected_roster sourceBytes
    normalizedBytes certificate hcheck
  have hnodup : ((joinedCells certificate island).map
      ColumnCell.traceRow).Nodup := by
    have hislandNodup : (island.map ColumnCell.traceRow).Nodup := by
      rw [hconstRows]
      exact constant_positions_nodup certificate hbudget
    have hdisjoint : List.Disjoint
        ((projectedCells certificate).map ColumnCell.traceRow)
        (island.map ColumnCell.traceRow) := by
      rw [hconstRows]
      exact projected_constant_rows_disjoint sourceBytes normalizedBytes
        certificate hcheck
    simpa [joinedCells, projectedCells, List.map_append] using
      hprojected.2.1.append hislandNodup hdisjoint
  have hbound : ∀ cell ∈ joinedCells certificate island,
      cell.traceRow < 512 := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojectedCell | hislandCell
    · have h := hprojected.2.2 cell (by simpa [projectedCells] using hprojectedCell)
      norm_num at h
      exact h
    · have hrow : cell.traceRow ∈ constantPositions certificate := by
        rw [← hconstRows]
        exact List.mem_map_of_mem hislandCell
      have hband := constant_position_band certificate hbudget
        cell.traceRow hrow
      have hA : compiledAddRows certificate ≤ 476 := by
        unfold compiledAddRows
        omega
      rcases hband with h | h | h <;> omega
  have hlen := checked_joined_cells_length sourceBytes normalizedBytes
    certificate island values hcheck hisland
  let rows := (joinedCells certificate island).map ColumnCell.traceRow
  have hsubset : rows.toFinset ⊆ Finset.range 512 := by
    intro row hrow
    have hmem : row ∈ rows := List.mem_toFinset.mp hrow
    obtain ⟨cell, hcell, heq⟩ := List.mem_map.mp hmem
    exact Finset.mem_range.mpr (by simpa [rows] using
      (heq ▸ hbound cell hcell))
  have hcard : rows.toFinset.card = (Finset.range 512).card := by
    rw [List.toFinset_card_of_nodup (by simpa [rows] using hnodup)]
    simp [rows, hlen]
  have heq : rows.toFinset = Finset.range 512 :=
    Finset.eq_of_subset_of_card_le hsubset hcard.symm.le
  refine ⟨hnodup, hbound, ?_⟩
  intro row
  have hmem : row.val ∈ rows := List.mem_toFinset.mp
    (heq.symm ▸ Finset.mem_range.mpr row.isLt)
  obtain ⟨cell, hcell, hrow⟩ := List.mem_map.mp hmem
  exact ⟨cell, hcell, hrow⟩

/-- On the synthesized decoded trace, every one of the 512 selected fixed
cells has the checked one-hot selector, addresses and multiplicity at its
unique physical row. Native preprocessed commitment equality is separate. -/
theorem checked_joined_fixed_matches
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (island : List ColumnCell) (values : List Quad) (wire : Nat → Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ∀ cell ∈ joinedCells certificate island,
      fixedMatches (trace (joinedCells certificate island) wire) cell := by
  have hroster := checked_joined_roster_complete sourceBytes normalizedBytes
    certificate island values hcheck hisland
  have hcanonical : ∀ cell ∈ joinedCells certificate island,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojected | hislandCell
    · exact AcceptedPublicFixedCells.projected_cells_canonical
        sourceBytes normalizedBytes certificate hcheck cell hprojected
    · have hsound := checked_cells_sound certificate island values
        hisland cell hislandCell
      rcases hsound with ⟨_, _, _, _, _, _, _, h0, h1, ho, hm, _⟩
      exact ⟨h0, h1, ho, hm⟩
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    zeroTrace_fixed (joinedCells certificate island) hroster.1
      hroster.2.1 hcanonical [] cell hcell
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [trace, row] using hflags
  · simpa [trace, row] using hin0
  · simpa [trace, row] using hin1
  · simpa [trace, row] using hout
  · simpa [trace, row] using hmult

def mergedWire (certificate : Certificate) (projectedWire : Nat → Quad)
    (values : List Quad) (address : Nat) : Quad :=
  if constantAddress certificate address then wireOfValues values address
  else projectedWire address

/-- The selected SSA result is below the fresh constant island allocation
and distinct from every reserved seed, basis, or inverse address. -/
theorem checked_selected_output_not_constant
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ¬ constantAddress certificate (address certificate.output) := by
  have houtput := AcceptedPublicFixedCells.checked_selected_output_id_bound
    sourceBytes normalizedBytes certificate hcheck
  simp only [constantAddress, address]
  omega

/-- The exact interface obligation between independently obtained source and
constant witnesses. It mentions only projected cells' three circuit ports. -/
def SharedAgreement (certificate : Certificate) (projectedWire : Nat → Quad)
    (values : List Quad) : Prop :=
  ∀ cell ∈ projectedCells certificate,
    ∀ address ∈ [cell.in0, cell.in1, cell.out],
      constantAddress certificate address →
        projectedWire address = wireOfValues values address

private theorem merged_projected_port (certificate : Certificate)
    (projectedWire : Nat → Quad) (values : List Quad)
    (hagrees : SharedAgreement certificate projectedWire values)
    (cell : ColumnCell) (hcell : cell ∈ projectedCells certificate)
    (address : Nat) (hport : address ∈ [cell.in0, cell.in1, cell.out]) :
    mergedWire certificate projectedWire values address =
      projectedWire address := by
  by_cases hconstant : constantAddress certificate address
  · simp [mergedWire, hconstant,
      (hagrees cell hcell address hport hconstant).symm]
  · simp [mergedWire, hconstant]

private theorem merged_island_port (certificate : Certificate)
    (projectedWire : Nat → Quad) (values : List Quad)
    (address : Nat) (hconstant : constantAddress certificate address) :
    mergedWire certificate projectedWire values address =
      wireOfValues values address := by
  simp [mergedWire, hconstant]

/-- The constant island can overwrite the public-input prefix only at the
checked zero and basis seeds. The public input boundary already pins those
values, so the merged witness retains every address used by that boundary. -/
theorem merged_input_prefix (certificate : Certificate)
    (projectedWire : Nat → Quad) (values : List Quad) (input : Lanes)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      projectedWire input)
    (hseed : SeedValues certificate values) (a : Nat)
    (ha : a < 23) (hone : a ≠ 1) :
    mergedWire certificate projectedWire values a = projectedWire a := by
  by_cases hc : constantAddress certificate a
  · rcases hc with rfl | rfl | rfl | rfl | rfl | h25 | h28 | h31 | hhigh
    · simpa [mergedWire, constantAddress, wireOfValues, hseed.1] using
        hinput.zero.symm
    · exact False.elim (hone rfl)
    · simpa [mergedWire, constantAddress, wireOfValues, hseed.2.2.1] using
        hinput.basis2.symm
    · simpa [mergedWire, constantAddress, wireOfValues, hseed.2.2.2.1] using
        hinput.basis1.symm
    · simpa [mergedWire, constantAddress, wireOfValues, hseed.2.2.2.2.1] using
        hinput.basis3.symm
    · omega
    · omega
    · omega
    · omega
  · simp [mergedWire, hc]

/-- The full modeled wire preserves the complete public input contract,
including scalar pins and six local pack rows, under the island seed check. -/
theorem merged_input_boundary (certificate : Certificate)
    (projectedWire : Nat → Quad) (values : List Quad) (input : Lanes)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      projectedWire input)
    (hseed : SeedValues certificate values) :
    InputBoundary certificate (compiledAddRows certificate)
      (mergedWire certificate projectedWire values) input := by
  have heq (a : Nat) (ha : a < 23) (hone : a ≠ 1) :=
    merged_input_prefix certificate projectedWire values input hinput hseed
      a ha hone
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [heq 0 (by omega) (by omega)] using hinput.zero
  · intro i
    have hi := i.isLt
    have hrow := hinput.copies i
    change accepts (encode .add) (projectedWire (11 + i.val))
      (projectedWire 0) (projectedWire (3 + i.val)) at hrow
    change accepts (encode .add)
      (mergedWire certificate projectedWire values (11 + i.val))
      (mergedWire certificate projectedWire values 0)
      (mergedWire certificate projectedWire values (3 + i.val))
    simpa only [heq (11 + i.val) (by omega) (by omega),
      heq 0 (by omega) (by omega),
      heq (3 + i.val) (by omega) (by omega)] using hrow
  · intro i
    have hi := i.isLt
    simpa only [heq (3 + i.val) (by omega) (by omega)] using
      hinput.pins i
  · simpa only [heq 15 (by omega) (by omega)] using hinput.basis1
  · simpa only [heq 2 (by omega) (by omega)] using hinput.basis2
  · simpa only [heq 16 (by omega) (by omega)] using hinput.basis3
  · intro i
    have hi := i.isLt
    have hmask : maskBasisAddress (i.val + 1) < 23 ∧
        maskBasisAddress (i.val + 1) ≠ 1 := by
      fin_cases i <;> decide
    have hrow := hinput.packMuls i
    change accepts (encode .mul)
      (projectedWire (maskBasisAddress (i.val + 1)))
      (projectedWire (12 + i.val))
      (projectedWire (17 + 2 * i.val)) at hrow
    change accepts (encode .mul)
      (mergedWire certificate projectedWire values
        (maskBasisAddress (i.val + 1)))
      (mergedWire certificate projectedWire values (12 + i.val))
      (mergedWire certificate projectedWire values (17 + 2 * i.val))
    simpa only [heq _ hmask.1 hmask.2,
      heq (12 + i.val) (by omega) (by omega),
      heq (17 + 2 * i.val) (by omega) (by omega)] using hrow
  · intro i
    have hi := i.isLt
    have hfirst : (if i.val == 0 then 11 else 16 + 2 * i.val) < 23 ∧
        (if i.val == 0 then 11 else 16 + 2 * i.val) ≠ 1 := by
      fin_cases i <;> decide
    have hrow := hinput.packAdds i
    change accepts (encode .add)
      (projectedWire (if i.val == 0 then 11 else 16 + 2 * i.val))
      (projectedWire (17 + 2 * i.val))
      (projectedWire (18 + 2 * i.val)) at hrow
    change accepts (encode .add)
      (mergedWire certificate projectedWire values
        (if i.val == 0 then 11 else 16 + 2 * i.val))
      (mergedWire certificate projectedWire values (17 + 2 * i.val))
      (mergedWire certificate projectedWire values (18 + 2 * i.val))
    simpa only [heq _ hfirst.1 hfirst.2,
      heq (17 + 2 * i.val) (by omega) (by omega),
      heq (18 + 2 * i.val) (by omega) (by omega)] using hrow

/-- Compose one concrete honest source/public witness with a checked
constant island. The shared-port agreement is explicit and only concerns
the two independently built value assignments. -/
theorem joined_local_arithmetic_of_projected_wire
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (projectedWire : Nat → Quad) (output : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hdenotation : denotation sourceBytes input = some output)
    (hsource : nativePolynomialRows certificate projectedWire)
    (hinput : InputBoundary certificate (compiledAddRows certificate)
      projectedWire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate)
      projectedWire output)
    (hselected : projectedWire (address certificate.output) =
      S31.Gadgets.Air.Qm31Ops.packM31 output)
    (hunit : projectedWire 1 = unit ⟨0, by decide⟩)
    (hshared : SharedAgreement certificate projectedWire values) :
    ∃ wire : Nat → Quad,
      denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input := by
  let wire := mergedWire certificate projectedWire values
  have hprojected : ∀ cell ∈ projectedCells certificate,
      cellAccepts cell projectedWire :=
    projected_cells_accept certificate projectedWire input output
      hsource hinput houtput hunit
  have hislandAccept : ∀ cell ∈ island,
      cellAccepts cell (wireOfValues values) :=
    checked_cells_arithmetic certificate island values hisland
  have hjoined : ∀ cell ∈ joinedCells certificate island,
      cellAccepts cell wire := by
    intro cell hcell
    rcases List.mem_append.mp hcell with hprojectedCell | hislandCell
    · have h0 := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.in0 (by simp)
      have h1 := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.in1 (by simp)
      have ho := merged_projected_port certificate projectedWire values
        hshared cell hprojectedCell cell.out (by simp)
      simpa only [wire, cellAccepts, h0, h1, ho] using
        hprojected cell hprojectedCell
    · have hsound := checked_cells_sound certificate island values
        hisland cell hislandCell
      have h0 := merged_island_port certificate projectedWire values
        cell.in0 hsound.2.1
      have h1 := merged_island_port certificate projectedWire values
        cell.in1 hsound.2.2.1
      have ho := merged_island_port certificate projectedWire values
        cell.out hsound.2.2.2.1
      simpa only [wire, cellAccepts, h0, h1, ho] using
        hislandAccept cell hislandCell
  have hjoinedLength := checked_joined_cells_length sourceBytes
    normalizedBytes certificate island values hcheck hisland
  have hcoverage := (checked_joined_roster_complete sourceBytes
    normalizedBytes certificate island values hcheck hisland).2.2
  have hnotconstant := checked_selected_output_not_constant
    sourceBytes normalizedBytes certificate hcheck
  have hseed : SeedValues certificate values :=
    (NativeConstantIslandCertificate.check_sound certificate island values
      hisland).2.2.2.1
  exact ⟨wire, hdenotation, hjoinedLength, hcoverage,
    checked_joined_fixed_matches sourceBytes normalizedBytes certificate
      island values wire hcheck hisland,
    arithmetic_complete (joinedCells certificate island) wire hjoined,
    by simpa [wire, mergedWire, hnotconstant] using hselected,
    merged_input_boundary certificate projectedWire values input hinput hseed⟩

/-- A byte-admitted source and checked island have a full modeled 512-row
trace whenever the island values agree with the honest public/source witness
at projected constant ports. Native fixed-column binding and Gate lookup
balance remain distinct obligations. -/
theorem checked_direct_joined_local_arithmetic_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true)
    (hagrees : ∀ projectedWire : Nat → Quad,
      nativePolynomialRows certificate projectedWire →
      InputBoundary certificate (compiledAddRows certificate) projectedWire input →
      ∀ output : Lanes,
      OutputBoundary certificate (compiledAddRows certificate) projectedWire output →
      SharedAgreement certificate projectedWire values) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) =
        S31.Gadgets.Air.Qm31Ops.packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input := by
  obtain ⟨projectedWire, output, hdenotation, hsource, hinput, houtput,
      hselected, hunit⟩ := checked_direct_public_boundary_exists
        sourceBytes normalizedBytes certificate input hcheck
  obtain ⟨wire, hdenotation, hlength, hcoverage, hfixed,
      harithmetic, hselected, hinputMerged⟩ :=
    joined_local_arithmetic_of_projected_wire sourceBytes normalizedBytes
      certificate input island values projectedWire output hcheck hisland
      hdenotation hsource hinput houtput hselected hunit
      (hagrees projectedWire hsource hinput output houtput)
  exact ⟨wire, output, hdenotation, hlength, hcoverage, hfixed,
    harithmetic, hselected, hinputMerged⟩

end S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition
