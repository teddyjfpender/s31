import S31.Gadgets.Functional.Correspondence.CheckedFullLocalArithmeticComposition

/-!
The source/public honest wire and the separately checked constant island
share eight fixed addresses. This module proves exact agreement there and
proves that every projected gate port lies below the island's fresh address
range. It does not identify modeled columns with native commitments.
-/

namespace S31.Functional.Correspondence.HonestConstantIslandAgreement

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAirRows
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.Correspondence.SyntheticSourceTraceCompletion
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.HonestPublicBoundaryWire
open S31.Functional.Correspondence.AcceptedPublicPhysicalTrace
open S31.Functional.Correspondence.NativeConstantIslandCertificate
open S31.Functional.Correspondence.CheckedFullLocalArithmeticComposition

private theorem trace_indices {initial final : List Lanes}
    {instructions : List Instruction}
    (htrace : AcceptsTrace initial instructions final) :
    ∀ instruction ∈ instructions,
      instruction.lhs < final.length ∧
      instruction.rhs < final.length ∧
      instruction.id < final.length := by
  induction htrace with
  | done => simp
  | @next values final instruction rest output hrow hrest ih =>
      have hlen : (values ++ [output]).length ≤ final.length := by
        have hsize := accepted_trace_length hrest
        omega
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        obtain ⟨_, _, hid, hleft, hright, _⟩ := hrow
        have hl := (List.getElem?_eq_some_iff.mp hleft).1
        have hr := (List.getElem?_eq_some_iff.mp hright).1
        simp only [List.length_append, List.length_singleton] at hlen
        omega
      · exact ih item htail

/-- Source cells cannot refer to constant-island fresh addresses. -/
theorem source_ports_below_island (certificate : Certificate)
    (input : Lanes) {final : List Lanes}
    (htrace : AcceptsTrace [input] certificate.instructions final) :
    ∀ cell ∈ expectedCells certificate (compiledAddRows certificate),
      cell.in0 < 33 + certificate.instructions.length ∧
      cell.in1 < 33 + certificate.instructions.length ∧
      cell.out < 33 + certificate.instructions.length := by
  intro cell hcell
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hcell
  have hinstruction : pair.1 ∈ certificate.instructions :=
    (List.of_mem_zip hpair).1
  have hids := trace_indices htrace pair.1 hinstruction
  have hlen := accepted_trace_length htrace
  simp only [List.length_singleton] at hlen
  have hshape := (expected_rows_opcode_and_addresses certificate
    (compiledAddRows certificate)) pair hpair
  simp only [expectedCell, hshape.2.2.1, hshape.2.2.2.1,
    hshape.2.2.2.2, address] at *
  omega

/-- Every public pack/unpack cell port remains in the reserved data-wire
range, including the selected SSA output source address. -/
theorem public_ports_below_island (certificate : Certificate)
    (houtput : certificate.output < 1 + certificate.instructions.length) :
    ∀ cell ∈ expectedInputCells certificate (compiledAddRows certificate) ++
        expectedOutputCells certificate (compiledAddRows certificate),
      cell.in0 < 33 + certificate.instructions.length ∧
      cell.in1 < 33 + certificate.instructions.length ∧
      cell.out < 33 + certificate.instructions.length := by
  intro cell hcell
  simp only [expectedInputCells, expectedOutputCells,
    expectedMaskCells, List.mem_append] at hcell
  rcases hcell with hinput | houtputCell
  · rcases hinput with ((hpackAdd | hpackMul) | hcopy) | hself
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpackAdd
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;> simp [expectedPackAddCell] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hpackMul
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;> simp [expectedPackMulCell, maskBasisAddress] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;> simp [expectedInputCopyCell] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hself
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;> simp [expectedInputSelfCell] <;> omega
  · rcases houtputCell with (hmask | hinverse) | hcopy
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hmask
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedMaskCell, address, maskAddress,
          maskBasisAddress] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hinverse
      have hii : i < 3 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedInverseCell, maskAddress, resultAddress] <;> omega
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hcopy
      have hii : i < 4 := List.mem_range.mp hi
      interval_cases i <;>
        simp [expectedCopyCell, resultAddress] <;> omega

theorem projected_ports_below_island (certificate : Certificate)
    (input : Lanes) {final : List Lanes}
    (htrace : AcceptsTrace [input] certificate.instructions final)
    (houtput : certificate.output < 1 + certificate.instructions.length) :
    ∀ cell ∈ projectedCells certificate,
      cell.in0 < 33 + certificate.instructions.length ∧
      cell.in1 < 33 + certificate.instructions.length ∧
      cell.out < 33 + certificate.instructions.length := by
  intro cell hcell
  rcases List.mem_append.mp hcell with hsource | hpublic
  · exact source_ports_below_island certificate input htrace cell hsource
  · exact public_ports_below_island certificate houtput cell hpublic

/-- The honest wire and the checked constant value table coincide at each
of the eight addresses deliberately shared with projected gates. -/
theorem honest_seed_values (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (values : List Quad)
    (hlen : final.length = 1 + certificate.instructions.length)
    (hseed : SeedValues certificate values) :
    ∀ address,
      constantAddress certificate address →
      address < 33 + certificate.instructions.length →
      extendedWire input output final term1 term2 term3 sum1 sum2 address =
        wireOfValues values address := by
  rcases hseed with ⟨h0, h1, h2, h15, h16, h25, h28, h31⟩
  intro a haddress hbelow
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hhigh
  · simp [extendedWire_lower, lowerValue, wireOfValues, h0]
  · simp [extendedWire_lower, lowerValue, wireOfValues, h1]
  · simp [extendedWire_lower, lowerValue, wireOfValues, h2]
  · simp [extendedWire_lower, lowerValue, wireOfValues, h15]
  · simp [extendedWire_lower, lowerValue, wireOfValues, h16]
  · have ha : 25 + certificate.instructions.length =
        22 + final.length + 2 := by omega
    calc
      extendedWire input output final term1 term2 term3 sum1 sum2
          (25 + certificate.instructions.length) = upperValue output 2 := by
            rw [ha, extendedWire_upper]
      _ = wireOfValues values (25 + certificate.instructions.length) := by
        simp [upperValue, wireOfValues, h25]
  · have ha : 28 + certificate.instructions.length =
        22 + final.length + 5 := by omega
    calc
      extendedWire input output final term1 term2 term3 sum1 sum2
          (28 + certificate.instructions.length) = upperValue output 5 := by
            rw [ha, extendedWire_upper]
      _ = wireOfValues values (28 + certificate.instructions.length) := by
        simp [upperValue, wireOfValues, h28]
  · have ha : 31 + certificate.instructions.length =
        22 + final.length + 8 := by omega
    calc
      extendedWire input output final term1 term2 term3 sum1 sum2
          (31 + certificate.instructions.length) = upperValue output 8 := by
            rw [ha, extendedWire_upper]
      _ = wireOfValues values (31 + certificate.instructions.length) := by
        simp [upperValue, wireOfValues, h31]
  · omega

/-- A concrete honest source/public wire fulfills the exact compatibility
premise used to join independently checked projected and constant cells.
No arbitrary wire agreement is assumed. -/
theorem honest_extended_shared_agreement (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (term1 term2 term3 sum1 sum2 : Quad) (values : List Quad)
    (htrace : AcceptsTrace [input] certificate.instructions final)
    (hselected : final[certificate.output]? = some output)
    (hseed : SeedValues certificate values) :
    SharedAgreement certificate
      (extendedWire input output final term1 term2 term3 sum1 sum2) values := by
  have hlen := accepted_trace_length htrace
  simp only [List.length_singleton] at hlen
  have houtput : certificate.output < 1 + certificate.instructions.length := by
    have h := (List.getElem?_eq_some_iff.mp hselected).1
    omega
  have hports := projected_ports_below_island certificate input htrace houtput
  have hseeds := honest_seed_values certificate input output final
    term1 term2 term3 sum1 sum2 values hlen hseed
  intro cell hcell address hport hconstant
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).1)
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).2.1)
  rcases List.mem_singleton.mp hport with ha
  exact hseeds address hconstant (ha ▸ (hports cell hcell).2.2)

/-- The public boundary contracts themselves pin every shared seed. Thus
the agreement proof applies to any honest boundary witness, including the
constructed `extendedWire`, without inspecting its internal representation. -/
theorem boundary_seed_values (certificate : Certificate)
    (wire : Nat → Quad) (input output : Lanes) (values : List Quad)
    (hinput : InputBoundary certificate (compiledAddRows certificate) wire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate) wire output)
    (hunit : wire 1 = unit ⟨0, by decide⟩)
    (hseed : SeedValues certificate values) :
    ∀ address,
      constantAddress certificate address →
      address < 33 + certificate.instructions.length →
      wire address = wireOfValues values address := by
  rcases hseed with ⟨h0, h1, h2, h15, h16, h25, h28, h31⟩
  intro a haddress hbelow
  rcases haddress with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hhigh
  · simpa [wireOfValues, h0] using hinput.zero
  · simpa [wireOfValues, h1] using hunit
  · simpa [wireOfValues, h2] using hinput.basis2
  · simpa [wireOfValues, h15] using hinput.basis1
  · simpa [wireOfValues, h16] using hinput.basis3
  · simpa [expectedInverseCell, wireOfValues, h25] using
      houtput.inverseBasis ⟨0, by decide⟩
  · have h := houtput.inverseBasis ⟨1, by decide⟩
    have ha : (expectedInverseCell certificate
        (compiledAddRows certificate) 1).in1 =
        28 + certificate.instructions.length := by
      simp [expectedInverseCell]; omega
    rw [ha] at h
    simpa [wireOfValues, h28] using h
  · have h := houtput.inverseBasis ⟨2, by decide⟩
    have ha : (expectedInverseCell certificate
        (compiledAddRows certificate) 2).in1 =
        31 + certificate.instructions.length := by
      simp [expectedInverseCell]; omega
    rw [ha] at h
    simpa [wireOfValues, h31] using h
  · omega

/-- Byte admission supplies an honest execution from which the source-port
bounds follow. The selected output bound is already checked independently. -/
theorem checked_projected_ports_below_island
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∀ cell ∈ projectedCells certificate,
      cell.in0 < 33 + certificate.instructions.length ∧
      cell.in1 < 33 + certificate.instructions.length ∧
      cell.out < 33 + certificate.instructions.length := by
  let input : Lanes := fun _ => 0
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hcheck
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hcheck
    | some parsed => exact ⟨parsed, rfl⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input hcheck]
    exact hdenotation
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have htrace : AcceptsTrace [input] certificate.instructions final :=
        executing_trace_has_air_rows certificate.instructions [input] final hrun
      have houtput := AcceptedPublicFixedCells.checked_selected_output_id_bound
        sourceBytes normalizedBytes certificate hcheck
      exact projected_ports_below_island certificate input htrace houtput

/-- No caller-supplied agreement premise is needed: admitted source bytes
bound every projected port, and the public boundary plus the island checker
pin every overlapping seed value. -/
theorem checked_boundary_shared_agreement
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (wire : Nat → Quad) (input output : Lanes) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hinput : InputBoundary certificate (compiledAddRows certificate) wire input)
    (houtput : OutputBoundary certificate (compiledAddRows certificate) wire output)
    (hunit : wire 1 = unit ⟨0, by decide⟩)
    (hseed : SeedValues certificate values) :
    SharedAgreement certificate wire values := by
  have hports := checked_projected_ports_below_island
    sourceBytes normalizedBytes certificate hcheck
  have hseeds := boundary_seed_values certificate wire input output values
    hinput houtput hunit hseed
  intro cell hcell address hport hconstant
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).1)
  rcases List.mem_cons.mp hport with ha | hport
  · exact hseeds address hconstant (ha ▸ (hports cell hcell).2.1)
  rcases List.mem_singleton.mp hport with ha
  exact hseeds address hconstant (ha ▸ (hports cell hcell).2.2)

/-- From exact byte admission and a checked constant island alone, construct
a complete modeled 512-row direct-Gate trace with every fixed cell, row, and
local arithmetic root accounted for. The source/public/island shared-address
premise of the composition theorem is discharged, not passed by the caller.
This remains a synthetic trace; native commitment binding and Gate lookup
balance are independent obligations. -/
theorem checked_direct_joined_local_arithmetic_no_agreement
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes) (island : List ColumnCell) (values : List Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hisland : NativeConstantIslandCertificate.check certificate island values = true) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      denotation sourceBytes input = some output ∧
      (joinedCells certificate island).length = 512 ∧
      (∀ row : Fin 512, ∃ cell ∈ joinedCells certificate island,
        cell.traceRow = row.val) ∧
      (∀ cell ∈ joinedCells certificate island,
        fixedMatches (trace (joinedCells certificate island) wire) cell) ∧
      allArithmeticRootsZero (trace (joinedCells certificate island) wire) ∧
      wire (address certificate.output) = packM31 output ∧
      InputBoundary certificate (compiledAddRows certificate) wire input := by
  have hseed : SeedValues certificate values :=
    (NativeConstantIslandCertificate.check_sound certificate island values
      hisland).2.2.2.1
  have hagrees : ∀ projectedWire : Nat → Quad,
      S31.Functional.SSANativePolynomialRows.nativePolynomialRows
        certificate projectedWire →
      InputBoundary certificate (compiledAddRows certificate)
        projectedWire input →
      ∀ output : Lanes,
      OutputBoundary certificate (compiledAddRows certificate)
        projectedWire output →
      SharedAgreement certificate projectedWire values := by
    intro projectedWire _ hinput output houtput
    have hunit : projectedWire 1 = unit ⟨0, by decide⟩ := by
      simpa [maskBasisAddress] using houtput.maskBasis ⟨0, by decide⟩
    exact checked_boundary_shared_agreement sourceBytes normalizedBytes
      certificate projectedWire input output values hcheck hinput houtput
      hunit hseed
  exact checked_direct_joined_local_arithmetic_exists
    sourceBytes normalizedBytes certificate input island values
    hcheck hisland hagrees

end S31.Functional.Correspondence.HonestConstantIslandAgreement
