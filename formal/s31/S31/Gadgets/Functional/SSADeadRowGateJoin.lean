import S31.Gadgets.Functional.SSAInstalledBytecodePublicInput

/-!
The bounded direct-Gate byte fragment permits an earlier returned SSA value.
Such a program may have later instructions whose output multiplicity is zero.
The existing all-row Gate theorem requires every instruction to yield at least
once, so it does not cover those accepted programs.

This module joins only source rows with positive `sourceUses` to the unique
Gate producer map. All source rows still have physical installed-bytecode
roots in the premise, including zero-multiplicity rows. Source-use counting
itself makes every instruction operand positive, while four public-mask reads
make the selected output positive.
The proof remains conditional on ideal exact Gate balance, fixed cells,
physical rows, public pins, and unique producer values. It does not derive
those premises from native proof verification.
-/

namespace S31.Functional.SSADeadRowGateJoin

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAGateLookupWireMap
open S31.Functional.SSAInstalledBytecodeGateJoin
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAInstalledBytecodePublicInput

/-- A dependency property stated in terms of `sourceUses`, the exact exported
multiplicity formula. It follows for every certificate from operand counting. -/
def usedDependencies (certificate : Certificate) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    0 < sourceUses certificate instruction.id →
      0 < sourceUses certificate instruction.lhs ∧
        0 < sourceUses certificate instruction.rhs

theorem usedDependencies_of_sourceUses (certificate : Certificate) :
    usedDependencies certificate := by
  intro instruction hmember _
  exact sourceUses_operand_pos certificate instruction hmember

/-- Only values that are used later or publicly selected need a producer-map
entry. A zero-use SSA result may have a locally accepted physical row without
any Gate yield at its output address. -/
private def fitsUsed (certificate : Certificate) (wire : Nat → Quad)
    (values : List Lanes) : Prop :=
  ∀ id value, values[id]? = some value →
    0 < sourceUses certificate id → wire (address id) = packM31 value

private theorem fits_used_append (certificate : Certificate)
    (wire : Nat → Quad) (values : List Lanes) (output : Lanes)
    (hfits : fitsUsed certificate wire values)
    (houtput : 0 < sourceUses certificate values.length →
      wire (address values.length) = packM31 output) :
    fitsUsed certificate wire (values ++ [output]) := by
  intro id value hget hused
  by_cases hprior : id < values.length
  · have hget' : values[id]? = some value := by
      simpa only [List.getElem?_append_left hprior] using hget
    exact hfits id value hget' hused
  · have hbound : id < (values ++ [output]).length :=
      (List.getElem?_eq_some_iff.mp hget).1
    have hid : id = values.length := by simp at hbound; omega
    subst id
    have hvalue : value = output := by simpa using hget.symm
    subst value
    exact houtput hused

private theorem used_row_output (wire : Nat → Quad)
    (instruction : Instruction) (lhs rhs : Lanes)
    (hleft : wire (address instruction.lhs) = packM31 lhs)
    (hright : wire (address instruction.rhs) = packM31 rhs)
    (hrow : accepts (encode (s31Op instruction.multiply))
      (wire (address instruction.lhs))
      (wire (address instruction.rhs))
      (wire (address instruction.id))) :
    wire (address instruction.id) =
      packM31 (instructionValue instruction.multiply lhs rhs) := by
  rw [hleft, hright] at hrow
  exact ((accepts_encoded (s31Op instruction.multiply) _ _ _).mp hrow).trans
    (operation_packed instruction.multiply lhs rhs)

/-- Source execution may append a dead value, but later used operands and the
selected output remain correct. No arithmetic-row premise is taken for a
zero-use result. -/
private theorem used_rows_refine_execution (certificate : Certificate)
    (instructions : List Instruction) (initial final : List Lanes)
    (wire : Nat → Quad)
    (hinitial : fitsUsed certificate wire initial)
    (hdependencies : usedDependencies certificate)
    (hsubset : ∀ instruction ∈ instructions,
      instruction ∈ certificate.instructions)
    (hrows : ∀ instruction ∈ instructions,
      0 < sourceUses certificate instruction.id →
        accepts (encode (s31Op instruction.multiply))
          (wire (address instruction.lhs))
          (wire (address instruction.rhs))
          (wire (address instruction.id)))
    (hrun : instructions.foldlM executeStep initial = some final) :
    fitsUsed certificate wire final := by
  induction instructions generalizing initial with
  | nil =>
      simp only [List.foldlM_nil] at hrun
      cases hrun
      exact hinitial
  | cons instruction rest ih =>
      have hrow := hrows instruction (by simp)
      have hsource : instruction ∈ certificate.instructions :=
        hsubset instruction (by simp)
      have htail : ∀ item ∈ rest,
          0 < sourceUses certificate item.id →
            accepts (encode (s31Op item.multiply))
              (wire (address item.lhs))
              (wire (address item.rhs))
              (wire (address item.id)) := by
        intro item hmem
        exact hrows item (by simp [hmem])
      have htailSubset : ∀ item ∈ rest,
          item ∈ certificate.instructions := by
        intro item hmem
        exact hsubset item (by simp [hmem])
      simp only [List.foldlM_cons] at hrun
      cases hid : instruction.id == initial.length with
      | false =>
          have hneq : instruction.id ≠ initial.length := of_decide_eq_false hid
          simp [executeStep, hneq] at hrun
      | true =>
          have heq : instruction.id = initial.length := of_decide_eq_true hid
          cases hleft : initial[instruction.lhs]? with
          | none => simp [executeStep, heq, hleft] at hrun
          | some lhs =>
              cases hright : initial[instruction.rhs]? with
              | none => simp [executeStep, heq, hleft, hright] at hrun
              | some rhs =>
                  let output := instructionValue instruction.multiply lhs rhs
                  have hstep : executeStep initial instruction =
                      some (initial ++ [output]) := by
                    simp [executeStep, heq, hleft, hright, output]
                  rw [hstep] at hrun
                  have houtput : 0 < sourceUses certificate initial.length →
                      wire (address initial.length) = packM31 output := by
                    intro hused
                    have husedInstruction :
                        0 < sourceUses certificate instruction.id := by
                      simpa [heq] using hused
                    have hoperands := hdependencies instruction hsource
                      husedInstruction
                    rw [← heq]
                    exact used_row_output wire instruction lhs rhs
                      (hinitial instruction.lhs lhs hleft hoperands.1)
                      (hinitial instruction.rhs rhs hright hoperands.2)
                      (hrow husedInstruction)
                  exact ih (initial ++ [output])
                    (fits_used_append certificate wire initial output hinitial houtput)
                    htailSubset htail hrun

/-- Local arithmetic acceptance only for positive-use source results is
enough to determine the source-selected value. The exported join discharges
the closure and selected-use premises from the source-use formula. -/
theorem selected_wire_matches_used_rows (certificate : Certificate)
    (wire : Nat → Quad) (input output : Lanes)
    (hinput : wire (address 0) = packM31 input)
    (hdependencies : usedDependencies certificate)
    (hselected : 0 < sourceUses certificate certificate.output)
    (hrows : ∀ instruction ∈ certificate.instructions,
      0 < sourceUses certificate instruction.id →
        accepts (encode (s31Op instruction.multiply))
          (wire (address instruction.lhs))
          (wire (address instruction.rhs))
          (wire (address instruction.id)))
    (hexecute : executeNormalized certificate input = some output) :
    wire (address certificate.output) = packM31 output := by
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselectedValue : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have hstart : fitsUsed certificate wire [input] := by
        intro id value hget _
        cases id with
        | zero =>
            have hv : value = input := by simpa using hget.symm
            simpa [hv, address] using hinput
        | succ id => simp at hget
      exact used_rows_refine_execution certificate certificate.instructions
        [input] final wire hstart hdependencies
        (fun _ hmember => hmember) hrows hrun
        certificate.output output hselectedValue hselected

/-- All source rows are physically identified and locally checked, including
rows whose output multiplicity is zero. Only a positive-use row must yield an
event and thus enter the coherent Gate producer map. -/
def sourceGateBytecodeRowsAllowDead (certificate : Certificate)
    (observedCells : List ColumnCell) (rows : List Row) : Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ observedCells, ∃ row : Row,
      rows[cell.traceRow]? = some row ∧
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      row.flags = cellFlags cell ∧
      row.in0Address = cell.in0 ∧
      row.in1Address = cell.in1 ∧
      row.outAddress = cell.out ∧
      row.multiplicity = cell.mults ∧
      (0 < sourceUses certificate instruction.id → 0 < row.multiplicity) ∧
      (∀ root ∈ bytecodeArithmetic (physicalBytecodeCells cell row), root = 0)

/-- Exact Gate balance joins the physical values of each positive-use source
row to the one value at each produced address. The zero-use rows need no
output event, so they are excluded from this value induction. -/
theorem exact_gate_implies_used_rows (certificate : Certificate)
    (observedCells : List ColumnCell) (rows : List Row)
    (externalUses externalYields : List Event)
    (hphysical : sourceGateBytecodeRowsAllowDead certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields)) :
    ∀ instruction ∈ certificate.instructions,
      0 < sourceUses certificate instruction.id →
        accepts (encode (s31Op instruction.multiply))
          (wireOfProduced (allYields rows externalYields)
            (address instruction.lhs))
          (wireOfProduced (allYields rows externalYields)
            (address instruction.rhs))
          (wireOfProduced (allYields rows externalYields)
            (address instruction.id)) := by
  intro instruction hmember hused
  obtain ⟨cell, _, row, hindex, hflag0, hflag1, hflag2, hflag3,
    hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
    _, hpositive, hzero⟩ := hphysical instruction hmember
  have hrow : row ∈ rows := by
    obtain ⟨hbound, hvalue⟩ := List.getElem?_eq_some_iff.mp hindex
    rw [← hvalue]
    exact List.getElem_mem hbound
  let produced := allYields rows externalYields
  have huses := row_input_use rows externalUses row hrow
  have hread0 : (row.in0Address, row.in0) ∈ produced :=
    hbalance.mem_iff.mp huses.1
  have hread1 : (row.in1Address, row.in1) ∈ produced :=
    hbalance.mem_iff.mp huses.2
  have hyield : (row.outAddress, row.output) ∈ produced :=
    row_output_yield rows externalYields row hrow (hpositive hused)
  have hwire0 : wireOfProduced produced cell.in0 = row.in0 := by
    rw [← haddr0]
    exact wire_of_produced_event produced hunique _ _ hread0
  have hwire1 : wireOfProduced produced cell.in1 = row.in1 := by
    rw [← haddr1]
    exact wire_of_produced_event produced hunique _ _ hread1
  have hwireOut : wireOfProduced produced cell.out = row.output := by
    rw [← haddrOut]
    exact wire_of_produced_event produced hunique _ _ hyield
  have hcell := physical_bytecode_zero_implies_logical_cell cell row
    (wireOfProduced produced) hwire0 hwire1 hwireOut hzero
  have hflags : cellFlags cell = encode (s31Op instruction.multiply) := by
    cases hmul : instruction.multiply <;>
      simp [cellFlags, s31Op, encode, hmul,
        hflag0, hflag1, hflag2, hflag3]
  simpa only [cellAccepts, hflags, hin0, hin1, hout] using hcell

/-- This removes the positive-multiplicity requirement for dead source
instructions from the source-byte to selected-wire Gate join. -/
theorem checked_source_output_of_used_gate
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (observedCells : List ColumnCell)
    (input : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedCells certificate totalAddRows)
    (hphysical : sourceGateBytecodeRowsAllowDead certificate observedCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hinputYield : (address 0, packM31 input) ∈
      allYields rows externalYields) :
    observedCells = expectedCells certificate totalAddRows ∧
      ∃ output : Lanes,
        denotation sourceBytes input = some output ∧
          wireOfProduced (allYields rows externalYields)
            (address certificate.output) = packM31 output := by
  let produced := allYields rows externalYields
  let wire := wireOfProduced produced
  have hinput : wire (address 0) = packM31 input :=
    wire_of_produced_event produced hunique _ _ hinputYield
  have hrows := exact_gate_implies_used_rows certificate observedCells rows
    externalUses externalYields hphysical hbalance hunique
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hrelation
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hrelation
    | some parsed => exact ⟨parsed, by simpa [hp]⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input hrelation]
    exact hdenotation
  exact ⟨hcells, output, hdenotation,
    selected_wire_matches_used_rows certificate wire input output hinput
      (usedDependencies_of_sourceUses certificate)
      (sourceUses_selected_pos certificate) hrows hexecute⟩

/-- Public input packing and public output unpacking close the selected claim
without requiring any zero-use source result to produce a Gate event. Fixed
constant events, both physical public-boundary row families, and the ideal
Gate join remain explicit premises. -/
theorem bytecode_exact_gate_public_io_allow_dead_sound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (sourceCells inputCells outputCells : List ColumnCell)
    (input claimed : Lanes) (rows : List Row)
    (externalUses externalYields : List Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hsourceCells : sourceCells = expectedCells certificate totalAddRows)
    (hsourceRows : sourceGateBytecodeRowsAllowDead certificate sourceCells rows)
    (hinputCells : inputCells = expectedInputCells certificate totalAddRows)
    (hinputRows : physicalGateBytecodeRows inputCells rows)
    (houtputCells : outputCells = expectedOutputCells certificate totalAddRows)
    (houtputRows : physicalGateBytecodeRows outputCells rows)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hzero : (0, base 0) ∈ allYields rows externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈ allYields rows externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈ allYields rows externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈ allYields rows externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈ allYields rows externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields rows externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈
        allYields rows externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈
        allYields rows externalYields) :
    denotation sourceBytes input = some claimed := by
  have hinputYield := packed_input_yield_of_exact_gate certificate
    totalAddRows inputCells input rows externalUses externalYields
    hinputCells hinputRows hbalance hunique hzero
    hbasis1 hbasis2 hbasis3 hpublicInputPins
  obtain ⟨_, output, hsource, hselectedValue⟩ :=
    checked_source_output_of_used_gate sourceBytes normalizedBytes
      certificate totalAddRows sourceCells input rows externalUses
      externalYields hrelation hsourceCells hsourceRows hbalance hunique
      hinputYield
  have houtputBoundary := output_boundary_of_exact_gate certificate
    totalAddRows outputCells claimed rows externalUses externalYields
    houtputCells houtputRows hbalance hunique hzero hmaskBasis
    hinverseBasis hpublicOutputPins
  have hclaim : wireOfProduced (allYields rows externalYields)
      (address certificate.output) = packM31 claimed :=
    output_boundary_claim certificate totalAddRows
      (wireOfProduced (allYields rows externalYields)) claimed houtputBoundary
  have hpacked : packM31 output = packM31 claimed :=
    hselectedValue.symm.trans hclaim
  have hvalue : output = claimed := by
    funext i
    apply S31.Field.toZMod_injective
    simpa only [coord_packM31] using
      congrArg (fun q => coord q i) hpacked
  simpa only [hvalue] using hsource

end S31.Functional.SSADeadRowGateJoin
