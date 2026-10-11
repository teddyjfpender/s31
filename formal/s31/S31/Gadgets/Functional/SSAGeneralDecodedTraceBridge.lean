import S31.Gadgets.Functional.SSADeadRowGateJoin
import S31.Gadgets.Air.DirectGateEvaluatorCells

/-!
A parameterized bridge from a decoded direct-Gate trace to the bounded SSA
source, input, and output row predicates. A single trace supplies all physical
row values. The source plan associates each checked instruction with a
projected fixed cell; the exact fixed projection and installed nine
arithmetic roots are premises about that trace, not independently chosen
logical wires.

The theorem is valid for any trace log size and any byte-admitted certificate.
The bounded parser's required first arithmetic instruction proves the source
input is read. It does not establish that verifier
acceptance authenticates the trace, that
challenge-compressed LogUp implies exact Gate balance, or PCS/FRI/Fiat--Shamir
soundness. Those premises stay explicit in the final source-to-claim theorem.
-/

namespace S31.Functional.SSAGeneralDecodedTraceBridge

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.DirectGatePolynomial
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAInstalledBytecodeGateJoin
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSADeadRowGateJoin

private def finishLet (state : State) (name left : Token)
    (multiply : Bool) (rest : List Token) : Option State := do
  let (right, rest) ← takeName rest
  let rest ← expect (token ";") rest
  let lhs ← findName left state.names
  let rhs ← findName right state.names
  if lhs > rhs then none else
  let expression := (multiply, lhs, rhs)
  if state.expressions.contains expression then none else
  let instruction : Instruction :=
    { id := state.names.length, lhs, rhs, multiply }
  return {
    remaining := rest,
    names := state.names ++ [name],
    expressions := state.expressions ++ [expression],
    instructions := state.instructions ++ [instruction] }

private theorem finishLet_instructions_length (state next : State)
    (name left : Token) (multiply : Bool) (rest : List Token)
    (hfinish : finishLet state name left multiply rest = some next) :
    next.instructions.length = state.instructions.length + 1 := by
  simp [finishLet, bind, Option.bind_eq_some_iff] at hfinish
  aesop

/-- Each accepted `let` appends exactly one positional SSA instruction. -/
theorem parseLet_instructions_length (state next : State)
    (hparse : parseLet state = some next) :
    next.instructions.length = state.instructions.length + 1 := by
  simp [parseLet, bind, Option.bind_eq_some_iff] at hparse
  rcases hparse with ⟨_, _, name, _, _, _, _, _, left, operations, _, htail⟩
  cases operations with
  | nil => simp at htail
  | cons operation tail =>
      by_cases hadd : operation = token "+"
      · simp [hadd] at htail
        apply finishLet_instructions_length state next name left false tail
        simpa [finishLet, bind] using htail
      · by_cases hmul : operation = token ".*"
        · simp [hmul, token] at htail
          apply finishLet_instructions_length state next name left true tail
          simpa [finishLet, bind] using htail
        · simp [hadd, hmul] at htail

/-- Successful fuel-bounded parsing cannot append more instructions than its
fuel, regardless of the token stream or initial parser state. -/
theorem parseLetsFuel_instruction_bound (fuel : Nat) (state next : State)
    (hparse : parseLetsFuel fuel state = some next) :
    next.instructions.length ≤ state.instructions.length + fuel := by
  induction fuel generalizing state with
  | zero =>
      simp [parseLetsFuel] at hparse
      rcases hparse with ⟨_, rfl⟩
      simp
  | succ fuel ih =>
      simp only [parseLetsFuel] at hparse
      split at hparse
      · obtain ⟨middle, hstep, hrest⟩ :=
          Option.bind_eq_some_iff.mp hparse
        have hlen := parseLet_instructions_length state middle hstep
        have hbound := ih middle hrest
        omega
      · simp_all

/-- Admission of source bytes carries the parser's actual 16-instruction
budget. This does not assume an independently supplied certificate bound. -/
theorem parseBytes_instruction_bound (bytes : List Nat) (parsed : Parsed)
    (hparse : parseBytes bytes = some parsed) :
    parsed.certificate.instructions.length ≤ 16 := by
  simp [parseBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  obtain ⟨_, _, _, _, _, hparsed⟩ := hparse
  subst parsed
  have hbudget := parseLetsFuel_instruction_bound 16 _ _ (by assumption)
  simpa using hbudget

/-- The exact source/normalized-byte relation inherits the 16-instruction
limit from the successful source parser, rather than from a free premise. -/
theorem checked_relation_instruction_bound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate) :
    certificate.instructions.length ≤ 16 := by
  unfold checkRelation at hrelation
  cases hsource : parseBytes sourceBytes with
  | none => simp [hsource] at hrelation
  | some parsed =>
      cases hencoded : encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hrelation
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hrelation
            subst certificate
            exact parseBytes_instruction_bound sourceBytes parsed hsource
          · simp [hsource, hencoded, hmatch] at hrelation

def nativeRows {logSize : Nat} (trace : Trace logSize) : List Row :=
  List.ofFn (row trace)

def fixedMatches {logSize : Nat} (trace : Trace logSize)
    (cell : ColumnCell) : Prop :=
  ∃ i : Fin (2 ^ logSize), i.val = cell.traceRow ∧
    (row trace i).flags = cellFlags cell ∧
    (row trace i).in0Address = cell.in0 ∧
    (row trace i).in1Address = cell.in1 ∧
    (row trace i).outAddress = cell.out ∧
    (row trace i).multiplicity = cell.mults

def allArithmeticRootsZero {logSize : Nat} (trace : Trace logSize) : Prop :=
  ∀ i : Fin (2 ^ logSize),
    ∀ root ∈ bytecodeArithmetic (fromTrace trace i), root = 0

/-- Every source instruction has a matching projected arithmetic cell,
including a zero-use result. This predicate does not assert uniqueness. -/
def SourcePlan (certificate : Certificate) (sourceCells : List ColumnCell) :
    Prop :=
  ∀ instruction ∈ certificate.instructions,
    ∃ cell ∈ sourceCells,
      cell.addFlag = (if instruction.multiply then 0 else 1) ∧
      cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
      cell.pointwiseMulFlag = (if instruction.multiply then 1 else 0) ∧
      cell.in0 = address instruction.lhs ∧
      cell.in1 = address instruction.rhs ∧
      cell.out = address instruction.id ∧
      cell.mults = sourceUses certificate instruction.id

private def rowShape (instruction : Instruction)
    (native : NativeSourceRow) : Prop :=
  native.circuitRow = 5 + instruction.id ∧
    native.multiply = instruction.multiply ∧
    native.in0 = address instruction.lhs ∧
    native.in1 = address instruction.rhs ∧
    native.out = address instruction.id

private def emittedRow (instruction : Instruction)
    (totalAddRows priorAdds priorMuls : Nat) : NativeSourceRow :=
  { circuitRow := 5 + instruction.id,
    traceRow := if instruction.multiply then
        totalAddRows + 28 + priorMuls else 3 + priorAdds,
    multiply := instruction.multiply,
    in0 := address instruction.lhs,
    in1 := address instruction.rhs,
    out := address instruction.id }

private def emitStep (totalAddRows : Nat)
    (state : Nat × Nat × List NativeSourceRow)
    (instruction : Instruction) : Nat × Nat × List NativeSourceRow :=
  let (priorAdds, priorMuls, rows) := state
  (priorAdds + if instruction.multiply then 0 else 1,
   priorMuls + if instruction.multiply then 1 else 0,
   rows ++ [emittedRow instruction totalAddRows priorAdds priorMuls])

private theorem fold_rows_shape (totalAddRows : Nat)
    (remaining prior : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow)
    (hprior : List.Forall₂ rowShape prior rows) :
    List.Forall₂ rowShape (prior ++ remaining)
      ((remaining.foldl (emitStep totalAddRows)
        (priorAdds, priorMuls, rows)).2.2) := by
  induction remaining generalizing prior priorAdds priorMuls rows with
  | nil => simpa using hprior
  | cons instruction rest ih =>
      let newRow := emittedRow instruction totalAddRows priorAdds priorMuls
      have hnew : rowShape instruction newRow := by
        simp [rowShape, newRow, emittedRow]
      have hnext : List.Forall₂ rowShape (prior ++ [instruction])
          (rows ++ [newRow]) :=
        List.rel_append hprior (List.Forall₂.cons hnew List.Forall₂.nil)
      simpa [List.foldl_cons, emitStep, newRow, List.append_assoc] using
        (ih (prior ++ [instruction]) _ _ (rows ++ [newRow]) hnext)

/-- Within the modeled `expectedRows` schedule, each position has the
instruction's operand and output addresses, even for a zero-use result.
This lemma does not compare the schedule with native emitted rows. -/
private theorem expected_rows_shape (certificate : Certificate)
    (totalAddRows : Nat) :
    List.Forall₂ rowShape certificate.instructions
      (expectedRows certificate totalAddRows) := by
  have h := fold_rows_shape totalAddRows certificate.instructions [] 0 0 []
    List.Forall₂.nil
  have heq : expectedRows certificate totalAddRows =
      ((certificate.instructions.foldl (emitStep totalAddRows)
        (0, 0, [])).2.2) := by
    rfl
  simpa [heq] using h

private theorem forall₂_rows_plan (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ∀ instruction ∈ instructions,
      ∃ native, (instruction, native) ∈ instructions.zip rows ∧
        rowShape instruction native := by
  induction hshape with
  | nil => simp
  | @cons instruction native rest rows hrow _ ih =>
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        exact ⟨native, by simp, hrow⟩
      · obtain ⟨other, hpair, hother⟩ := ih item htail
        exact ⟨other, by simp [hpair], hother⟩

private theorem forall₂_rows_all_pairs (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ∀ pair ∈ instructions.zip rows, rowShape pair.1 pair.2 := by
  induction hshape with
  | nil => simp
  | @cons instruction native rest rows hrow _ ih =>
      intro pair hpair
      rcases List.mem_cons.mp hpair with heq | htail
      · subst pair
        exact hrow
      · exact ih pair htail

/-- The modeled source rows retain each instruction's opcode, circuit wire
position, and operand/output addresses. This is an assertion about the
`expectedRows` constructor, not about the native trace emitter. -/
theorem expected_rows_opcode_and_addresses (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ pair ∈ certificate.instructions.zip (expectedRows certificate totalAddRows),
      pair.2.circuitRow = 5 + pair.1.id ∧
      pair.2.multiply = pair.1.multiply ∧
      pair.2.in0 = address pair.1.lhs ∧
      pair.2.in1 = address pair.1.rhs ∧
      pair.2.out = address pair.1.id := by
  exact forall₂_rows_all_pairs certificate.instructions
    (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows)

private theorem forall₂_opcode_sequence (instructions : List Instruction)
    (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    rows.map NativeSourceRow.multiply =
      instructions.map Instruction.multiply := by
  induction hshape with
  | nil => rfl
  | @cons instruction native rest rows hrow _ ih =>
      simp [hrow.2.1, ih]

/-- The full modeled row opcode sequence has exactly the source's ordered
add/pointwise-multiply partition. No arithmetic selector is inferred from a
native commitment by this theorem. -/
theorem expected_rows_opcode_sequence (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedRows certificate totalAddRows).map NativeSourceRow.multiply =
      certificate.instructions.map Instruction.multiply :=
  forall₂_opcode_sequence certificate.instructions
    (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows)

private theorem forall₂_cell_opcode_flags (certificate : Certificate)
    (instructions : List Instruction) (rows : List NativeSourceRow)
    (hshape : List.Forall₂ rowShape instructions rows) :
    ((instructions.zip rows).map
      (fun pair =>
        let cell := expectedCell certificate pair.1 pair.2
        (cell.addFlag, cell.pointwiseMulFlag))) =
      instructions.map (fun instruction =>
        (if instruction.multiply then 0 else 1,
         if instruction.multiply then 1 else 0)) := by
  induction hshape with
  | nil => rfl
  | @cons instruction native rest rows _ _ ih =>
      simp only [List.zip_cons_cons, List.map_cons]
      congr 1

/-- The projected source AIR cells have exactly one add or pointwise-multiply
selector per source instruction, in source order. The remaining arithmetic
selectors are zero by `expectedCell`'s definition. -/
theorem expected_cells_opcode_flags (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedCells certificate totalAddRows).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
      certificate.instructions.map (fun instruction =>
        (if instruction.multiply then 0 else 1,
         if instruction.multiply then 1 else 0)) := by
  simpa [expectedCells, List.map_map] using
    (forall₂_cell_opcode_flags certificate certificate.instructions
      (expectedRows certificate totalAddRows)
      (expected_rows_shape certificate totalAddRows))

private def rowsWithin (totalAddRows priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow) : Prop :=
  ∀ row ∈ rows,
    if row.multiply then
      totalAddRows + 28 ≤ row.traceRow ∧
        row.traceRow < totalAddRows + 28 + priorMuls
    else
      3 ≤ row.traceRow ∧ row.traceRow < 3 + priorAdds

private theorem fold_rows_within (totalAddRows : Nat)
    (remaining : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow)
    (hwithin : rowsWithin totalAddRows priorAdds priorMuls rows) :
    let result := remaining.foldl (emitStep totalAddRows)
      (priorAdds, priorMuls, rows)
    rowsWithin totalAddRows result.1 result.2.1 result.2.2 := by
  induction remaining generalizing priorAdds priorMuls rows with
  | nil => simpa using hwithin
  | cons instruction rest ih =>
      let next := emittedRow instruction totalAddRows priorAdds priorMuls
      have hwithin' : rowsWithin totalAddRows
          (priorAdds + if instruction.multiply then 0 else 1)
          (priorMuls + if instruction.multiply then 1 else 0)
          (rows ++ [next]) := by
        intro row hmember
        rcases List.mem_append.mp hmember with hold | hnew
        · have hrange := hwithin row hold
          cases instruction.multiply <;> cases ho : row.multiply <;>
            simp [ho] at hrange ⊢ <;> omega
        · have heq : row = next := by simpa using hnew
          subst row
          cases hi : instruction.multiply <;>
            simp [next, emittedRow, hi]
      simpa [List.foldl_cons, emitStep, next] using
        (ih _ _ (rows ++ [next]) hwithin')

private theorem fold_rows_add_count (totalAddRows : Nat)
    (remaining : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow) :
    (remaining.foldl (emitStep totalAddRows)
      (priorAdds, priorMuls, rows)).1 =
      remaining.foldl (fun n instruction =>
        n + if instruction.multiply then 0 else 1) priorAdds := by
  induction remaining generalizing priorAdds priorMuls rows with
  | nil => rfl
  | cons instruction rest ih =>
      simpa [List.foldl_cons, emitStep] using
        ih (priorAdds + if instruction.multiply then 0 else 1)
          (priorMuls + if instruction.multiply then 1 else 0)
          (rows ++ [emittedRow instruction totalAddRows priorAdds priorMuls])

private theorem fold_rows_mul_count (totalAddRows : Nat)
    (remaining : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow) :
    (remaining.foldl (emitStep totalAddRows)
      (priorAdds, priorMuls, rows)).2.1 =
      remaining.foldl (fun n instruction =>
        n + if instruction.multiply then 1 else 0) priorMuls := by
  induction remaining generalizing priorAdds priorMuls rows with
  | nil => rfl
  | cons instruction rest ih =>
      simpa [List.foldl_cons, emitStep] using
        ih (priorAdds + if instruction.multiply then 0 else 1)
          (priorMuls + if instruction.multiply then 1 else 0)
          (rows ++ [emittedRow instruction totalAddRows priorAdds priorMuls])

/-- Every modeled source row lies in its actual counted native gate-kind
partition. The add and pointwise-multiply counts come from the certificate's
instructions; no separate row-count oracle is assumed. -/
theorem expected_rows_partition (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ row ∈ expectedRows certificate totalAddRows,
      if row.multiply then
        totalAddRows + 28 ≤ row.traceRow ∧
          row.traceRow < totalAddRows + 28 + sourceMulCount certificate
      else
        3 ≤ row.traceRow ∧
          row.traceRow < 3 + sourceAddCount certificate := by
  let result := certificate.instructions.foldl (emitStep totalAddRows)
    (0, 0, [])
  have hwithin : rowsWithin totalAddRows result.1 result.2.1 result.2.2 :=
    fold_rows_within totalAddRows certificate.instructions 0 0 []
      (by simp [rowsWithin])
  have hadd : result.1 = sourceAddCount certificate := by
    simpa [result, sourceAddCount] using
      fold_rows_add_count totalAddRows certificate.instructions 0 0 []
  have hmul : result.2.1 = sourceMulCount certificate := by
    simpa [result, sourceMulCount] using
      fold_rows_mul_count totalAddRows certificate.instructions 0 0 []
  simpa [expectedRows, result, rowsWithin, hadd, hmul] using hwithin

private theorem add_count_bounded (instructions : List Instruction)
    (start : Nat) :
    instructions.foldl (fun n instruction =>
      n + if instruction.multiply then 0 else 1) start ≤
      start + instructions.length := by
  induction instructions generalizing start with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have h := ih (start + if instruction.multiply then 0 else 1)
      cases hkind : instruction.multiply <;> simp [hkind] at h ⊢ <;> omega

private theorem mul_count_bounded (instructions : List Instruction)
    (start : Nat) :
    instructions.foldl (fun n instruction =>
      n + if instruction.multiply then 1 else 0) start ≤
      start + instructions.length := by
  induction instructions generalizing start with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have h := ih (start + if instruction.multiply then 1 else 0)
      cases hkind : instruction.multiply <;> simp [hkind] at h ⊢ <;> omega

theorem source_add_count_bounded (certificate : Certificate) :
    sourceAddCount certificate ≤ certificate.instructions.length := by
  simpa [sourceAddCount] using
    add_count_bounded certificate.instructions 0

theorem source_mul_count_bounded (certificate : Certificate) :
    sourceMulCount certificate ≤ certificate.instructions.length := by
  simpa [sourceMulCount] using
    mul_count_bounded certificate.instructions 0

/-- The bounded native profile has 512 arithmetic rows: `totalAddRows` add
rows, one sub row, 27 ordinary mul rows, source pointwise rows, and eight
fixed pointwise rows. Constant derivation and padding contribute hundreds of
add rows, so `totalAddRows` is *not* eleven plus the source add count.
Equality of these counts with the native emitted or committed trace remains
a separate premise. -/
theorem checked_source_rows_within_512
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hrows : totalAddRows + 1 + 27 + sourceMulCount certificate + 8 = 2 ^ 9) :
    ∀ row ∈ expectedRows certificate totalAddRows,
      row.traceRow < 2 ^ 9 := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have ha := source_add_count_bounded certificate
  have hm := source_mul_count_bounded certificate
  intro row hrow
  have hrange := expected_rows_partition certificate totalAddRows row hrow
  cases hkind : row.multiply <;> simp [hkind] at hrange <;> norm_num at hrows ⊢ <;> omega

/-- Cell projection preserves every modeled source trace position. -/
theorem expected_cells_trace_rows_eq (certificate : Certificate)
    (totalAddRows : Nat) :
    (expectedCells certificate totalAddRows).map ColumnCell.traceRow =
      (expectedRows certificate totalAddRows).map
        NativeSourceRow.traceRow := by
  have hlen := (expected_rows_shape certificate totalAddRows).length_eq
  calc
    _ = ((certificate.instructions.zip
        (expectedRows certificate totalAddRows)).map Prod.snd).map
          NativeSourceRow.traceRow := by
            simp [expectedCells, expectedCell, List.map_map]
    _ = _ := by rw [List.map_snd_zip hlen.ge]

private def publicRowBand (certificate : Certificate)
    (totalAddRows row : Nat) : Prop :=
  row < 3 ∨
  (3 + sourceAddCount certificate ≤ row ∧
    row < 11 + sourceAddCount certificate) ∨
  (totalAddRows + 1 ≤ row ∧ row < totalAddRows + 7) ∨
  (totalAddRows + 28 + sourceMulCount certificate ≤ row ∧
    row < totalAddRows + 36 + sourceMulCount certificate)

/-- The public input and output cells occupy four fixed-width ranges outside
the source add and pointwise-multiply partitions. -/
private theorem public_cells_band (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ cell ∈ expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows,
      publicRowBand certificate totalAddRows cell.traceRow := by
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
          simp [publicRowBand, expectedPackAddCell]
          omega
        · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hpackMul
          subst cell
          have hi := List.mem_range.mp hindex
          simp [publicRowBand, expectedPackMulCell]
          omega
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hcopy
        subst cell
        have hi := List.mem_range.mp hindex
        simp [publicRowBand, expectedInputCopyCell]
        omega
    · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hself
      subst cell
      have hi := List.mem_range.mp hindex
      simp [publicRowBand, expectedInputSelfCell]
      omega
  · rcases houtput with hpre | hcopy
    · rcases hpre with hmask | hinverse
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hmask
        subst cell
        have hi := List.mem_range.mp hindex
        simp [publicRowBand, expectedMaskCell]
        omega
      · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hinverse
        subst cell
        have hi := List.mem_range.mp hindex
        simp [publicRowBand, expectedInverseCell]
        omega
    · obtain ⟨index, hindex, heq⟩ := List.mem_map.mp hcopy
      subst cell
      have hi := List.mem_range.mp hindex
      simp [publicRowBand, expectedCopyCell]
      omega

/-- Source and public projected positions are disjoint if the native add
partition extends beyond the eleven source/public add rows. -/
theorem expected_source_public_rows_disjoint (certificate : Certificate)
    (totalAddRows : Nat)
    (hspace : 11 + sourceAddCount certificate ≤ totalAddRows) :
    ∀ sourceCell ∈ expectedCells certificate totalAddRows,
      ∀ publicCell ∈ expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows,
        sourceCell.traceRow ≠ publicCell.traceRow := by
  intro sourceCell hsource publicCell hpublic heq
  have hsourceRow : sourceCell.traceRow ∈
      (expectedRows certificate totalAddRows).map
        NativeSourceRow.traceRow := by
    rw [← expected_cells_trace_rows_eq]
    exact List.mem_map_of_mem hsource
  obtain ⟨sourceRow, hrow, htrace⟩ := List.mem_map.mp hsourceRow
  have hsourceBand := expected_rows_partition certificate totalAddRows
    sourceRow hrow
  have hpublicBand := public_cells_band certificate totalAddRows
    publicCell hpublic
  rcases hpublicBand with h | h | h | h <;>
    cases hkind : sourceRow.multiply <;>
    simp [hkind] at hsourceBand <;> omega

/-- The twenty-five modeled public input/output cells have distinct trace
positions when the native add partition leaves room for constant/padding
adds after the source and public copy adds. -/
theorem expected_public_rows_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hspace : 11 + sourceAddCount certificate ≤ totalAddRows) :
    (((expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows).map
      ColumnCell.traceRow)).Nodup := by
  simp [expectedInputCells, expectedOutputCells, expectedMaskCells,
    expectedPackAddCell, expectedPackMulCell, expectedInputCopyCell,
    expectedInputSelfCell, expectedMaskCell, expectedInverseCell,
    expectedCopyCell, List.range, List.range.loop, List.map_append,
    List.nodup_cons] <;> omega

theorem checked_public_cells_within_512
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hrows : totalAddRows + 1 + 27 + sourceMulCount certificate + 8 = 2 ^ 9) :
    ∀ cell ∈ expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows,
      cell.traceRow < 2 ^ 9 := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have ha := source_add_count_bounded certificate
  have hm := source_mul_count_bounded certificate
  intro cell hcell
  have hband := public_cells_band certificate totalAddRows cell hcell
  rcases hband with h | h | h | h <;> norm_num at hrows ⊢ <;> omega

private theorem fold_rows_unique (totalAddRows : Nat)
    (remaining : List Instruction) (priorAdds priorMuls : Nat)
    (rows : List NativeSourceRow)
    (hnodup : (rows.map NativeSourceRow.traceRow).Nodup)
    (hwithin : rowsWithin totalAddRows priorAdds priorMuls rows)
    (hgap : 3 + priorAdds + remaining.length ≤ totalAddRows + 28) :
    (((remaining.foldl (emitStep totalAddRows)
      (priorAdds, priorMuls, rows)).2.2).map NativeSourceRow.traceRow).Nodup := by
  induction remaining generalizing priorAdds priorMuls rows with
  | nil => simpa using hnodup
  | cons instruction rest ih =>
      let next := emittedRow instruction totalAddRows priorAdds priorMuls
      simp only [List.length_cons] at hgap
      have hnot : next.traceRow ∉ rows.map NativeSourceRow.traceRow := by
        intro hmember
        obtain ⟨old, hold, heq⟩ := List.mem_map.mp hmember
        have hrange := hwithin old hold
        cases hi : instruction.multiply <;> cases ho : old.multiply <;>
          simp [next, emittedRow, hi, ho] at heq hrange <;> omega
      have hnodup' :
          ((rows ++ [next]).map NativeSourceRow.traceRow).Nodup := by
        simpa [List.map_append] using
          (List.nodup_concat (rows.map NativeSourceRow.traceRow)
            next.traceRow).2 ⟨hnot, hnodup⟩
      have hwithin' : rowsWithin totalAddRows
          (priorAdds + if instruction.multiply then 0 else 1)
          (priorMuls + if instruction.multiply then 1 else 0)
          (rows ++ [next]) := by
        intro row hmember
        rcases List.mem_append.mp hmember with hold | hnew
        · have hrange := hwithin row hold
          cases instruction.multiply <;> cases ho : row.multiply <;>
            simp [ho] at hrange ⊢ <;> omega
        · have heq : row = next := by simpa using hnew
          subst row
          cases hi : instruction.multiply <;>
            simp [next, emittedRow, hi]
      have hgap' :
          3 + (priorAdds + if instruction.multiply then 0 else 1) +
            rest.length ≤ totalAddRows + 28 := by
        cases hi : instruction.multiply <;> simp [hi] at * <;> omega
      simpa [List.foldl_cons, emitStep, next] using
        (ih _ _ (rows ++ [next]) hnodup' hwithin' hgap')

/-- Source rows in the modeled grouped AIR schedule occupy distinct trace
positions. The explicit gap premise keeps the source-add partition below the
pointwise-multiply partition. It is satisfied by the native bounded profile's
row count, but equality of that count with the committed trace is separate. -/
theorem expected_rows_trace_rows_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hgap : 3 + certificate.instructions.length ≤ totalAddRows + 28) :
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup := by
  have h := fold_rows_unique totalAddRows certificate.instructions 0 0 []
    (by simp) (by simp [rowsWithin]) (by simpa using hgap)
  simpa [expectedRows, emitStep] using h

/-- A separately established 16-instruction budget is sufficient for unique
source trace positions at any natural `totalAddRows` in this modeled layout. -/
theorem expected_rows_trace_rows_nodup_of_budget (certificate : Certificate)
    (totalAddRows : Nat) (hbudget : certificate.instructions.length ≤ 16) :
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup := by
  apply expected_rows_trace_rows_nodup
  omega

/-- The projected AIR source cells inherit the modeled schedule's unique
trace positions. This says nothing about omitted non-source cells. -/
theorem expected_cells_trace_rows_nodup (certificate : Certificate)
    (totalAddRows : Nat)
    (hgap : 3 + certificate.instructions.length ≤ totalAddRows + 28) :
    ((expectedCells certificate totalAddRows).map ColumnCell.traceRow).Nodup := by
  rw [expected_cells_trace_rows_eq]
  exact expected_rows_trace_rows_nodup certificate totalAddRows hgap

/-- The modeled deterministic `expectedRows` schedule supplies a matching
projected cell for each instruction. This theorem does not itself prove
uniqueness; `expected_rows_trace_rows_nodup` separately proves modeled source
row uniqueness under its gap premise. Matching these modeled fields to a
decoded trace still requires the separate `fixedMatches` premise; native
emitter correspondence is not proved here. -/
theorem source_plan_expected (certificate : Certificate)
    (totalAddRows : Nat) :
    SourcePlan certificate (expectedCells certificate totalAddRows) := by
  intro instruction hmember
  obtain ⟨native, hpair, hshape⟩ := forall₂_rows_plan
    certificate.instructions (expectedRows certificate totalAddRows)
    (expected_rows_shape certificate totalAddRows) instruction hmember
  refine ⟨expectedCell certificate instruction native, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨(instruction, native), hpair, rfl⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hshape.2.2.1
  · exact hshape.2.2.2.1
  · exact hshape.2.2.2.2
  · rfl

/-- A successful exact byte relation supplies both a complete modeled
source-cell plan and distinct modeled source row positions. The statement
does not identify those positions with native emitted or committed rows. -/
theorem checked_relation_modeled_source_schedule
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate) :
    SourcePlan certificate (expectedCells certificate totalAddRows) ∧
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.traceRow).Nodup ∧
    ((expectedCells certificate totalAddRows).map ColumnCell.traceRow).Nodup := by
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  refine ⟨source_plan_expected certificate totalAddRows,
    expected_rows_trace_rows_nodup_of_budget certificate totalAddRows hbudget,
    expected_cells_trace_rows_nodup certificate totalAddRows ?_⟩
  omega

/-- Exact projected row roster for the modeled bounded direct-gate profile.
Every byte-admitted source instruction retains its order, opcode, circuit
wire, and operand/output addresses by `expected_rows_opcode_and_addresses`;
this theorem adds global row uniqueness and 512-row capacity for all source,
input, and output projections. `hrows` states the actual native arithmetic
partition counts, including constant and padding adds; source admission alone
does not establish it. Committed-column equality and remaining nonprojected
native rows are outside this theorem. -/
theorem checked_relation_modeled_row_roster
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hrows : totalAddRows + 1 + 27 + sourceMulCount certificate + 8 = 2 ^ 9) :
    SourcePlan certificate (expectedCells certificate totalAddRows) ∧
    (((expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows)).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows),
      cell.traceRow < 2 ^ 9) := by
  have hsource := checked_relation_modeled_source_schedule
    sourceBytes normalizedBytes certificate totalAddRows hrelation
  have hbudget := checked_relation_instruction_bound sourceBytes
    normalizedBytes certificate hrelation
  have ha := source_add_count_bounded certificate
  have hm := source_mul_count_bounded certificate
  have hspace : 11 + sourceAddCount certificate ≤ totalAddRows := by
    norm_num at hrows
    omega
  have hpublic := expected_public_rows_nodup certificate totalAddRows hspace
  have hdisjoint : List.Disjoint
      ((expectedCells certificate totalAddRows).map ColumnCell.traceRow)
      ((expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows).map ColumnCell.traceRow) := by
    intro row hsourceRow hpublicRow
    obtain ⟨sourceCell, hsourceCell, hsourceEq⟩ :=
      List.mem_map.mp hsourceRow
    obtain ⟨publicCell, hpublicCell, hpublicEq⟩ :=
      List.mem_map.mp hpublicRow
    exact expected_source_public_rows_disjoint certificate totalAddRows hspace
      sourceCell hsourceCell publicCell hpublicCell
      (hsourceEq.trans hpublicEq.symm)
  refine ⟨hsource.1, ?_, ?_⟩
  · rw [List.map_append]
    exact hsource.2.2.append hpublic hdisjoint
  · intro cell hcell
    rcases List.mem_append.mp hcell with hsourceCell | hpublicCell
    · have hsourceRow : cell.traceRow ∈
          (expectedRows certificate totalAddRows).map
            NativeSourceRow.traceRow := by
        rw [← expected_cells_trace_rows_eq]
        exact List.mem_map_of_mem hsourceCell
      obtain ⟨sourceRow, hrow, htrace⟩ := List.mem_map.mp hsourceRow
      have hbound := checked_source_rows_within_512 sourceBytes
        normalizedBytes certificate totalAddRows hrelation hrows sourceRow hrow
      omega
    · exact checked_public_cells_within_512 sourceBytes normalizedBytes
        certificate totalAddRows hrelation hrows cell hpublicCell

/-- A single admission theorem collects exact modeled source instruction
order, opcode, circuit position, addresses, projected selector flags, and the
capacity-safe pairwise-distinct source/public row roster. Every equality here
is about `expectedRows` and projected `ColumnCell`s. Native emitter fidelity,
the nonprojected cells, and committed-column equality remain external. -/
theorem checked_relation_modeled_exact_row_roster
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hrows : totalAddRows + 1 + 27 + sourceMulCount certificate + 8 = 2 ^ 9) :
    (∀ pair ∈ certificate.instructions.zip
        (expectedRows certificate totalAddRows),
      pair.2.circuitRow = 5 + pair.1.id ∧
      pair.2.multiply = pair.1.multiply ∧
      pair.2.in0 = address pair.1.lhs ∧
      pair.2.in1 = address pair.1.rhs ∧
      pair.2.out = address pair.1.id) ∧
    ((expectedRows certificate totalAddRows).map
      NativeSourceRow.multiply =
        certificate.instructions.map Instruction.multiply) ∧
    ((expectedCells certificate totalAddRows).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
        certificate.instructions.map (fun instruction =>
          (if instruction.multiply then 0 else 1,
           if instruction.multiply then 1 else 0))) ∧
    SourcePlan certificate (expectedCells certificate totalAddRows) ∧
    (((expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows)).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows),
      cell.traceRow < 2 ^ 9) := by
  exact ⟨expected_rows_opcode_and_addresses certificate totalAddRows,
    expected_rows_opcode_sequence certificate totalAddRows,
    expected_cells_opcode_flags certificate totalAddRows,
    checked_relation_modeled_row_roster sourceBytes normalizedBytes
      certificate totalAddRows hrelation hrows⟩

/-- Output masks, inverse-basis products, and public copies each yield once
by construction, independently of the source program's instruction count. -/
theorem expected_output_cells_positive (certificate : Certificate)
    (totalAddRows : Nat) :
    ∀ cell ∈ expectedOutputCells certificate totalAddRows,
      0 < cell.mults := by
  intro cell hcell
  simp [expectedOutputCells, expectedMaskCells, expectedMaskCell,
    expectedInverseCell, expectedCopyCell] at hcell
  rcases hcell with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ <;>
    subst cell <;> simp

/-- The input pack's final row has exactly the source input's use count;
other public-input rows have fixed positive multiplicity. -/
theorem expected_input_cells_positive (certificate : Certificate)
    (totalAddRows : Nat) (huse : 0 < sourceInputUses certificate) :
    ∀ cell ∈ expectedInputCells certificate totalAddRows,
      0 < cell.mults := by
  intro cell hcell
  simp [expectedInputCells, expectedPackAddCell, expectedPackMulCell,
    expectedInputCopyCell, expectedInputSelfCell] at hcell
  rcases hcell with ⟨index, _, h⟩ | ⟨_, _, h⟩ |
      ⟨_, _, h⟩ | ⟨_, _, h⟩
  · subst cell
    by_cases hi : index = 2 <;> simp [hi, huse]
  all_goals subst cell; simp

private theorem input_read_fold_ge (instructions : List Instruction)
    (start : Nat) :
    start ≤ instructions.foldl
      (fun count instruction =>
        count + (if instruction.lhs == 0 then 1 else 0) +
          (if instruction.rhs == 0 then 1 else 0)) start := by
  induction instructions generalizing start with
  | nil => simp
  | cons instruction rest ih =>
      simp only [List.foldl_cons]
      have hstep : start ≤
          start + (if instruction.lhs == 0 then 1 else 0) +
            (if instruction.rhs == 0 then 1 else 0) := by omega
      exact hstep.trans (ih _)

private theorem first_checked_step_reads_input (instruction : Instruction)
    (next : List Term)
    (hstep : checkStep [.input] instruction = some next) :
    instruction.lhs = 0 ∧ instruction.rhs = 0 := by
  have hleft : [Term.input][instruction.lhs]? ≠ none := by
    intro hnone
    simp [checkStep, hnone] at hstep
  have hright : [Term.input][instruction.rhs]? ≠ none := by
    intro hnone
    simp [checkStep, hnone] at hstep
  constructor
  · simpa using hleft
  · simpa using hright

/-- A nonempty checked SSA execution has a first step, and its only initial
wire is input zero. Consequently the source input has a positive arithmetic
use count. -/
theorem source_input_used_of_checked_nonempty (certificate : Certificate)
    (meaning : Term)
    (hterm : termFor certificate = some meaning)
    (hnonempty : certificate.instructions ≠ []) :
    0 < sourceInputUses certificate := by
  cases hins : certificate.instructions with
  | nil => exact False.elim (hnonempty hins)
  | cons instruction rest =>
      have hfirst : ∃ next, checkStep [.input] instruction = some next := by
        unfold termFor at hterm
        simp only [hins, List.foldlM_cons] at hterm
        cases hstep : checkStep [.input] instruction with
        | none => simp [hstep] at hterm
        | some next => exact ⟨next, rfl⟩
      obtain ⟨next, hstep⟩ := hfirst
      have hzero := (first_checked_step_reads_input instruction next hstep).1
      simp only [sourceInputUses, hins, List.foldl_cons]
      have hpositive : 0 <
          (0 + (if instruction.lhs == 0 then 1 else 0) +
            (if instruction.rhs == 0 then 1 else 0)) := by
        simp [hzero]
      exact lt_of_lt_of_le hpositive (input_read_fold_ge rest _)

private theorem parsed_nonempty (bytes : List Nat) (parsed : Parsed)
    (hparse : parseBytes bytes = some parsed) :
    parsed.certificate.instructions ≠ [] := by
  simp [parseBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  have hnonempty := hparse.2.2.1
  have hparsed := hparse.2.2.2.2.2
  intro hnil
  exact hnonempty ((congrArg (fun p : Parsed => p.certificate.instructions)
    hparsed).trans hnil)

/-- Successful exact source/normalized-byte admission forces a first checked
instruction. The first instruction can only read the sole initial input wire,
so the public input pack's final producer multiplicity is positive. -/
theorem checked_relation_source_input_used
    (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate) :
    0 < sourceInputUses certificate := by
  unfold checkRelation at hrelation
  cases hsource : parseBytes sourceBytes with
  | none => simp [hsource] at hrelation
  | some parsed =>
      cases hencoded : encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hrelation
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hrelation
            subst certificate
            exact source_input_used_of_checked_nonempty
              parsed.certificate parsed.meaning parsed.checked
              (parsed_nonempty sourceBytes parsed hsource)
          · simp [hsource, hencoded, hmatch] at hrelation

private theorem native_rows_lookup {logSize : Nat} (trace : Trace logSize)
    (i : Fin (2 ^ logSize)) :
    (nativeRows trace)[i.val]? = some (row trace i) := by
  simp only [nativeRows, List.getElem?_ofFn, dif_pos i.isLt]

private theorem projected_roots_zero {logSize : Nat}
    (trace : Trace logSize) (cell : ColumnCell)
    (i : Fin (2 ^ logSize))
    (hflags : (row trace i).flags = cellFlags cell)
    (hroots : allArithmeticRootsZero trace) :
    ∀ root ∈ bytecodeArithmetic
      (physicalBytecodeCells cell (row trace i)), root = 0 := by
  have heq : bytecodeArithmetic
      (physicalBytecodeCells cell (row trace i)) =
      bytecodeArithmetic (fromTrace trace i) := by
    calc
      bytecodeArithmetic (physicalBytecodeCells cell (row trace i))
          = residuals (cellFlags cell) (row trace i).in0
              (row trace i).in1 (row trace i).output :=
            physical_bytecode_arithmetic_eq cell (row trace i)
      _ = S31.Gadgets.Air.NativeQm31Air.residuals (row trace i).flags
            (row trace i).in0 (row trace i).in1 (row trace i).output := by
            rw [hflags]
            exact (S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq
              (cellFlags cell) (row trace i).in0 (row trace i).in1
              (row trace i).output).symm
      _ = arithmetic (fromTrace trace i) :=
            (arithmetic_from_trace trace i).symm
      _ = bytecodeArithmetic (fromTrace trace i) := by
            exact (bytecode_arithmetic_eq (fromTrace trace i)).symm
  simpa only [heq] using hroots i

private theorem physical_boundary_rows {logSize : Nat}
    (trace : Trace logSize) (cells : List ColumnCell)
    (hfixed : ∀ cell ∈ cells, fixedMatches trace cell)
    (hpositive : ∀ cell ∈ cells, 0 < cell.mults)
    (hroots : allArithmeticRootsZero trace) :
    physicalGateBytecodeRows cells (nativeRows trace) := by
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    hfixed cell hcell
  refine ⟨row trace i, ?_, hflags, hin0, hin1, hout, hmult, ?_, ?_⟩
  · simpa only [← hi] using native_rows_lookup trace i
  · simpa only [hmult] using hpositive cell hcell
  · exact projected_roots_zero trace cell i hflags hroots

/-- One decoded trace discharges the three physical-row families for any
certificate whose projected source plan and boundary multiplicities are
checked. Dead source rows still carry exact fixed cells and zero roots. -/
theorem decoded_rows {logSize : Nat} (trace : Trace logSize)
    (certificate : Certificate)
    (sourceCells inputCells outputCells : List ColumnCell)
    (hplan : SourcePlan certificate sourceCells)
    (hpositiveInput : ∀ cell ∈ inputCells, 0 < cell.mults)
    (hpositiveOutput : ∀ cell ∈ outputCells, 0 < cell.mults)
    (hfixed : ∀ cell ∈ sourceCells ++ inputCells ++ outputCells,
      fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace) :
    sourceGateBytecodeRowsAllowDead certificate sourceCells
      (nativeRows trace) ∧
    physicalGateBytecodeRows inputCells (nativeRows trace) ∧
    physicalGateBytecodeRows outputCells (nativeRows trace) := by
  constructor
  · intro instruction hmember
    obtain ⟨cell, hcell, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, huses⟩ := hplan instruction hmember
    obtain ⟨i, hi, hflags, haddr0, haddr1, haddrOut, hmult⟩ :=
      hfixed cell (by simp [hcell])
    refine ⟨cell, hcell, row trace i, ?_, hadd, hsub, hmul, hpm,
      hin0, hin1, hout, hflags, haddr0, haddr1, haddrOut,
      hmult, ?_, ?_⟩
    · simpa only [← hi] using native_rows_lookup trace i
    · intro hused
      simpa only [hmult, huses] using hused
    · exact projected_roots_zero trace cell i hflags hroots
  constructor
  · exact physical_boundary_rows trace inputCells
      (by intro cell hcell; exact hfixed cell (by simp [hcell]))
      hpositiveInput hroots
  · exact physical_boundary_rows trace outputCells
      (by intro cell hcell; exact hfixed cell (by simp [hcell]))
      hpositiveOutput hroots

/-- Generic source-to-public semantics from one decoded trace. Successful
bounded source/normalized-byte admission proves the public input's use count
positive, and row constructors prove the remaining public multiplicities.
Ideal Gate and constant/public-event
premises remain separate from native verifier acceptance. -/
theorem decoded_public_io_sound {logSize : Nat} (trace : Trace logSize)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat)
    (sourceCells inputCells outputCells : List ColumnCell)
    (input claimed : Lanes)
    (externalUses externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hsourceCells : sourceCells = expectedCells certificate totalAddRows)
    (hinputCells : inputCells = expectedInputCells certificate totalAddRows)
    (houtputCells : outputCells = expectedOutputCells certificate totalAddRows)
    (hfixed : ∀ cell ∈ sourceCells ++ inputCells ++ outputCells,
      fixedMatches trace cell)
    (hroots : allArithmeticRootsZero trace)
    (hbalance : balanced (nativeRows trace) externalUses externalYields)
    (hunique : uniqueProduced (allYields (nativeRows trace) externalYields))
    (hzero : (0, base 0) ∈ allYields (nativeRows trace) externalYields)
    (hbasis1 : (15, unit ⟨1, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hbasis2 : (2, unit ⟨2, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hbasis3 : (16, unit ⟨3, by decide⟩) ∈
      allYields (nativeRows trace) externalYields)
    (hmaskBasis : ∀ i : Fin 4,
      (maskBasisAddress i.val, unit i) ∈
        allYields (nativeRows trace) externalYields)
    (hinverseBasis : ∀ i : Fin 3,
      ((expectedInverseCell certificate totalAddRows i.val).in1,
        unitInverse ⟨i.val + 1, by omega⟩) ∈
          allYields (nativeRows trace) externalYields)
    (hpublicInputPins : ∀ i : Fin 4,
      (3 + i.val, base (Field.toZMod (input i))) ∈
        allYields (nativeRows trace) externalYields)
    (hpublicOutputPins : ∀ i : Fin 4,
      (7 + i.val, base (Field.toZMod (claimed i))) ∈
        allYields (nativeRows trace) externalYields) :
    denotation sourceBytes input = some claimed := by
  have hinputUse := checked_relation_source_input_used sourceBytes
    normalizedBytes certificate hrelation
  obtain ⟨hsource, hinput, houtput⟩ :=
    decoded_rows trace certificate sourceCells inputCells outputCells
      (by rw [hsourceCells]; exact source_plan_expected certificate totalAddRows)
      (by rw [hinputCells]; exact expected_input_cells_positive certificate totalAddRows hinputUse)
      (by rw [houtputCells]; exact expected_output_cells_positive certificate totalAddRows)
      hfixed hroots
  exact bytecode_exact_gate_public_io_allow_dead_sound
    sourceBytes normalizedBytes certificate totalAddRows
    sourceCells inputCells outputCells input claimed
    (nativeRows trace) externalUses externalYields
    hrelation hsourceCells hsource hinputCells hinput
    houtputCells houtput hbalance hunique
    hzero hbasis1 hbasis2 hbasis3 hmaskBasis hinverseBasis
    hpublicInputPins hpublicOutputPins

end S31.Functional.SSAGeneralDecodedTraceBridge
