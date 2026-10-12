import S31.Gadgets.Functional.Correspondence.OptimizedSourceAirRows
import S31.Gadgets.Functional.Correspondence.SourceDeterminedDirectRows

/-!
The optimized source-byte grammar permits reversed commutative operands and
common-subexpression elimination. This module proves that its compact
certificate still fits the bounded 512-row direct-Gate layout. In particular,
CSE cannot increase the producer count, and source/public projected cells
have distinct, in-range physical positions.

These are modeled row-roster properties. Equality to native-exported fixed
columns, binding to a proof commitment, Gate interaction soundness, and
PCS/FRI remain separate obligations.
-/

namespace S31.Functional.Correspondence.OptimizedPhysicalRoster

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAPublicInputBinding
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.Correspondence.CanonicalDagOptimization
open S31.Functional.Correspondence.OptimizedTextBytes
open S31.Functional.Correspondence.OptimizedSourceAirRows
open S31.Functional.Correspondence.SourceDeterminedDirectRows

/-- A CSE hit adds no compact producer; a miss adds exactly one. -/
private theorem step_compact_length_le
    (state next : CanonicalDagOptimization.State)
    (raw : Instruction) (hstep : step state raw = some next) :
    next.instructions.length ≤ state.instructions.length + 1 := by
  unfold step at hstep
  by_cases hid : raw.id = state.sourceToCanonical.length
  · cases hlhs : state.sourceToCanonical[raw.lhs]? with
    | none => simp [hid, hlhs] at hstep
    | some lhs =>
        cases hrhs : state.sourceToCanonical[raw.rhs]? with
        | none => simp [hid, hlhs, hrhs] at hstep
        | some rhs =>
            let key : Key := (raw.multiply, min lhs rhs, max lhs rhs)
            cases hfind : findKey key state.keys with
            | none =>
                have hnext : next.instructions = state.instructions ++
                    [{ id := state.instructions.length + 1,
                       lhs := min lhs rhs, rhs := max lhs rhs,
                       multiply := raw.multiply }] := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using
                    congrArg (fun item => item.map
                      CanonicalDagOptimization.State.instructions) hstep.symm
                simp [hnext]
            | some existing =>
                have hnext : next.instructions = state.instructions := by
                  simpa [step, hid, hlhs, hrhs, key, hfind] using
                    congrArg (fun item => item.map
                      CanonicalDagOptimization.State.instructions) hstep.symm
                simp [hnext]
  · simp [hid] at hstep

/-- Every successful optimizer fold produces at most one compact arithmetic
node per source arithmetic instruction. -/
private theorem fold_compact_length_le (instructions : List Instruction)
    (state next : CanonicalDagOptimization.State)
    (hfold : instructions.foldlM step state = some next) :
    next.instructions.length ≤ state.instructions.length + instructions.length := by
  induction instructions generalizing state with
  | nil =>
      have hsame : state = next := by simpa using hfold
      subst next
      simp
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at hfold
      cases hstep : step state instruction with
      | none => simp [hstep] at hfold
      | some middle =>
          have htail := ih middle (by simpa [hstep] using hfold)
          have hhead := step_compact_length_le state middle instruction hstep
          simp only [List.length_cons]
          omega

/-- Every accepted CSE result uses at most as many arithmetic producers as
its source and the optimizer enforces the 16-source-producer limit. -/
theorem optimized_compact_cost_bound (raw compact : Certificate)
    (hopt : optimizeChecked raw = some compact) :
    compact.instructions.length ≤ raw.instructions.length ∧
      raw.instructions.length ≤ 16 := by
  unfold optimizeChecked at hopt
  cases hraw : optimize raw with
  | none => simp [hraw] at hopt
  | some checked =>
      have haudit : audit raw checked = true := by
        by_contra hfalse
        simp [hraw, hfalse] at hopt
      have hcompact : compact = checked := by
        simpa [hraw, haudit] using hopt.symm
      subst compact
      unfold optimize at hraw
      by_cases hsmall : raw.instructions.length > 16
      · simp [hsmall] at hraw
      · cases hfold : raw.instructions.foldlM step
          ({} : CanonicalDagOptimization.State) with
        | none => simp [hsmall, hfold] at hraw
        | some state =>
            cases hlookup : state.sourceToCanonical[raw.output]? with
            | none => simp [hsmall, hfold, hlookup] at hraw
            | some output =>
                have hchecked : checked.instructions = state.instructions := by
                  have heq : checked = Certificate.mk state.instructions output := by
                    simpa [hsmall, hfold, hlookup] using hraw.symm
                  exact congrArg Certificate.instructions heq
                have hlength := fold_compact_length_le raw.instructions
                  ({} : CanonicalDagOptimization.State) state hfold
                have hcost : checked.instructions.length ≤
                    raw.instructions.length := by
                  simpa [hchecked] using hlength
                exact ⟨hcost, by omega⟩

/-- The compact certificate is itself within the 16-producer direct-Gate
profile. -/
theorem optimized_compact_budget (raw compact : Certificate)
    (hopt : optimizeChecked raw = some compact) :
    compact.instructions.length ≤ 16 := by
  obtain ⟨hcost, hsource⟩ := optimized_compact_cost_bound raw compact hopt
  omega

/-- Exact optimized source, normalized JSON and canonical IR bytes give a
compact producer budget; this is not a free caller-supplied assumption. -/
theorem checked_optimized_compact_budget
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact) :
    compact.instructions.length ≤ 16 := by
  obtain ⟨parsed, _, _, _, hcompact, _⟩ := checked_bytes_sound
    sourceBytes normalizedBytes canonicalBytes compact (fun _ => 0) hbytes
  subst compact
  exact optimized_compact_budget parsed.raw parsed.compact
    parsed.checkedOptimization

/-- The compact source certificate determines a valid 512-row native-profile
partition with no independently chosen add-row count. -/
theorem optimized_bytes_partition
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact) :
    compiledAddRows compact + 1 + 27 + sourceMulCount compact + 8 =
      2 ^ 9 := by
  have hbudget := checked_optimized_compact_budget sourceBytes
    normalizedBytes canonicalBytes compact hbytes
  have hm := source_mul_count_bounded compact
  unfold compiledAddRows
  omega

/-- For every accepted optimized byte triple, the modeled source cells and
the 25 public input/output cells fit a single 512-row direct-Gate trace. CSE
hits use the earlier canonical producer and allocate no additional source
cell. Every source operation retains its selector and operand/address shape.
The native emitter-to-roster and committed-column checks are not discharged
here. -/
theorem optimized_bytes_exact_row_roster
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact) :
    compact.instructions.length ≤ 16 ∧
    compiledAddRows compact + 1 + 27 + sourceMulCount compact + 8 =
      2 ^ 9 ∧
    SourcePlan compact (expectedCells compact (compiledAddRows compact)) ∧
    ((expectedRows compact (compiledAddRows compact)).map
      NativeSourceRow.multiply =
        compact.instructions.map Instruction.multiply) ∧
    ((expectedCells compact (compiledAddRows compact)).map
      (fun cell => (cell.addFlag, cell.pointwiseMulFlag)) =
        compact.instructions.map (fun instruction =>
          (if instruction.multiply then 0 else 1,
           if instruction.multiply then 1 else 0))) ∧
    (((expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact))).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact)),
      cell.traceRow < 2 ^ 9) := by
  have hbudget := checked_optimized_compact_budget sourceBytes
    normalizedBytes canonicalBytes compact hbytes
  have hpartition := optimized_bytes_partition sourceBytes
    normalizedBytes canonicalBytes compact hbytes
  have ha := source_add_count_bounded compact
  have hm := source_mul_count_bounded compact
  have hspace :
      11 + sourceAddCount compact ≤ compiledAddRows compact := by
    unfold compiledAddRows
    omega
  have hsourceNodup :
      ((expectedCells compact (compiledAddRows compact)).map
        ColumnCell.traceRow).Nodup := by
    rw [expected_cells_trace_rows_eq]
    exact expected_rows_trace_rows_nodup_of_budget compact
      (compiledAddRows compact) hbudget
  have hpublicNodup := expected_public_rows_nodup compact
    (compiledAddRows compact) hspace
  have hdisjoint : List.Disjoint
      ((expectedCells compact (compiledAddRows compact)).map
        ColumnCell.traceRow)
      ((expectedInputCells compact (compiledAddRows compact) ++
        expectedOutputCells compact (compiledAddRows compact)).map
          ColumnCell.traceRow) := by
    intro physicalRow hsourceRow hpublicRow
    obtain ⟨sourceCell, hsourceCell, hsourceEq⟩ :=
      List.mem_map.mp hsourceRow
    obtain ⟨publicCell, hpublicCell, hpublicEq⟩ :=
      List.mem_map.mp hpublicRow
    exact expected_source_public_rows_disjoint compact
      (compiledAddRows compact) hspace sourceCell hsourceCell
      publicCell hpublicCell (hsourceEq.trans hpublicEq.symm)
  refine ⟨hbudget, hpartition,
    source_plan_expected compact (compiledAddRows compact),
    expected_rows_opcode_sequence compact (compiledAddRows compact),
    expected_cells_opcode_flags compact (compiledAddRows compact), ?_, ?_⟩
  · rw [List.map_append]
    exact hsourceNodup.append hpublicNodup hdisjoint
  · intro cell hcell
    rcases List.mem_append.mp hcell with hsource | hpublic
    · have hrow : cell.traceRow ∈
          (expectedRows compact (compiledAddRows compact)).map
            NativeSourceRow.traceRow := by
        rw [← expected_cells_trace_rows_eq]
        exact List.mem_map_of_mem hsource
      obtain ⟨row, hrow, htrace⟩ := List.mem_map.mp hrow
      have hwithin := source_rows_within_512_of_budget compact
        (compiledAddRows compact) hbudget hpartition row hrow
      simpa [htrace] using hwithin
    · exact public_cells_within_512_of_budget compact
        (compiledAddRows compact) hbudget hpartition cell hpublic

/-- The same accepted byte triple supplies the bounded physical roster and,
under explicit observed-cell/local-equation and public-boundary premises,
the source-correct public claim. This theorem still assumes native/exported
fixed-cell equality, coherent Gate wire values, and accepted local roots;
it does not infer them from a succinct proof verifier's Boolean. -/
theorem optimized_bytes_public_claim_with_roster
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (observedCells : List ColumnCell)
    (wire : Nat → Quad) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (hcells : observedCells = expectedCells compact
      (compiledAddRows compact))
    (hinput : InputBoundary compact (compiledAddRows compact) wire input)
    (hlocal : ∀ cell ∈ observedCells, cellAccepts cell wire)
    (houtput : OutputBoundary compact (compiledAddRows compact) wire claimed) :
    OptimizedTextBytes.denotation sourceBytes input = some claimed ∧
    (((expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact))).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact)),
      cell.traceRow < 2 ^ 9) := by
  obtain ⟨_, _, _, _, _, hnodup, hwithin⟩ :=
    optimized_bytes_exact_row_roster sourceBytes normalizedBytes
      canonicalBytes compact hbytes
  exact ⟨optimized_source_public_output_sound sourceBytes normalizedBytes
    canonicalBytes compact observedCells wire input claimed hbytes hcells
    hinput hlocal houtput, hnodup, hwithin⟩

set_option maxRecDepth 8192 in
/-- The handwritten reversed/CSE source has four arithmetic lets but exactly
three compact producers; its source plus public boundary roster has 28 unique
positions inside the 512-row modeled trace. -/
theorem reversed_and_repeated_roster :
    ((expectedCells compactExample (compiledAddRows compactExample) ++
      (expectedInputCells compactExample (compiledAddRows compactExample) ++
        expectedOutputCells compactExample (compiledAddRows compactExample))).map
      ColumnCell.traceRow).length = 28 ∧
    (((expectedCells compactExample (compiledAddRows compactExample) ++
      (expectedInputCells compactExample (compiledAddRows compactExample) ++
        expectedOutputCells compactExample (compiledAddRows compactExample))).map
      ColumnCell.traceRow)).Nodup := by
  constructor
  · decide
  · decide

end S31.Functional.Correspondence.OptimizedPhysicalRoster
