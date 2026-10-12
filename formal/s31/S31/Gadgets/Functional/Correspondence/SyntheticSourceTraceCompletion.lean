import S31.Gadgets.Functional.Correspondence.HonestSourceCellWitness
import S31.Gadgets.Functional.Correspondence.ZeroPhysicalTraceWitness

/-!
An exact 512-row *arithmetic* completion of the modeled source slice.
Source-selected rows use the address-coherent honest wire assignment from
`HonestSourceCellWitness`; every other row is a zero-plus-zero add row. This
is deliberately a synthetic completion: the native compiler's actual
source-independent fixed roster and its constant/basis/public Gate network
are not represented by these default rows.
-/

namespace S31.Functional.Correspondence.SyntheticSourceTraceCompletion

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness
open S31.Functional.Correspondence.HonestSourceCellWitness
open S31.Functional.Correspondence.SourceDeterminedDirectRows

private theorem find_row_mem (cells : List ColumnCell) (n : Nat)
    (cell : ColumnCell) (h : findRow cells n = some cell) : cell ∈ cells := by
  induction cells with
  | nil => simp [findRow] at h
  | cons first rest ih =>
      simp only [findRow] at h
      split at h
      · cases h
        simp
      · exact List.mem_cons_of_mem _ (ih h)

/-- A full twelve-column main row: read both values from the single wire
assignment and write its value at the cell's declared output address. -/
def mainAt (cells : List ColumnCell) (wire : Nat → Quad)
    (i : Fin 512) (c : Fin 12) : F :=
  match findRow cells i.val with
  | none => 0
  | some cell =>
      match c.val with
      | 0 => (wire cell.in0).a
      | 1 => (wire cell.in0).b
      | 2 => (wire cell.in0).c
      | 3 => (wire cell.in0).d
      | 4 => (wire cell.in1).a
      | 5 => (wire cell.in1).b
      | 6 => (wire cell.in1).c
      | 7 => (wire cell.in1).d
      | 8 => (wire cell.out).a
      | 9 => (wire cell.out).b
      | 10 => (wire cell.out).c
      | _ => (wire cell.out).d

/-- All 512 fixed/main rows are actual decoded cells. Source rows receive
their projected selectors and addresses; the rest are zero add rows. -/
def trace (cells : List ColumnCell) (wire : Nat → Quad) : Trace 9 :=
  { zeroTrace cells [] with main := mainAt cells wire }

private theorem row_of_some (cells : List ColumnCell) (wire : Nat → Quad)
    (i : Fin 512) (cell : ColumnCell)
    (hfind : findRow cells i.val = some cell) :
    (row (trace cells wire) i).flags = cellFlags cell ∧
    (row (trace cells wire) i).in0 = wire cell.in0 ∧
    (row (trace cells wire) i).in1 = wire cell.in1 ∧
    (row (trace cells wire) i).output = wire cell.out := by
  simp [row, trace, zeroTrace, fixedAt, mainAt, hfind,
    SSANativePolynomialRows.cellFlags]

private theorem row_of_none (cells : List ColumnCell) (wire : Nat → Quad)
    (i : Fin 512) (hfind : findRow cells i.val = none) :
    (row (trace cells wire) i).flags = encode .add ∧
    (row (trace cells wire) i).in0 = base 0 ∧
    (row (trace cells wire) i).in1 = base 0 ∧
    (row (trace cells wire) i).output = base 0 := by
  simp [row, trace, zeroTrace, fixedAt, mainAt, hfind, encode, base]

/-- A local polynomial witness at every selected cell gives an honest
assignment of all installed arithmetic roots for the entire synthetic
512-row trace. This constructs the trace rather than assuming its roots. -/
theorem arithmetic_complete (cells : List ColumnCell) (wire : Nat → Quad)
    (hcells : ∀ cell ∈ cells, cellAccepts cell wire) :
    allArithmeticRootsZero (trace cells wire) := by
  intro i root hroot
  rw [bytecode_arithmetic_eq, arithmetic_from_trace] at hroot
  have hdecoded : ∃ op : S31.Gadgets.Air.Qm31Ops.Op,
      (row (trace cells wire) i).flags = encode op ∧
      (row (trace cells wire) i).output =
        evaluate op (row (trace cells wire) i).in0
          (row (trace cells wire) i).in1 := by
    cases hfind : findRow cells i.val with
    | none =>
        obtain ⟨hf, hi0, hi1, ho⟩ := row_of_none cells wire i hfind
        refine ⟨.add, hf, ?_⟩
        simp [hi0, hi1, ho, evaluate, S31.Gadgets.Packed.add, base]
    | some cell =>
        obtain ⟨hf, hi0, hi1, ho⟩ := row_of_some cells wire i cell hfind
        obtain ⟨op, hflag, hvalue⟩ :=
          (accepts_iff _ _ _ _).mp
            (hcells cell (find_row_mem cells i.val cell hfind))
        refine ⟨op, ?_, ?_⟩
        · exact hf.trans hflag
        · simpa [ho, hi0, hi1] using hvalue
  exact (S31.Gadgets.Air.NativeQm31AirProof.native_accepts_iff
    (row (trace cells wire) i).flags
    (row (trace cells wire) i).in0
    (row (trace cells wire) i).in1
    (row (trace cells wire) i).output).mpr hdecoded root hroot

/-- Every projected cell, not just one existential representative per
instruction, satisfies its local source polynomial under one honest wire. -/
theorem expected_source_cells_accept (certificate : Certificate)
    (totalAddRows : Nat) (wire : Nat → Quad)
    (hrows : nativePolynomialRows certificate wire) :
    ∀ cell ∈ expectedCells certificate totalAddRows,
      cellAccepts cell wire := by
  intro cell hcell
  obtain ⟨pair, hpair, rfl⟩ := List.mem_map.mp hcell
  have hmember : pair.1 ∈ certificate.instructions :=
    (List.of_mem_zip hpair).1
  obtain ⟨_, _, hin0, hin1, hout⟩ :=
    expected_rows_opcode_and_addresses certificate totalAddRows pair hpair
  rw [expected_cell_polynomial_iff]
  simpa [hin0, hin1, hout] using hrows pair.1 hmember

/-- The synthetic trace's selected fixed cells equal the source projection
at their actual physical positions once the four exported Nat address/count
columns are shown canonical. Source-byte admission already proves these
positions distinct and in bounds. Canonicality is a separate static compiler
property; this theorem does not assume any main witness or AIR relation. -/
theorem selected_source_fixed_of_canonical_bounds
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (wire : Nat → Quad)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcanonical : ∀ cell ∈ expectedCells certificate
      (compiledAddRows certificate),
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647) :
    ∀ cell ∈ expectedCells certificate (compiledAddRows certificate),
      fixedMatches
        (trace (expectedCells certificate (compiledAddRows certificate)) wire)
        cell := by
  let cells := expectedCells certificate (compiledAddRows certificate)
  obtain ⟨_, hnodupFull, hboundFull⟩ :=
    direct_bytes_projected_roster sourceBytes normalizedBytes certificate hcheck
  have hnodup : (cells.map ColumnCell.traceRow).Nodup := by
    have hsplit : (cells.map ColumnCell.traceRow ++
        ((SSAInputAirCells.expectedInputCells certificate
          (compiledAddRows certificate) ++
          SSAOutputAirCells.expectedOutputCells certificate
            (compiledAddRows certificate)).map ColumnCell.traceRow)).Nodup := by
      simpa [cells, List.map_append] using hnodupFull
    exact hsplit.of_append_left
  have hbound : ∀ cell ∈ cells, cell.traceRow < 512 := by
    intro cell hcell
    have h := hboundFull cell (by
      apply List.mem_append_left
      simpa [cells] using hcell)
    norm_num at h
    exact h
  intro cell hcell
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    zeroTrace_fixed cells hnodup hbound hcanonical [] cell hcell
  refine ⟨i, hi, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [trace, row] using hflags
  · simpa [trace, row] using hin0
  · simpa [trace, row] using hin1
  · simpa [trace, row] using hout
  · simpa [trace, row] using hmult

/-- Every checked direct source and every input have a concrete
512-row decoded trace whose complete nine-polynomial arithmetic relation
vanishes. Its selected source-row main values come from one coherent SSA
wire assignment, and its selected output is the parsed source result.

The other rows are synthetic zero-add padding. The theorem does not claim
the native full fixed roster, public boundary, or Gate balance. -/
theorem accepted_direct_arithmetic_trace_exists
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (wire : Nat → Quad) (output : Lanes),
      SSATextBytes.denotation sourceBytes input = some output ∧
      allArithmeticRootsZero
        (trace (expectedCells certificate (compiledAddRows certificate)) wire) ∧
      wire (address certificate.output) = packM31 output := by
  obtain ⟨final, output, hdenotation, hcells, hselected⟩ :=
    checked_direct_source_cells_satisfiable sourceBytes normalizedBytes
      certificate input hcheck
  let wire := wireOfFinal final
  have hpolynomials : nativePolynomialRows certificate wire :=
    source_cells_imply_polynomial_rows certificate
      (expectedCells certificate (compiledAddRows certificate)) wire hcells
  exact ⟨wire, output, hdenotation,
    arithmetic_complete _ wire
      (expected_source_cells_accept certificate (compiledAddRows certificate)
        wire hpolynomials), hselected⟩

end S31.Functional.Correspondence.SyntheticSourceTraceCompletion
