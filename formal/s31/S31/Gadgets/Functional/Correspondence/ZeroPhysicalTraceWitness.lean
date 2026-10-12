import S31.Gadgets.Functional.Correspondence.AliasRawGateSoundness
import S31.Gadgets.Functional.TextSquare4Native

/-!
A concrete 512-row decoded trace witness for the zero-input alias square.
This module separates satisfiability of the physical fixed and arithmetic
premises from the native commitment and LogUp authentication obligations.
-/

namespace S31.Functional.Correspondence.ZeroPhysicalTraceWitness

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSACertificate
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.RawGateSoundness
open S31.Functional.Correspondence.AliasRawGateSoundness

abbrev QOp := S31.Gadgets.Air.Qm31Ops.Op

def roster (certificate : Certificate) (totalAddRows : Nat) : List ColumnCell :=
  expectedCells certificate totalAddRows ++
    expectedInputCells certificate totalAddRows ++
      expectedOutputCells certificate totalAddRows

def findRow : List ColumnCell → Nat → Option ColumnCell
  | [], _ => none
  | cell :: rest, row =>
      if cell.traceRow = row then some cell else findRow rest row

private theorem findRow_mem (cells : List ColumnCell) (row : Nat)
    (cell : ColumnCell) (h : findRow cells row = some cell) :
    cell ∈ cells := by
  induction cells with
  | nil => simp [findRow] at h
  | cons head tail ih =>
      simp only [findRow] at h
      split at h
      · cases h
        simp
      · exact List.mem_cons_of_mem _ (ih h)

private theorem findRow_eq_of_unique (cells : List ColumnCell)
    (cell : ColumnCell) (hmem : cell ∈ cells)
    (hunique : ∀ left ∈ cells, ∀ right ∈ cells,
      left.traceRow = right.traceRow → left = right) :
    findRow cells cell.traceRow = some cell := by
  induction cells with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [findRow]
      by_cases heq : head.traceRow = cell.traceRow
      · simp [heq]
        exact hunique head (by simp) cell hmem heq
      · simp only [heq, ↓reduceIte]
        have htail : cell ∈ tail := by
          rcases List.mem_cons.mp hmem with h | h
          · subst head
            exact False.elim (heq rfl)
          · exact h
        apply ih htail
        intro left hleft right hright hrow
        exact hunique left (by simp [hleft]) right (by simp [hright]) hrow

private theorem unique_rows_of_nodup (cells : List ColumnCell)
    (hnodup : (cells.map ColumnCell.traceRow).Nodup) :
    ∀ left ∈ cells, ∀ right ∈ cells,
      left.traceRow = right.traceRow → left = right := by
  intro left hleft right hright hrow
  exact (List.inj_on_of_nodup_map hnodup) hleft hright hrow

def fixedAt (cells : List ColumnCell) (row : Nat) (column : Fin 8) : F :=
  match findRow cells row with
  | none => if column.val = 0 then 1 else 0
  | some cell =>
      match column.val with
      | 0 => cell.addFlag
      | 1 => cell.subFlag
      | 2 => cell.mulFlag
      | 3 => cell.pointwiseMulFlag
      | 4 => cell.in0
      | 5 => cell.in1
      | 6 => cell.out
      | _ => cell.mults

def zeroTrace (cells : List ColumnCell)
    (externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    Trace 9 where
  fixed i column := fixedAt cells i.val column
  main _ _ := 0
  interaction _ _ := 0
  prev := Equiv.refl _
  airPair _ := 0
  airLast _ := 0
  claimed := 0
  externalUses := []
  externalYields := externalYields

theorem zeroTrace_fixed (cells : List ColumnCell)
    (hnodup : (cells.map ColumnCell.traceRow).Nodup)
    (hbound : ∀ cell ∈ cells, cell.traceRow < 512)
    (haddress : ∀ cell ∈ cells,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647)
    (externalYields : List S31.Gadgets.Air.GateLookup.Event)
    (cell : ColumnCell) (hmem : cell ∈ cells) :
    fixedMatches (zeroTrace cells externalYields) cell := by
  have hfind := findRow_eq_of_unique cells cell hmem
    (unique_rows_of_nodup cells hnodup)
  refine ⟨⟨cell.traceRow, hbound cell hmem⟩, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · simp [row, zeroTrace, fixedAt, hfind,
      S31.Functional.SSANativePolynomialRows.cellFlags]
  · simp [row, zeroTrace, fixedAt, hfind,
      Nat.mod_eq_of_lt (haddress cell hmem).1]
  · simp [row, zeroTrace, fixedAt, hfind,
      Nat.mod_eq_of_lt (haddress cell hmem).2.1]
  · simp [row, zeroTrace, fixedAt, hfind,
      Nat.mod_eq_of_lt (haddress cell hmem).2.2.1]
  · simp [row, zeroTrace, fixedAt, hfind,
      Nat.mod_eq_of_lt (haddress cell hmem).2.2.2]

/-- Every row of the zero-value trace satisfies the installed nine
arithmetic polynomials whenever its selected fixed flags encode one
operation. This includes the 485 unselected padding rows. -/
theorem zeroTrace_arithmetic (cells : List ColumnCell)
    (hflags : ∀ cell ∈ cells, ∃ op : QOp,
      S31.Functional.SSANativePolynomialRows.cellFlags cell = encode op)
    (externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    allArithmeticRootsZero (zeroTrace cells externalYields) := by
  intro i root hroot
  rw [bytecode_arithmetic_eq,
    arithmetic_from_trace] at hroot
  have hin : (row (zeroTrace cells externalYields) i).in0 = base 0 := by
    rfl
  have hin1 : (row (zeroTrace cells externalYields) i).in1 = base 0 := by
    rfl
  have hout : (row (zeroTrace cells externalYields) i).output = base 0 := by
    rfl
  have hdecoded : ∃ op : QOp,
      (row (zeroTrace cells externalYields) i).flags = encode op ∧
      (row (zeroTrace cells externalYields) i).output =
        evaluate op (row (zeroTrace cells externalYields) i).in0
          (row (zeroTrace cells externalYields) i).in1 := by
    cases hfind : findRow cells i.val with
    | none =>
        refine ⟨.add, ?_, ?_⟩
        · simp [row, zeroTrace, fixedAt, hfind, encode]
        · simp [hin, hin1, hout, evaluate,
            S31.Gadgets.Packed.add, base]
    | some cell =>
        obtain ⟨op, hop⟩ := hflags cell (findRow_mem cells i.val cell hfind)
        refine ⟨op, ?_, ?_⟩
        · simpa [row, zeroTrace, fixedAt, hfind,
            S31.Functional.SSANativePolynomialRows.cellFlags] using hop
        · cases op <;> simp [hin, hin1, hout, evaluate,
            S31.Gadgets.Packed.add, S31.Gadgets.Packed.mul,
            S31.Gadgets.Packed.pointwise, subtract, base]
  exact (S31.Gadgets.Air.NativeQm31AirProof.native_accepts_iff
    (row (zeroTrace cells externalYields) i).flags
    (row (zeroTrace cells externalYields) i).in0
    (row (zeroTrace cells externalYields) i).in1
    (row (zeroTrace cells externalYields) i).output).mpr hdecoded root hroot

def squareCertificate : Certificate :=
  { instructions :=
      [{ id := 1, lhs := 0, rhs := 0, multiply := true },
       { id := 2, lhs := 1, rhs := 1, multiply := true }],
    output := 2 }

def squareNormalized : List Nat :=
  ((S31.Functional.SSAAliasTextBytes.parseAliasBytes
    S31.Functional.SSAAliasTextBytes.aliasSquareSource).bind
      S31.Functional.SSANormalizedBytes.encodeNormalized).getD []

def squareCells : List ColumnCell := roster squareCertificate 474

set_option maxRecDepth 2048 in
theorem alias_square_relation :
    S31.Functional.SSAAliasTextBytes.checkAliasRelation
      S31.Functional.SSAAliasTextBytes.aliasSquareSource squareNormalized =
        some squareCertificate := by
  decide

theorem square_partition :
    474 + 1 + 27 + sourceMulCount squareCertificate + 8 = 2 ^ 9 := by
  decide

theorem square_roster_nodup :
    (squareCells.map ColumnCell.traceRow).Nodup := by
  decide

theorem square_roster_bounded :
    ∀ cell ∈ squareCells, cell.traceRow < 512 := by
  decide

theorem square_roster_addresses :
    ∀ cell ∈ squareCells,
      cell.in0 < 2147483647 ∧ cell.in1 < 2147483647 ∧
        cell.out < 2147483647 ∧ cell.mults < 2147483647 := by
  decide

theorem square_roster_flags :
    ∀ cell ∈ squareCells, ∃ op : QOp,
      S31.Functional.SSANativePolynomialRows.cellFlags cell = encode op := by
  have h : ∀ cell ∈ squareCells,
      S31.Functional.SSANativePolynomialRows.cellFlags cell = encode .add ∨
      S31.Functional.SSANativePolynomialRows.cellFlags cell = encode .sub ∨
      S31.Functional.SSANativePolynomialRows.cellFlags cell = encode .mul ∨
      S31.Functional.SSANativePolynomialRows.cellFlags cell =
        encode .pointwiseMul := by decide
  intro cell hcell
  rcases h cell hcell with ha | hs | hm | hp
  · exact ⟨.add, ha⟩
  · exact ⟨.sub, hs⟩
  · exact ⟨.mul, hm⟩
  · exact ⟨.pointwiseMul, hp⟩

def squareTrace (externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    Trace 9 := zeroTrace squareCells externalYields

/-- A real 512-row decoded assignment has all alias-square fixed selectors,
addresses and multiplicities and satisfies every installed local arithmetic
root at public input/output zero. The external Gate event lists are still a
parameter here, so this theorem does not claim lookup balance. -/
theorem square_fixed_arithmetic
    (externalYields : List S31.Gadgets.Air.GateLookup.Event) :
    (∀ cell ∈ squareCells, fixedMatches (squareTrace externalYields) cell) ∧
      allArithmeticRootsZero (squareTrace externalYields) := by
  constructor
  · intro cell hcell
    exact zeroTrace_fixed squareCells square_roster_nodup
      square_roster_bounded square_roster_addresses externalYields cell hcell
  · exact zeroTrace_arithmetic squareCells square_roster_flags externalYields

def zeroExternal : List S31.Gadgets.Air.GateLookup.Event :=
  [(0, base 0),
   (1, unit ⟨0, by decide⟩),
   (2, unit ⟨2, by decide⟩),
   (15, unit ⟨1, by decide⟩),
   (16, unit ⟨3, by decide⟩),
   (27, unitInverse ⟨1, by decide⟩),
   (30, unitInverse ⟨2, by decide⟩),
   (33, unitInverse ⟨3, by decide⟩)] ++
    (List.range 4).map (fun i => (3 + i, base 0)) ++
    (List.range 4).map (fun i => (7 + i, base 0))

/-- Public feeder values are uses of the Gate relation. The synthetic
zero-main trace keeps its separate external producers for local nonvacuity;
unlike the production witness, it intentionally is not Gate balanced. -/
def zeroFeederUses : List S31.Gadgets.Air.GateLookup.Event :=
  [(2, unit ⟨2, by decide⟩)] ++
    (List.range 4).map (fun i => (3 + i, base 0)) ++
    (List.range 4).map (fun i => (7 + i, base 0))

def zeroMainTrace : Trace 9 :=
  { squareTrace zeroExternal with externalUses := zeroFeederUses }

private theorem pairwise_implies_unique
    (events : List S31.Gadgets.Air.GateLookup.Event)
    (hp : events.Pairwise (fun a b => a.1 = b.1 → a.2 = b.2)) :
    uniqueProduced events := by
  intro address left right hleft hright
  have hsym : Symmetric
      (fun a b : S31.Gadgets.Air.GateLookup.Event =>
        a.1 = b.1 → a.2 = b.2) := by
    intro a b h hab
    exact (h hab.symm).symm
  have hself : ∀ e ∈ events, e.1 = e.1 → e.2 = e.2 := by
    intro _ _ _
    rfl
  exact hp.forall_of_forall hsym hself hleft hright rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem zero_main_unique :
    uniqueProduced (allYields (nativeRows zeroMainTrace)
      zeroMainTrace.externalYields) := by
  apply pairwise_implies_unique
  decide

def zeroLanes : Lanes := fun _ => 0

/-- The physical assumptions used by the alias-source raw-Gate theorem are
jointly satisfiable on a full decoded 512-row trace. The trace uses zero main
columns, so it is not claimed to satisfy ideal Gate balance: its basis
operands deliberately expose the distinction between arithmetic validity
and authenticated lookup validity. -/
theorem zero_main_physical_context :
    PhysicalTraceContext zeroMainTrace squareCertificate 474
      zeroLanes zeroLanes := by
  refine {
    partition := square_partition
    fixed := ?_
    arithmetic := (square_fixed_arithmetic zeroExternal).2
    unique := zero_main_unique
    zero := ?_
    basis1 := ?_
    basis2 := ?_
    basis3 := ?_
    maskBasis := ?_
    inverseBasis := ?_
    inputPins := ?_
    outputPins := ?_ }
  · intro cell hcell
    exact (square_fixed_arithmetic zeroExternal).1 cell hcell
  · simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
      allYields]
  · simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
      allYields]
  · simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
      allYields]
  · simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
      allYields]
  · intro i
    fin_cases i <;>
      simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
        allYields, maskBasisAddress]
  · intro i
    fin_cases i <;>
      simp [zeroMainTrace, squareTrace, zeroTrace, zeroExternal,
        allYields, expectedInverseCell, squareCertificate]
  · intro i
    fin_cases i <;> decide
  · intro i
    fin_cases i <;> decide

/-- The exact alias source bytes and normalized relation are satisfied by
the same 512-row context. All of `AliasFixedTraceContext` is constructive;
challenge acceptance and proof-system authentication are separate claims. -/
theorem zero_main_alias_context :
    AliasFixedTraceContext zeroMainTrace
      S31.Functional.SSAAliasTextBytes.aliasSquareSource
      squareNormalized squareCertificate 474 zeroLanes zeroLanes := by
  exact ⟨zero_main_physical_context, alias_square_relation⟩

/-- Local arithmetic by itself accepts the zero main-column assignment,
but the Gate lookup rejects it: the first pack-basis multiplication reads
zero from address 15, whose public basis producer is the nonzero `u` unit.
This checks that the constructed context does not accidentally certify a
balanced trace. -/
theorem zero_main_columns_not_gate_balanced :
    ¬ balanced (nativeRows zeroMainTrace)
      zeroMainTrace.externalUses zeroMainTrace.externalYields := by
  let index : Fin 512 := ⟨475, by decide⟩
  let r := row zeroMainTrace index
  have hr : r ∈ nativeRows zeroMainTrace := by
    exact List.mem_ofFn.mpr ⟨index, rfl⟩
  have hread : r.in0 = base 0 := by
    rfl
  have haddress : r.in0Address = 15 := by
    decide
  have hyield : (15, unit ⟨1, by decide⟩) ∈
      allYields (nativeRows zeroMainTrace)
        zeroMainTrace.externalYields := by
    apply List.mem_append_right
    decide
  have hnonzero : base 0 ≠ unit ⟨1, by decide⟩ := by decide
  intro hbalanced
  have hequal := balanced_read_matches _ _ hbalanced zero_main_unique
    r.in0Address r.in0 (unit ⟨1, by decide⟩)
    (row_input_use _ _ r hr).1 (by simpa only [haddress] using hyield)
  exact hnonzero (hread.symm.trans hequal)

/-- The fixture proves consistency of the *projected* physical context; its
unprojected padding is deliberately synthetic. This explicit mismatch at row
11 prevents it from being mistaken for an honest production witness. The
native direct-gate exporter assigns multiplicity 11 there, while this fixture assigns
zero. A full native completeness proof must bind all fixed rows and all
non-Gate feeder events. -/
theorem zero_main_not_native_padding :
    ((row zeroMainTrace ⟨11, by decide⟩).outAddress,
      (row zeroMainTrace ⟨11, by decide⟩).multiplicity) ≠
    S31.Functional.TextSquare4Native.paddedArithmeticOutputRows[11]! := by
  decide

end S31.Functional.Correspondence.ZeroPhysicalTraceWitness
