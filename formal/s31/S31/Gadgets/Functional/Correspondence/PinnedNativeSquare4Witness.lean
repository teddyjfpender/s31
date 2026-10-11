import S31.Gadgets.Functional.Correspondence.PinnedFullFixedRoster
import S31.Gadgets.Functional.TextSquare4NativeWitness

/-!
The direct prover's uncommitted `writeBase` evaluations for the concrete
square4 assignment `x = [0, 1, 2, 7]`, composed with the complete native
512-row fixed roster. These are generated diagnostic values checked against
the source-bound package and key root by `check_square4_native_witness.py`.
Nothing here authenticates PCS openings, interaction columns, Fiat--Shamir
challenges, or acceptance by the verifier.
-/

namespace S31.Functional.Correspondence.PinnedNativeSquare4Witness

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.NativeQm31AirProof
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Gadgets.Air.GateLookup
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.ZeroPhysicalTraceWitness

set_option maxRecDepth 16384
set_option maxHeartbeats 5000000

def mainRows : List (List Nat) := S31.Functional.TextSquare4NativeWitness.mainRows

theorem main_rows_length : mainRows.length = 512 := by decide

private theorem main_all_width :
    mainRows.all (fun row => row.length == 12) = true := by decide

theorem main_row_width : ∀ i : Fin 512, (mainRows[i.val]!).length = 12 := by
  intro i
  have hi : i.val < mainRows.length := by
    rw [main_rows_length]
    exact i.isLt
  have hrow : mainRows[i.val]! ∈ mainRows := by
    rw [getElem!_pos mainRows i.val hi]
    exact List.getElem_mem hi
  simpa using (List.all_eq_true.mp main_all_width) _ hrow

private theorem main_flat_canonical :
    mainRows.flatten.all (· < 2147483647) = true := by decide

theorem main_cells_canonical : ∀ i : Fin 512, ∀ c : Fin 12,
    (mainRows[i.val]!)[c.val]! < 2147483647 := by
  intro i c
  have hi : i.val < mainRows.length := by
    rw [main_rows_length]
    exact i.isLt
  have hc : c.val < (mainRows[i.val]!).length := by
    rw [main_row_width]
    exact c.isLt
  have hrow : mainRows[i.val]! ∈ mainRows := by
    rw [getElem!_pos mainRows i.val hi]
    exact List.getElem_mem hi
  have hcell : (mainRows[i.val]!)[c.val]! ∈ mainRows.flatten := by
    apply List.mem_flatten.mpr
    refine ⟨mainRows[i.val]!, hrow, ?_⟩
    rw [getElem!_pos (mainRows[i.val]!) c.val hc]
    exact List.getElem_mem hc
  simpa using (List.all_eq_true.mp main_flat_canonical) _ hcell

def mainAt (i : Fin 512) (c : Fin 12) : F :=
  (mainRows[i.val]!)[c.val]!

theorem mainAt_exact (i : Fin 512) (c : Fin 12) :
    (mainAt i c).val = (mainRows[i.val]!)[c.val]! := by
  change ((mainRows[i.val]!)[c.val]! % 2147483647) =
    (mainRows[i.val]!)[c.val]!
  exact Nat.mod_eq_of_lt (main_cells_canonical i c)

def trace : Trace 9 := PinnedFullFixedRoster.trace mainAt

/-- The complete fixed roster is the source-derived direct-gate fixture,
while every main cell is the native prover's concrete base evaluation. -/
theorem all_native_cells_exact (i : Fin 512) :
    (∀ c : Fin 8, (trace.fixed i c).val =
      (PinnedFullFixedRoster.fixedRows[i.val]!)[c.val]!) ∧
    (∀ c : Fin 12, (trace.main i c).val =
      (mainRows[i.val]!)[c.val]!) := by
  constructor
  · exact PinnedFullFixedRoster.trace_fixed_exact mainAt i
  · exact mainAt_exact i

/-- Full fixed-column equality discharges the selected source and public
boundary fixed-cell premise, independently of the main witness. -/
theorem selected_cells_fixed :
    ∀ cell ∈ squareCells, fixedMatches trace cell :=
  PinnedFullFixedRoster.selected_cells_fixed mainAt

/-- This is exactly the `PhysicalTraceContext.fixed` field for the bounded
square4 certificate, discharged from the full 4096-cell native roster. -/
theorem physical_fixed_premise :
    ∀ cell ∈ expectedCells squareCertificate 474 ++
      expectedInputCells squareCertificate 474 ++
        expectedOutputCells squareCertificate 474,
      fixedMatches trace cell := by
  simpa [squareCells, roster, List.append_assoc] using selected_cells_fixed

/-- The complete native output-address and multiplicity projection also
matches the pinned direct-gate key roster, including all padding rows. -/
theorem native_output_pairs :
    (nativeRows trace).map (fun r => (r.outAddress, r.multiplicity)) =
      S31.Functional.TextSquare4Native.paddedArithmeticOutputRows := by
  decide

/-- Every active native arithmetic address has a unique produced value for
this concrete base trace. This is an ideal Gate fact; cryptographic row
authentication and interaction balance remain separate. -/
theorem native_producers_unique :
    uniqueProduced (allYields (nativeRows trace) trace.externalYields) := by
  apply PinnedFullOutputRoster.unique_of_pinned_output_roster trace native_output_pairs
  simp [trace, PinnedFullFixedRoster.trace]

/-- The two source products occupy physical rows 502 and 503, with the
native main limbs equal to the handwritten pointwise square chain. -/
theorem source_square_rows :
    (row trace ⟨502, by decide⟩).in0 = ⟨0, 1, 2, 7⟩ ∧
    (row trace ⟨502, by decide⟩).output = ⟨0, 1, 4, 49⟩ ∧
    (row trace ⟨503, by decide⟩).in0 = ⟨0, 1, 4, 49⟩ ∧
    (row trace ⟨503, by decide⟩).output = ⟨0, 1, 16, 2401⟩ := by
  decide

/-- The two actual source-product rows satisfy the installed nine local AIR
polynomials. The independent executable checker covers all 512 rows; a
kernel proof of the complete native base trace is still pending. -/
theorem source_rows_arithmetic :
    (∀ root ∈ bytecodeArithmetic (fromTrace trace ⟨502, by decide⟩), root = 0) ∧
    (∀ root ∈ bytecodeArithmetic (fromTrace trace ⟨503, by decide⟩), root = 0) := by
  constructor
  · have hflags : (row trace ⟨502, by decide⟩).flags = encode .pointwiseMul := by decide
    have hout : (row trace ⟨502, by decide⟩).output =
        evaluate .pointwiseMul (row trace ⟨502, by decide⟩).in0
          (row trace ⟨502, by decide⟩).in1 := by decide
    rw [bytecode_arithmetic_eq, arithmetic_from_trace]
    exact (native_accepts_iff _ _ _ _).mpr ⟨.pointwiseMul, hflags, hout⟩
  · have hflags : (row trace ⟨503, by decide⟩).flags = encode .pointwiseMul := by decide
    have hout : (row trace ⟨503, by decide⟩).output =
        evaluate .pointwiseMul (row trace ⟨503, by decide⟩).in0
          (row trace ⟨503, by decide⟩).in1 := by decide
    rw [bytecode_arithmetic_eq, arithmetic_from_trace]
    exact (native_accepts_iff _ _ _ _).mpr ⟨.pointwiseMul, hflags, hout⟩

def publicInput (i : Fin 4) : F :=
  ([0, 1, 2, 7] : List Nat)[i.val]!

def publicOutput (i : Fin 4) : F :=
  ([0, 1, 16, 2401] : List Nat)[i.val]!

/-- The eight source-owned public copy rows in the actual native main trace
yield exactly the public input and output words at addresses 3–10. The
outside verifier feeder still requires a separate authenticity proof. -/
theorem public_copy_events_covered :
    (∀ i : Fin 4, (3 + i.val, base (publicInput i)) ∈
      allYields (nativeRows trace) []) ∧
    (∀ i : Fin 4, (7 + i.val, base (publicOutput i)) ∈
      allYields (nativeRows trace) []) := by
  constructor
  · intro i
    let ix : Fin 512 := ⟨3 + i.val, by omega⟩
    have hr : row trace ix ∈ nativeRows trace := by
      exact List.mem_ofFn.mpr ⟨ix, rfl⟩
    have hm : 0 < (row trace ix).multiplicity := by
      fin_cases i <;> decide
    have hv : ((row trace ix).outAddress, (row trace ix).output) =
        (3 + i.val, base (publicInput i)) := by
      fin_cases i <;> decide
    rw [← hv]
    exact row_output_yield (nativeRows trace) [] (row trace ix) hr hm
  · intro i
    let ix : Fin 512 := ⟨7 + i.val, by omega⟩
    have hr : row trace ix ∈ nativeRows trace := by
      exact List.mem_ofFn.mpr ⟨ix, rfl⟩
    have hm : 0 < (row trace ix).multiplicity := by
      fin_cases i <;> decide
    have hv : ((row trace ix).outAddress, (row trace ix).output) =
        (7 + i.val, base (publicOutput i)) := by
      fin_cases i <;> decide
    rw [← hv]
    exact row_output_yield (nativeRows trace) [] (row trace ix) hr hm
def mutatedTrace : Trace 9 :=
  { trace with main := fun i c =>
      if i.val = 503 ∧ c.val = 8 then 1 else mainAt i c }

/-- A one-cell mutation of the second square's output violates a local
arithmetic polynomial at physical row 503. -/
theorem mutated_source_row_rejected :
    ¬ allArithmeticRootsZero mutatedTrace := by
  intro h
  have hlocal := h ⟨503, by decide⟩
  obtain ⟨op, hflags, hout⟩ := bytecode_zero_decodes
    (fromTrace mutatedTrace ⟨503, by decide⟩) hlocal
  rw [decoded_row_from_trace] at hflags hout
  have hactual : (row mutatedTrace ⟨503, by decide⟩).flags = encode .pointwiseMul ∧
      (row mutatedTrace ⟨503, by decide⟩).in0 = ⟨0, 1, 4, 49⟩ ∧
      (row mutatedTrace ⟨503, by decide⟩).in1 = ⟨0, 1, 4, 49⟩ ∧
      (row mutatedTrace ⟨503, by decide⟩).output = ⟨1, 1, 16, 2401⟩ := by
    decide
  have hop : op = .pointwiseMul := by
    have heq : encode op = encode .pointwiseMul := hflags.symm.trans hactual.1
    cases op <;> simp [encode] at heq ⊢
  subst op
  rw [hactual.2.2.2, hactual.2.1, hactual.2.2.1] at hout
  have hwrong : (⟨1, 1, 16, 2401⟩ : Quad) ≠
      evaluate .pointwiseMul ⟨0, 1, 4, 49⟩ ⟨0, 1, 4, 49⟩ := by decide
  exact hwrong hout

end S31.Functional.Correspondence.PinnedNativeSquare4Witness
