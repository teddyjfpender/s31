import S31.Gadgets.Air.DirectGateNativeIndices
import S31.Gadgets.Air.NativeQm31AirProof

/-!
An algebraic evaluator for one decoded direct `qm31_ops` row. The fixed
columns are supplied in the *captured AIR's local read order*; main and
interaction columns are supplied in their selected component spans. This
module proves the 9 + 2 residual formulas and the column permutation for
arbitrary cells. It does not prove that a native proof opens these cells, or
that the installed `STWZEVA/1` bytecode equals this evaluator.
-/

namespace S31.Gadgets.Air.DirectGateEvaluatorCells

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.NativeGateRawSoundness
open S31.Gadgets.Air.NativeQm31AirProof
open S31.Gadgets.Air.GateLogUpBridge
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateNativeIndices
open S31.Gadgets.Air.GateChallenge

/-- The selected component's current local reads and previous interaction
read. `previousInteraction` is selected with the installed `at_prev` mask;
matching that mask to `directPrevious` remains a separate premise. -/
structure Cells where
  localFixed : Fin 8 → F
  main : Fin 12 → F
  interaction : Fin 8 → F
  previousInteraction : Fin 8 → F

def semanticFixed (cells : Cells) (index : Fin 8) : F :=
  cells.localFixed (fixedReadOrder.symm index)

def decodedRow (cells : Cells) : Row :=
  { in0Address := (semanticFixed cells 4).val,
    in1Address := (semanticFixed cells 5).val,
    outAddress := (semanticFixed cells 6).val,
    flags := ⟨semanticFixed cells 0, semanticFixed cells 1,
      semanticFixed cells 2, semanticFixed cells 3⟩,
    in0 := ⟨cells.main 0, cells.main 1, cells.main 2, cells.main 3⟩,
    in1 := ⟨cells.main 4, cells.main 5, cells.main 6, cells.main 7⟩,
    output := ⟨cells.main 8, cells.main 9, cells.main 10, cells.main 11⟩,
    multiplicity := (semanticFixed cells 7).val }

def firstColumn (cells : Cells) : GateSecure :=
  ⟨⟨cells.interaction 0, cells.interaction 1⟩,
    ⟨cells.interaction 2, cells.interaction 3⟩⟩

def lastColumn (cells : Cells) : GateSecure :=
  ⟨⟨cells.interaction 4, cells.interaction 5⟩,
    ⟨cells.interaction 6, cells.interaction 7⟩⟩

def previousLastColumn (cells : Cells) : GateSecure :=
  ⟨⟨cells.previousInteraction 4, cells.previousInteraction 5⟩,
    ⟨cells.previousInteraction 6, cells.previousInteraction 7⟩⟩

/-- The nine local arithmetic constraints from the Zig-exported
`qm31_ops_constraint_trees`, evaluated on the selected cells. -/
def arithmetic (cells : Cells) : List F :=
  let gate := decodedRow cells
  NativeQm31Air.residuals gate.flags gate.in0 gate.in1 gate.output

/-- Nine zero local residuals determine the operation and output value for
these decoded cells. The premise is a field equality, not a PCS claim. -/
theorem arithmetic_zero_decodes (cells : Cells)
    (hzero : ∀ residual ∈ arithmetic cells, residual = 0) :
    ∃ op, (decodedRow cells).flags = encode op ∧
      (decodedRow cells).output = evaluate op
        (decodedRow cells).in0 (decodedRow cells).in1 := by
  exact (native_accepts_iff (decodedRow cells).flags
    (decodedRow cells).in0 (decodedRow cells).in1
    (decodedRow cells).output).mp hzero

/-- The two ordered LogUp batch constraints. These formulas are independent
of the native claimed-sum and transcript binding. -/
def pair (cells : Cells) (alpha z : GateSecure) : GateSecure :=
  NativeLogUpAir.pair
    (nativeRowPair (decodedRow cells) alpha z).1
    (nativeRowPair (decodedRow cells) alpha z).2
    (firstColumn cells)

def last (cells : Cells) (alpha z claimed : GateSecure)
    (rowCount : Nat) : GateSecure :=
  NativeLogUpAir.single
    (nativeYieldTerm (decodedRow cells) alpha z)
    (lastColumn cells - previousLastColumn cells - firstColumn cells +
      claimed / (rowCount : GateSecure))

def fromTrace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) : Cells :=
  { localFixed := airLocalFixed trace index,
    main := trace.main index,
    interaction := trace.interaction index,
    previousInteraction := trace.interaction (trace.prev index) }

theorem semantic_fixed_from_trace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) (column : Fin 8) :
    semanticFixed (fromTrace trace index) column =
      trace.fixed index column := by
  exact local_fixed_at_semantic trace index column

theorem decoded_row_from_trace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) :
    decodedRow (fromTrace trace index) = row trace index := by
  simp [decodedRow, fromTrace, semanticFixed, airLocalFixed,
    fixedReadOrder, semantic_local_inverse, row]

theorem arithmetic_from_trace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) :
    arithmetic (fromTrace trace index) =
      NativeQm31Air.residuals (row trace index).flags
        (row trace index).in0 (row trace index).in1
        (row trace index).output := by
  simp [arithmetic, decoded_row_from_trace]

theorem pair_from_trace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) (alpha z : GateSecure) :
    pair (fromTrace trace index) alpha z =
      NativeLogUpAir.pair
        (nativeRowPair (row trace index) alpha z).1
        (nativeRowPair (row trace index) alpha z).2
        (DecodedDirectGateTrace.firstColumn trace index) := by
  rw [pair, decoded_row_from_trace]
  rfl

theorem last_from_trace {logSize : Nat} (trace : Trace logSize)
    (index : Fin (2 ^ logSize)) (alpha z : GateSecure) :
    last (fromTrace trace index) alpha z trace.claimed (2 ^ logSize) =
      NativeLogUpAir.single
        (nativeYieldTerm (row trace index) alpha z)
        (DecodedDirectGateTrace.lastColumn trace index -
          DecodedDirectGateTrace.lastColumn trace (trace.prev index) -
          DecodedDirectGateTrace.firstColumn trace index +
          trace.claimed / ((2 ^ logSize : Nat) : GateSecure)) := by
  rw [last, decoded_row_from_trace]
  rfl

/-- The only evaluator premise here is that the selected native program's
two outputs equal this explicit pure model at each authenticated row. All
cryptographic row binding and claimed-sum closure remain separate premises. -/
theorem modeled_evaluator_to_raw_accepts {logSize : Nat}
    (trace : Trace logSize) (alpha z : GateSecure)
    (hInstalledEvaluator : ∀ index,
      trace.airPair index = pair (fromTrace trace index) alpha z ∧
      trace.airLast index =
        last (fromTrace trace index) alpha z trace.claimed (2 ^ logSize))
    (hAuthenticatedRows : ∀ index,
      trace.airPair index = 0 ∧ trace.airLast index = 0)
    (hPublicClosure : trace.claimed +
      productionReciprocalSum trace.externalUses alpha z -
      productionReciprocalSum trace.externalYields alpha z = 0) :
    GateAirRawSoundness.rawInteractionAccepts logSize trace.prev (row trace)
      trace.externalUses trace.externalYields alpha z := by
  apply decoded_cells_to_raw_accepts trace alpha z
  · intro index
    rw [(hInstalledEvaluator index).1, pair_from_trace]
  · intro index
    rw [(hInstalledEvaluator index).2, last_from_trace]
  · exact hAuthenticatedRows
  · exact hPublicClosure

end S31.Gadgets.Air.DirectGateEvaluatorCells
