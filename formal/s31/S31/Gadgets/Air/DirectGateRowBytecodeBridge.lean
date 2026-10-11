import S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
import S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
import S31.Gadgets.Air.DirectGateOodsMask

/-!
Selected Gate row correspondence for all M31 cell values. The installed
`STWZEVA/1` bytecode's eleven generated roots are reduced to the existing
pure row evaluator after embedding each M31 column value in QM31. The
previous interaction cells are selected using the proved 512-row mask
permutation. This is a local evaluator identity; native opcode execution,
committed rows, PCS/FRI, and all-row zero constraints remain separate.
-/

namespace S31.Gadgets.Air.DirectGateRowBytecodeBridge

open S31.Gadgets.Packed
open S31.Gadgets.Air.DirectGateOodsArithmetic
open S31.Gadgets.Air.DirectGateOodsLogUp
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic
open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Gadgets.Air.DirectGateOodsMask

abbrev RowCells := S31.Gadgets.Air.DirectGateEvaluatorCells.Cells
abbrev RowTrace := S31.Gadgets.Air.DecodedDirectGateTrace.Trace 9

/-- The native row evaluator reads M31 trace columns and injects them into
QM31 for its extension instructions. -/
def liftCells (cells : RowCells) : Cells where
  localFixed i := liftBase (cells.localFixed i)
  main i := liftBase (cells.main i)
  interaction i := liftBase (cells.interaction i)
  previousInteraction i := liftBase (cells.previousInteraction i)

private theorem liftBase_zero : liftBase 0 = (0 : QM) := by
  rfl

private theorem liftBase_one : liftBase 1 = (1 : QM) := by
  rfl

private theorem liftBase_add (a b : F) :
    liftBase (a + b) = liftBase a + liftBase b := by
  ext <;> simp [liftBase]

private theorem liftBase_natCast (n : Nat) :
    liftBase (n : F) = (n : QM) := by
  induction n with
  | zero => exact liftBase_zero
  | succ n ih =>
      rw [Nat.cast_succ, liftBase_add, ih]
      simp [liftBase_one]

private theorem liftBase_eq_zmodCast (value : F) :
    liftBase value = (ZMod.cast value : QM) := by
  calc
    liftBase value = liftBase (value.val : F) := by
      rw [ZMod.natCast_zmod_val]
    _ = (value.val : QM) := liftBase_natCast value.val
    _ = ZMod.cast value := (ZMod.cast_eq_val value).symm

/-- Reassembly of four M31 row limbs is the same QM31 value as the existing
Gate row model's packed secure-field column. -/
theorem decode_lifted_limbs (a b c d : F) :
    fromPartialEvals (liftBase a) (liftBase b)
      (liftBase c) (liftBase d) =
        (⟨⟨a, b⟩, ⟨c, d⟩⟩ : QM) := by
  ext <;> simp [fromPartialEvals, liftBase, basisI, basisU, basisIU]

private theorem denominator_lifted (address a b c d : F)
    (alpha z : QM) :
    denominator (liftBase address) (liftBase a) (liftBase b)
      (liftBase c) (liftBase d) alpha z =
      S31.Gadgets.Air.NativeLogUpAir.combine
        (gateTuple address ⟨a, b, c, d⟩) alpha z := by
  simp [denominator, S31.Gadgets.Air.NativeLogUpAir.combine,
    gateTuple, liftBase]
  rfl

private theorem input_zero_denominator_at_row (cells : RowCells)
    (alpha z : QM) :
    inputZeroDenominator (liftCells cells) alpha z =
      (S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair
        (S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow cells)
        alpha z).1.denominator := by
  simp [inputZeroDenominator, liftCells,
    S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair,
    S31.Gadgets.Air.NativeGateRawSoundness.nativeUseTerm,
    S31.Gadgets.Air.GateChallenge.eventTuple,
    S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow,
    S31.Gadgets.Air.DirectGateEvaluatorCells.semanticFixed,
    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal,
    denominator_lifted]

private theorem input_one_denominator_at_row (cells : RowCells)
    (alpha z : QM) :
    inputOneDenominator (liftCells cells) alpha z =
      (S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair
        (S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow cells)
        alpha z).2.denominator := by
  simp [inputOneDenominator, liftCells,
    S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair,
    S31.Gadgets.Air.NativeGateRawSoundness.nativeUseTerm,
    S31.Gadgets.Air.GateChallenge.eventTuple,
    S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow,
    S31.Gadgets.Air.DirectGateEvaluatorCells.semanticFixed,
    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal,
    denominator_lifted]

private theorem output_denominator_at_row (cells : RowCells)
    (alpha z : QM) :
    outputDenominator (liftCells cells) alpha z =
      (S31.Gadgets.Air.NativeGateRawSoundness.nativeYieldTerm
        (S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow cells)
        alpha z).denominator := by
  simp [outputDenominator, liftCells,
    S31.Gadgets.Air.NativeGateRawSoundness.nativeYieldTerm,
    S31.Gadgets.Air.GateChallenge.eventTuple,
    S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow,
    S31.Gadgets.Air.DirectGateEvaluatorCells.semanticFixed,
    S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
    S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal,
    denominator_lifted]

/-- At every M31 row, the two selected bytecode LogUp roots equal the pure
Gate pair and singleton residuals. The claim scaling is the same native
`claimed / rowCount` extension parameter. -/
theorem bytecode_logup_at_row (cells : RowCells) (alpha z claimed : QM)
    (rowCount : Nat) :
    bytecodeLogup (liftCells cells) alpha z (claimed / rowCount) =
      (S31.Gadgets.Air.DirectGateEvaluatorCells.pair cells alpha z,
       S31.Gadgets.Air.DirectGateEvaluatorCells.last cells alpha z
         claimed rowCount) := by
  have hfirst : firstColumn (liftCells cells) =
      S31.Gadgets.Air.DirectGateEvaluatorCells.firstColumn cells := by
    simp [firstColumn, liftCells,
      S31.Gadgets.Air.DirectGateEvaluatorCells.firstColumn,
      decode_lifted_limbs]
  have hlast : lastColumn (liftCells cells) =
      S31.Gadgets.Air.DirectGateEvaluatorCells.lastColumn cells := by
    simp [lastColumn, liftCells,
      S31.Gadgets.Air.DirectGateEvaluatorCells.lastColumn,
      decode_lifted_limbs]
  have hprevious : previousLastColumn (liftCells cells) =
      S31.Gadgets.Air.DirectGateEvaluatorCells.previousLastColumn cells := by
    simp [previousLastColumn, liftCells,
      S31.Gadgets.Air.DirectGateEvaluatorCells.previousLastColumn,
      decode_lifted_limbs]
  rw [bytecode_logup_eq]
  apply Prod.ext
  · simp only [pair, S31.Gadgets.Air.DirectGateEvaluatorCells.pair,
      S31.Gadgets.Air.NativeLogUpAir.pair]
    rw [hfirst, input_zero_denominator_at_row,
      input_one_denominator_at_row]
    simp [S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair,
      S31.Gadgets.Air.NativeGateRawSoundness.nativeUseTerm]
  · simp only [last, S31.Gadgets.Air.DirectGateEvaluatorCells.last,
      S31.Gadgets.Air.NativeLogUpAir.single]
    rw [hfirst, hlast, hprevious, output_denominator_at_row]
    simp [S31.Gadgets.Air.NativeGateRawSoundness.nativeYieldTerm,
      S31.Gadgets.Air.DirectGateEvaluatorCells.decodedRow,
      S31.Gadgets.Air.DirectGateEvaluatorCells.semanticFixed,
      S31.Gadgets.Air.DirectGateNativeIndices.fixedReadOrder,
      S31.Gadgets.Air.DirectGateNativeIndices.semanticToAirLocal,
      liftCells]
    exact liftBase_eq_zmodCast (cells.localFixed 7)

/-- All eleven selected bytecode roots at any of the 512 trace rows agree
with the existing Gate row formulas. The nine arithmetic roots live in M31;
the two LogUp roots live in QM31 after lifting row cells. -/
theorem bytecode_residuals_at_any_row (trace : RowTrace)
    (index : Fin 512) (alpha z : QM) :
    bytecodeArithmetic
      (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index) =
        S31.Gadgets.Air.NativeQm31Air.residuals
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).flags
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).in0
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).in1
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).output ∧
    bytecodeLogup (liftCells
      (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index))
        alpha z (trace.claimed / 512) =
      (S31.Gadgets.Air.NativeLogUpAir.pair
        (S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index)
          alpha z).1
        (S31.Gadgets.Air.NativeGateRawSoundness.nativeRowPair
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index)
          alpha z).2
        (S31.Gadgets.Air.DecodedDirectGateTrace.firstColumn trace index),
       S31.Gadgets.Air.NativeLogUpAir.single
        (S31.Gadgets.Air.NativeGateRawSoundness.nativeYieldTerm
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index)
          alpha z)
        (S31.Gadgets.Air.DecodedDirectGateTrace.lastColumn trace index -
          S31.Gadgets.Air.DecodedDirectGateTrace.lastColumn trace
            (trace.prev index) -
          S31.Gadgets.Air.DecodedDirectGateTrace.firstColumn trace index +
          trace.claimed / (512 : QM))) := by
  constructor
  · rw [bytecode_arithmetic_eq]
    exact S31.Gadgets.Air.DirectGateEvaluatorCells.arithmetic_from_trace
      trace index
  · calc
      bytecodeLogup (liftCells
        (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index))
          alpha z (trace.claimed / 512) =
        (S31.Gadgets.Air.DirectGateEvaluatorCells.pair
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
          alpha z,
         S31.Gadgets.Air.DirectGateEvaluatorCells.last
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
          alpha z trace.claimed 512) := by
            exact bytecode_logup_at_row
              (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
              alpha z trace.claimed 512
      _ = _ := by
        apply Prod.ext
        · exact S31.Gadgets.Air.DirectGateEvaluatorCells.pair_from_trace
            trace index alpha z
        · simpa only [show (2 ^ 9 : Nat) = 512 by decide] using
            S31.Gadgets.Air.DirectGateEvaluatorCells.last_from_trace
              trace index alpha z

/-- A row's `at_prev` value is the interaction value at the selected
bit-reversed circle-domain predecessor, in bytecode mask slot zero. The
native row-index implementation is checked separately by its exhaustive
512-index Zig test. -/
theorem selected_previous_mask_at_row (trace : RowTrace)
    (hprev : trace.prev = directPrevious512)
    (index : Fin 512) (column : Fin 8) (hcolumn : 4 ≤ column.val) :
    interactionMaskRead
      (fun c => rowMask
        (fun i c => liftBase (trace.interaction i c)) index c)
      column (-1) =
      some ((liftCells
        (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
        ).previousInteraction column) := by
  rw [row_mask_previous _ index column hcolumn]
  simp [liftCells, S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace,
    hprev]

/-- The corresponding current sample is bytecode mask slot one for the last
four columns and slot zero for the first four. -/
theorem selected_current_mask_at_row (trace : RowTrace)
    (index : Fin 512) (column : Fin 8) :
    interactionMaskRead
      (fun c => rowMask
        (fun i c => liftBase (trace.interaction i c)) index c)
      column 0 =
      some ((liftCells
        (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
        ).interaction column) := by
  rw [row_mask_current]
  rfl

/-- Once a separately authenticated all-row argument supplies zero *native
bytecode* arithmetic outputs, every decoded row has one valid Gate operation
and its stated output. This theorem does not infer the zero premise from a
single OODS check or a proof flag. -/
theorem bytecode_zero_rows_decode (trace : RowTrace)
    (hzero : ∀ index : Fin 512, ∀ residual ∈ bytecodeArithmetic
      (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index),
      residual = 0) :
    ∀ index : Fin 512, ∃ op,
      (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).flags =
        S31.Gadgets.Air.Qm31Ops.encode op ∧
      (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).output =
        S31.Gadgets.Air.Qm31Ops.evaluate op
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).in0
          (S31.Gadgets.Air.DecodedDirectGateTrace.row trace index).in1 := by
  intro index
  have h := bytecode_zero_decodes
    (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
    (hzero index)
  rwa [S31.Gadgets.Air.DirectGateEvaluatorCells.decoded_row_from_trace] at h

/-- The older generic evaluator premise is discharged when the trace's pair
and singleton outputs are those of the installed bytecode at every row. The
remaining zero-row and public-closure premises are still external proof
obligations. -/
theorem bytecode_outputs_to_raw_accepts (trace : RowTrace)
    (alpha z : QM) (hprev : trace.prev = directPrevious512)
    (hBytecodeOutputs : ∀ index : Fin 512,
      let outputs := bytecodeLogup
        (liftCells
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index))
        alpha z (trace.claimed / (2 ^ 9 : Nat))
      trace.airPair index = outputs.1 ∧ trace.airLast index = outputs.2)
    (hAuthenticatedRows : ∀ index : Fin 512,
      trace.airPair index = 0 ∧ trace.airLast index = 0)
    (hPublicClosure : trace.claimed +
      S31.Gadgets.Air.GateLogUpBridge.productionReciprocalSum
        trace.externalUses alpha z -
      S31.Gadgets.Air.GateLogUpBridge.productionReciprocalSum
        trace.externalYields alpha z = 0) :
    S31.Gadgets.Air.GateAirRawSoundness.rawInteractionAccepts
      9 directPrevious512 (S31.Gadgets.Air.DecodedDirectGateTrace.row trace)
      trace.externalUses trace.externalYields alpha z := by
  have hmodeled : ∀ index,
      trace.airPair index =
        S31.Gadgets.Air.DirectGateEvaluatorCells.pair
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
          alpha z ∧
      trace.airLast index =
        S31.Gadgets.Air.DirectGateEvaluatorCells.last
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index)
          alpha z trace.claimed (2 ^ 9) := by
    intro index
    simpa only [bytecode_logup_at_row] using hBytecodeOutputs index
  have hraw :=
    S31.Gadgets.Air.DirectGateEvaluatorCells.modeled_evaluator_to_raw_accepts
      trace alpha z hmodeled hAuthenticatedRows hPublicClosure
  rw [hprev] at hraw
  exact hraw

end S31.Gadgets.Air.DirectGateRowBytecodeBridge
