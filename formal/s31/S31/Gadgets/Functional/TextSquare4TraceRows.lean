import S31.Gadgets.Functional.TextSquare4GateJoin

/-!
The selected rows in the production circuit's padded QM31 AIR component.
Their indices and fixed flag/address/multiplicity columns are checked by the
native exporter against `PreprocessedCircuit.fromCircuit`. The actual trace
operands and local AIR acceptance remain explicit witness premises here.
-/

namespace S31.Functional.TextSquare4TraceRows

open S31
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.TextSquare4NativeBoundary
open S31.Functional.TextSquare4NativeProof
open S31.Functional.TextSquare4GateJoin

def matchesGate (row : Row) (gate : TextSquare4Native.Gate)
    (op : S31.Gadgets.Air.Qm31Ops.Op) : Prop :=
  row.in0Address = gate.input0 ∧
  row.in1Address = gate.input1 ∧
  row.outAddress = gate.output ∧
  row.flags = encode op ∧
  0 < row.multiplicity ∧
  accepts row.flags row.in0 row.in1 row.output

def atGate
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (index : Nat) (gate : TextSquare4Native.Gate)
    (op : S31.Gadgets.Air.Qm31Ops.Op) : Prop :=
  ∃ hindex : index < TextSquare4Native.paddedArithmeticRowCount,
    matchesGate (rows ⟨index, hindex⟩) gate op

theorem atGate_hasGate
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (index : Nat) (gate : TextSquare4Native.Gate)
    (op : S31.Gadgets.Air.Qm31Ops.Op)
    (h : atGate rows index gate op) :
    hasGate (List.ofFn rows) gate op := by
  obtain ⟨hindex, hmatch⟩ := h
  refine ⟨rows ⟨index, hindex⟩, by simp, ?_⟩
  exact hmatch

/-- The index schedule checked against the production preprocessed columns:
add rows start at zero, mul rows at `mulRowStart`, and pointwise rows at
`pointRowStart`. The compiler's padding appends add rows before the latter
two groups, which is why the fourth-power rows are 502 and 503. -/
def selectedRows
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row) : Prop :=
  (∀ i : Fin 4, atGate rows (3 + i.val) (inputCopy i.val) .add) ∧
  (∀ i : Fin 3, atGate rows
    (TextSquare4Native.mulRowStart + i.val) (packMul i.val) .mul) ∧
  (∀ i : Fin 3, atGate rows i.val (packAdd i.val) .add) ∧
  atGate rows TextSquare4Native.pointRowStart
    TextSquare4Native.first (s31Op true) ∧
  atGate rows (TextSquare4Native.pointRowStart + 1)
    TextSquare4Native.second (s31Op true) ∧
  (∀ i : Fin 4, atGate rows
    (TextSquare4Native.pointRowStart + 2 + i.val)
    (outputPoint i.val) .pointwiseMul) ∧
  (∀ i : Fin 4, if i.val = 0 then True else
    atGate rows (TextSquare4Native.mulRowStart + 3 + (i.val - 1))
      (outputInverse (i.val - 1)) .mul) ∧
  (∀ i : Fin 4, atGate rows (7 + i.val) (outputCopy i.val) .add)

theorem selected_rows_imply_path
    (rows : Fin TextSquare4Native.paddedArithmeticRowCount → Row)
    (h : selectedRows rows) :
    nativePathRows (List.ofFn rows) := by
  rcases h with ⟨hinput, hpackMul, hpackAdd, hfirst, hsecond,
    hpoint, hinverse, houtput⟩
  refine ⟨(fun i => atGate_hasGate rows _ _ .add (hinput i)),
    (fun i => atGate_hasGate rows _ _ .mul (hpackMul i)),
    (fun i => atGate_hasGate rows _ _ .add (hpackAdd i)),
    atGate_hasGate rows _ _ (s31Op true) hfirst,
    atGate_hasGate rows _ _ (s31Op true) hsecond,
    (fun i => atGate_hasGate rows _ _ .pointwiseMul (hpoint i)),
    ?_,
    (fun i => atGate_hasGate rows _ _ .add (houtput i))⟩
  intro i
  by_cases hi : i.val = 0
  · simp [hi]
  · simp only [hi, ↓reduceIte]
    have hrow := hinverse i
    simp only [hi, ↓reduceIte] at hrow
    exact atGate_hasGate rows _ _ .mul hrow

theorem native_square_row_indices :
    TextSquare4Native.pointRowStart = 502 ∧
    TextSquare4Native.pointRowStart + 1 = 503 ∧
    TextSquare4Native.paddedArithmeticRowCount = 512 := by
  decide

end S31.Functional.TextSquare4TraceRows
