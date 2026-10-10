import S31.Gadgets.Functional.TextSquare4Witness

/-!
An honest assignment to every wire on the exported source program's selected
input-to-output path, for arbitrary four-word public input. Other native
component rows and proof commitments are outside this local completeness
statement.
-/

namespace S31.Functional.TextSquare4WitnessAll

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.TextSquare4NativeBoundary
open S31.Functional.TextSquare4NativeProof

private def lane (input : Fin 4 → M31) (i : Fin 4) : Quad :=
  base (Field.toZMod (input i))

private def packed (input : Fin 4 → M31) : Quad := packM31 input
private def squarePacked (input : Fin 4 → M31) : Quad :=
  packM31 (TextSquare4Air.square input)
private def fourthPacked (input : Fin 4 → M31) : Quad :=
  packM31 (TextSquare4Air.fourth input)

/-- Every selected address in the native fourth-power circuit has an honest
packed value. The default value concerns addresses outside the selected path. -/
def wire (input : Fin 4 → M31) : Nat → Quad
  | 0 => base 0
  | 1 => unit ⟨0, by decide⟩
  | 2 => unit ⟨2, by decide⟩
  | 3 => lane input ⟨0, by decide⟩
  | 4 => lane input ⟨1, by decide⟩
  | 5 => lane input ⟨2, by decide⟩
  | 6 => lane input ⟨3, by decide⟩
  | 7 => base (Field.toZMod (TextSquare4Air.fourth input ⟨0, by decide⟩))
  | 8 => base (Field.toZMod (TextSquare4Air.fourth input ⟨1, by decide⟩))
  | 9 => base (Field.toZMod (TextSquare4Air.fourth input ⟨2, by decide⟩))
  | 10 => base (Field.toZMod (TextSquare4Air.fourth input ⟨3, by decide⟩))
  | 11 => lane input ⟨0, by decide⟩
  | 12 => lane input ⟨1, by decide⟩
  | 13 => lane input ⟨2, by decide⟩
  | 14 => lane input ⟨3, by decide⟩
  | 15 => unit ⟨1, by decide⟩
  | 16 => unit ⟨3, by decide⟩
  | 17 => mul (unit ⟨1, by decide⟩) (lane input ⟨1, by decide⟩)
  | 18 => add (lane input ⟨0, by decide⟩)
      (mul (unit ⟨1, by decide⟩) (lane input ⟨1, by decide⟩))
  | 19 => mul (unit ⟨2, by decide⟩) (lane input ⟨2, by decide⟩)
  | 20 => add (wire input 18) (wire input 19)
  | 21 => mul (unit ⟨3, by decide⟩) (lane input ⟨3, by decide⟩)
  | 22 => packed input
  | 23 => squarePacked input
  | 24 => fourthPacked input
  | 25 => pointwise (fourthPacked input) (unit ⟨0, by decide⟩)
  | 26 => pointwise (fourthPacked input) (unit ⟨1, by decide⟩)
  | 27 => unitInverse ⟨1, by decide⟩
  | 28 => base (Field.toZMod (TextSquare4Air.fourth input ⟨1, by decide⟩))
  | 29 => pointwise (fourthPacked input) (unit ⟨2, by decide⟩)
  | 30 => unitInverse ⟨2, by decide⟩
  | 31 => base (Field.toZMod (TextSquare4Air.fourth input ⟨2, by decide⟩))
  | 32 => pointwise (fourthPacked input) (unit ⟨3, by decide⟩)
  | 33 => unitInverse ⟨3, by decide⟩
  | 34 => base (Field.toZMod (TextSquare4Air.fourth input ⟨3, by decide⟩))
  | _ => base 0

private theorem packed_from_parts (input : Fin 4 → M31) :
    add (wire input 20) (wire input 21) = packed input := by
  ext <;> simp [wire, packed, lane, packM31, add,
    S31.Gadgets.Packed.mul, unit, base]

private theorem first_square (input : Fin 4 → M31) :
    pointwise (packed input) (packed input) = squarePacked input := by
  simpa [packed, squarePacked, TextSquare4Air.square, s31Op, evaluate]
    using TextSquare4Air.pointwise_pack input input

private theorem second_square (input : Fin 4 → M31) :
    pointwise (squarePacked input) (squarePacked input) =
      fourthPacked input := by
  simpa [squarePacked, fourthPacked, TextSquare4Air.fourth,
    s31Op, evaluate] using
    TextSquare4Air.pointwise_pack
      (TextSquare4Air.square input) (TextSquare4Air.square input)

theorem input_complete (input : Fin 4 → M31) :
    inputBoundary (wire input) input := by
  constructor
  · simp [TextSquare4Native.zeroWire, wire]
  · intro i
    fin_cases i <;>
      simp [inputCopy, publicInputWire, wire, lane,
        TextSquare4Native.inputBindingAdd, TextSquare4Native.publicInputWires,
        accepts_encoded, evaluate, add, base]

theorem arithmetic_complete (input : Fin 4 → M31) :
    arithmeticGateRows (wire input) := by
  refine ⟨by simp [basisWire, TextSquare4Native.inputBasisWires, wire],
    by simp [basisWire, TextSquare4Native.inputBasisWires, wire],
    by simp [basisWire, TextSquare4Native.inputBasisWires, wire],
    ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [packMul, TextSquare4Native.inputPackMul, wire,
        accepts_encoded, evaluate]
  · intro i
    fin_cases i
    · simp [packAdd, TextSquare4Native.inputPackAdd, wire,
        accepts_encoded, evaluate]
    · simp [packAdd, TextSquare4Native.inputPackAdd, wire,
        accepts_encoded, evaluate]
    · change accepts (encode .add) (wire input 20) (wire input 21)
        (wire input 22)
      apply (accepts_encoded .add _ _ _).mpr
      simpa only [wire, evaluate] using (packed_from_parts input).symm
  · apply (accepts_encoded (s31Op true) _ _ _).mpr
    simpa [TextSquare4Native.first, wire, s31Op, evaluate]
      using (first_square input).symm
  · apply (accepts_encoded (s31Op true) _ _ _).mpr
    simpa [TextSquare4Native.second, wire, s31Op, evaluate]
      using (second_square input).symm

theorem output_complete (input : Fin 4 → M31) :
    nativeOutputRows (wire input) (TextSquare4Air.fourth input) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      simp [outputPoint, TextSquare4Native.outputUnpackPoint,
        wire, accepts_encoded, evaluate]
  · intro i
    fin_cases i
    · simp
    · constructor
      · simp [outputInverse, TextSquare4Native.outputUnpackMul, wire]
      · apply (accepts_encoded .mul _ _ _).mpr
        simpa [outputInverse, TextSquare4Native.outputUnpackMul, wire,
          fourthPacked, coord_packM31, evaluate] using
          (unpack_coordinate (fourthPacked input) ⟨1, by decide⟩).symm
    · constructor
      · simp [outputInverse, TextSquare4Native.outputUnpackMul, wire]
      · apply (accepts_encoded .mul _ _ _).mpr
        simpa [outputInverse, TextSquare4Native.outputUnpackMul, wire,
          fourthPacked, coord_packM31, evaluate] using
          (unpack_coordinate (fourthPacked input) ⟨2, by decide⟩).symm
    · constructor
      · simp [outputInverse, TextSquare4Native.outputUnpackMul, wire]
      · apply (accepts_encoded .mul _ _ _).mpr
        simpa [outputInverse, TextSquare4Native.outputUnpackMul, wire,
          fourthPacked, coord_packM31, evaluate] using
          (unpack_coordinate (fourthPacked input) ⟨3, by decide⟩).symm
  · intro i
    fin_cases i <;>
      simp [outputCopy, publicOutputWire,
        TextSquare4Native.outputBindingAdd,
        TextSquare4Native.publicOutputWires,
        wire, accepts_encoded, evaluate, add, base,
        pointwise, unit, fourthPacked, packM31]

/-- Every four-word public input has a satisfying assignment for the 23
selected native AIR rows and both public boundaries. -/
theorem native_path_complete (input : Fin 4 → M31) :
    ∃ witness : Nat → Quad,
      inputBoundary witness input ∧
      arithmeticGateRows witness ∧
      nativeOutputRows witness (TextSquare4Air.fourth input) :=
  ⟨wire input, input_complete input, arithmetic_complete input,
    output_complete input⟩

/-- The 23 selected native rows accept a public claim exactly when it is the
fourth power of the public input. This is a local AIR statement; it does not
assert completeness of the full STARK trace or proof protocol. -/
theorem native_path_iff (input claimed : Fin 4 → M31) :
    (∃ witness : Nat → Quad,
      inputBoundary witness input ∧
      arithmeticGateRows witness ∧
      nativeOutputRows witness claimed) ↔
    claimed = TextSquare4Air.fourth input := by
  constructor
  · rintro ⟨witness, hinput, harithmetic, houtput⟩
    exact native_public_claim_sound witness input claimed
      hinput harithmetic houtput
  · intro hclaim
    subst claimed
    exact native_path_complete input

end S31.Functional.TextSquare4WitnessAll
