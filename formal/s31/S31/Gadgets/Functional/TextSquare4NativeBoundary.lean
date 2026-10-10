import S31.Gadgets.Functional.TextSquare4NativeProof
import S31.Gadgets.Air.UnpackRows

/-!
Local public input/output boundary of the native direct circuit for
`functional_square4.s31`. The gate IDs are source-generated; all gate output
values remain arbitrary witnesses. These theorems model AIR acceptance,
not STARK opening or transcript soundness.
-/

namespace S31.Functional.TextSquare4NativeBoundary

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.TextSquare4NativeProof

def publicInputWire (i : Nat) : Nat := TextSquare4Native.publicInputWires[i]!
def publicOutputWire (i : Nat) : Nat := TextSquare4Native.publicOutputWires[i]!
def inputCopy (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.inputBindingAdd[i]!
def outputCopy (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.outputBindingAdd[i]!
def outputPoint (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.outputUnpackPoint[i]!
def outputInverse (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.outputUnpackMul[i]!
def unpackedWire (i : Fin 4) : Nat :=
  if i.val = 0 then (outputPoint 0).output else (outputInverse (i.val - 1)).output

/-- The four public input words are copied from the four scalar source wires
through native addition-with-zero gates. -/
def inputBoundary (wire : Nat → Quad) (input : Fin 4 → M31) : Prop :=
  wire TextSquare4Native.zeroWire = base 0 ∧
  ∀ i : Fin 4,
    accepts (encode .add)
      (wire ((inputCopy i.val).input0))
      (wire ((inputCopy i.val).input1))
      (wire ((inputCopy i.val).output)) ∧
    wire (publicInputWire i.val) = base (Field.toZMod (input i))

theorem input_scalar_bound (wire : Nat → Quad) (input : Fin 4 → M31)
    (h : inputBoundary wire input) (i : Fin 4) :
    wire (inputWire i.val) = base (Field.toZMod (input i)) := by
  rcases h with ⟨hzero, hrows⟩
  obtain ⟨hrow, hpublic⟩ := hrows i
  have hshape :
      (inputCopy i.val).input0 = inputWire i.val ∧
      (inputCopy i.val).input1 = TextSquare4Native.zeroWire ∧
      (inputCopy i.val).output = publicInputWire i.val := by
    fin_cases i <;> decide
  rw [hshape.1, hshape.2.1, hshape.2.2] at hrow
  have hrow' := (accepts_encoded .add _ _ _).mp hrow
  rw [hzero] at hrow'
  have heq : wire (publicInputWire i.val) = wire (inputWire i.val) := by
    simpa [evaluate, S31.Gadgets.Packed.add, base] using hrow'
  exact heq.symm.trans hpublic

/-- The three basis constants, six pack gates and two fourth-power gates.
Their outputs can be any QM31 field values. -/
def arithmeticGateRows (wire : Nat → Quad) : Prop :=
  wire (basisWire 0) = unit ⟨1, by decide⟩ ∧
  wire (basisWire 1) = unit ⟨2, by decide⟩ ∧
  wire (basisWire 2) = unit ⟨3, by decide⟩ ∧
  (∀ i : Fin 3, accepts (encode .mul)
    (wire ((packMul i.val).input0))
    (wire ((packMul i.val).input1))
    (wire ((packMul i.val).output))) ∧
  (∀ i : Fin 3, accepts (encode .add)
    (wire ((packAdd i.val).input0))
    (wire ((packAdd i.val).input1))
    (wire ((packAdd i.val).output))) ∧
  accepts (encode (s31Op true))
    (wire TextSquare4Native.first.input0)
    (wire TextSquare4Native.first.input1)
    (wire TextSquare4Native.first.output) ∧
  accepts (encode (s31Op true))
    (wire TextSquare4Native.second.input0)
    (wire TextSquare4Native.second.input1)
    (wire TextSquare4Native.second.output)

theorem arithmetic_result_sound (wire : Nat → Quad)
    (input : Fin 4 → M31)
    (hinput : inputBoundary wire input)
    (harithmetic : arithmeticGateRows wire) :
    wire TextSquare4Native.second.output =
      packM31 (TextSquare4Air.fourth input) := by
  rcases harithmetic with ⟨hb1, hb2, hb3, hm, ha, hfirst, hsecond⟩
  have hpack : nativePackRows wire input :=
    ⟨input_scalar_bound wire input hinput ⟨0, by decide⟩,
     input_scalar_bound wire input hinput ⟨1, by decide⟩,
     input_scalar_bound wire input hinput ⟨2, by decide⟩,
     input_scalar_bound wire input hinput ⟨3, by decide⟩,
     hb1, hb2, hb3, hm, ha⟩
  exact native_rows_sound wire input ⟨hpack, hfirst, hsecond⟩

/-- Four coordinate extracts from the result wire, followed by four native
addition-with-zero gates into the public output slots. -/
def outputBoundary (wire : Nat → Quad) (claimed : Fin 4 → M31) : Prop :=
  (∀ i : Fin 4, S31.Gadgets.Air.UnpackRows.acceptsUnpack i
    (wire TextSquare4Native.second.output) (wire (unpackedWire i))) ∧
  (∀ i : Fin 4,
    accepts (encode .add)
      (wire ((outputCopy i.val).input0))
      (wire ((outputCopy i.val).input1))
      (wire ((outputCopy i.val).output)) ∧
    wire (publicOutputWire i.val) = base (Field.toZMod (claimed i)))

/-- No satisfying native local circuit witness can expose a forged public
result when the public input words and fixed basis/zero wires are bound. -/
theorem public_claim_sound (wire : Nat → Quad)
    (input claimed : Fin 4 → M31)
    (hinput : inputBoundary wire input)
    (harithmetic : arithmeticGateRows wire)
    (houtput : outputBoundary wire claimed) :
    claimed = TextSquare4Air.fourth input := by
  funext i
  have hzero := hinput.1
  have hresult := arithmetic_result_sound wire input hinput harithmetic
  obtain ⟨hunpackRows, hcopyRows⟩ := houtput
  have hunpacked := (S31.Gadgets.Air.UnpackRows.acceptsUnpack_iff i
    (wire TextSquare4Native.second.output) (wire (unpackedWire i))).mp
      (hunpackRows i)
  obtain ⟨hcopy, hpublic⟩ := hcopyRows i
  have hshape :
      (outputCopy i.val).input0 = unpackedWire i ∧
      (outputCopy i.val).input1 = TextSquare4Native.zeroWire ∧
      (outputCopy i.val).output = publicOutputWire i.val := by
    fin_cases i <;> decide
  rw [hshape.1, hshape.2.1, hshape.2.2] at hcopy
  have hcopy' := (accepts_encoded .add _ _ _).mp hcopy
  rw [hzero] at hcopy'
  have heq : wire (publicOutputWire i.val) = wire (unpackedWire i) := by
    simpa [evaluate, S31.Gadgets.Packed.add, base] using hcopy'
  have hfield : Field.toZMod (claimed i) =
      coord (wire TextSquare4Native.second.output) i := by
    exact congrArg Quad.a (hpublic.symm.trans (heq.trans hunpacked))
  rw [hresult, coord_packM31] at hfield
  exact Field.toZMod_injective hfield

/-- The exact emitted output gates: four pointwise masks, three inverse-basis
multiplications, and four additions into public output slots. Each gate is
checked as a local AIR row; every intermediate wire is an arbitrary witness. -/
def nativeOutputRows (wire : Nat → Quad) (claimed : Fin 4 → M31) : Prop :=
  (∀ i : Fin 4,
    wire ((outputPoint i.val).input1) = unit i ∧
    accepts (encode .pointwiseMul)
      (wire ((outputPoint i.val).input0))
      (wire ((outputPoint i.val).input1))
      (wire ((outputPoint i.val).output))) ∧
  (∀ i : Fin 4, if i.val = 0 then True else
    wire ((outputInverse (i.val - 1)).input1) = unitInverse i ∧
    accepts (encode .mul)
      (wire ((outputInverse (i.val - 1)).input0))
      (wire ((outputInverse (i.val - 1)).input1))
      (wire ((outputInverse (i.val - 1)).output))) ∧
  (∀ i : Fin 4,
    accepts (encode .add)
      (wire ((outputCopy i.val).input0))
      (wire ((outputCopy i.val).input1))
      (wire ((outputCopy i.val).output)) ∧
    wire (publicOutputWire i.val) = base (Field.toZMod (claimed i)))

theorem native_output_boundary (wire : Nat → Quad)
    (claimed : Fin 4 → M31) (h : nativeOutputRows wire claimed) :
    outputBoundary wire claimed := by
  rcases h with ⟨hpoint, hinverse, hcopy⟩
  refine ⟨?_, hcopy⟩
  intro i
  refine ⟨wire ((outputPoint i.val).output), ?_, ?_⟩
  · obtain ⟨hunit, hrow⟩ := hpoint i
    have hshape : (outputPoint i.val).input0 =
        TextSquare4Native.second.output := by
      fin_cases i <;> decide
    simpa only [hshape, hunit] using hrow
  · by_cases hi : i.val = 0
    · simp only [hi, ↓reduceIte]
      simp [unpackedWire, hi]
    · simp only [hi, ↓reduceIte]
      have hrow := hinverse i
      simp only [hi, ↓reduceIte] at hrow
      obtain ⟨hunit, hmul⟩ := hrow
      have hshape :
          (outputInverse (i.val - 1)).input0 = (outputPoint i.val).output ∧
          (outputInverse (i.val - 1)).output = unpackedWire i := by
        fin_cases i <;> simp_all [unpackedWire, outputPoint, outputInverse,
          TextSquare4Native.outputUnpackPoint, TextSquare4Native.outputUnpackMul]
      simpa only [hshape.1, hshape.2, hunit] using hmul

/-- Full local-row soundness of the source-generated native direct circuit,
from four public inputs through packing, two arithmetic nodes, unpacking,
and four public outputs. -/
theorem native_public_claim_sound (wire : Nat → Quad)
    (input claimed : Fin 4 → M31)
    (hinput : inputBoundary wire input)
    (harithmetic : arithmeticGateRows wire)
    (houtput : nativeOutputRows wire claimed) :
    claimed = TextSquare4Air.fourth input :=
  public_claim_sound wire input claimed hinput harithmetic
    (native_output_boundary wire claimed houtput)

end S31.Functional.TextSquare4NativeBoundary
