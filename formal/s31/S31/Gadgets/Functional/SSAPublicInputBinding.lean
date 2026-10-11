import S31.Gadgets.Functional.SSAInputAirCells
import S31.Gadgets.Air.PackRows

/-!
The value side of the bounded direct-gate public-input boundary. The earlier
cell lemmas determine row selectors and addresses; here `wire` remains an
arbitrary assignment. The four public ABI pins, fixed zero/basis wires, and
local AIR acceptance are explicit premises. In particular, this theorem does
not prove that a commitment opens to `wire`, or that Gate lookup connects
the local rows to the corresponding address values.
-/

namespace S31.Functional.SSAPublicInputBinding

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAInputAirCells

structure InputBoundary (certificate : Certificate) (totalAddRows : Nat)
    (wire : Nat → Quad) (input : Fin 4 → M31) : Prop where
  zero : wire 0 = base 0
  copies : ∀ i : Fin 4, accepts (encode .add)
    (wire ((expectedInputCopyCell certificate i.val).in0))
    (wire ((expectedInputCopyCell certificate i.val).in1))
    (wire ((expectedInputCopyCell certificate i.val).out))
  pins : ∀ i : Fin 4, wire (3 + i.val) = base (Field.toZMod (input i))
  basis1 : wire 15 = unit ⟨1, by decide⟩
  basis2 : wire 2 = unit ⟨2, by decide⟩
  basis3 : wire 16 = unit ⟨3, by decide⟩
  packMuls : ∀ i : Fin 3, accepts (encode .mul)
    (wire ((expectedPackMulCell totalAddRows i.val).in0))
    (wire ((expectedPackMulCell totalAddRows i.val).in1))
    (wire ((expectedPackMulCell totalAddRows i.val).out))
  packAdds : ∀ i : Fin 3, accepts (encode .add)
    (wire ((expectedPackAddCell certificate i.val).in0))
    (wire ((expectedPackAddCell certificate i.val).in1))
    (wire ((expectedPackAddCell certificate i.val).out))

/-- A public pin and its addition-with-zero row determine each scalar input
wire, for an arbitrary witness assignment and admitted SSA certificate. -/
theorem input_copy_scalar_bound (certificate : Certificate)
    (totalAddRows : Nat) (wire : Nat → Quad) (input : Fin 4 → M31)
    (h : InputBoundary certificate totalAddRows wire input) (i : Fin 4) :
    wire (11 + i.val) = base (Field.toZMod (input i)) := by
  have hrow := h.copies i
  change accepts (encode .add) (wire (11 + i.val)) (wire 0)
    (wire (3 + i.val)) at hrow
  have hrow' := (accepts_encoded .add _ _ _).mp hrow
  rw [h.zero] at hrow'
  have heq : wire (3 + i.val) = wire (11 + i.val) := by
    simpa [evaluate, S31.Gadgets.Packed.add, base] using hrow'
  exact heq.symm.trans (h.pins i)

/-- The six emitted input pack rows make native wire 22 equal the public
four-lane M31 input, under the public pins and fixed basis/zero premises. -/
theorem packed_input_bound (certificate : Certificate)
    (totalAddRows : Nat) (wire : Nat → Quad) (input : Fin 4 → M31)
    (h : InputBoundary certificate totalAddRows wire input) :
    wire 22 = packM31 input := by
  have hi0 := input_copy_scalar_bound certificate totalAddRows wire input h ⟨0, by decide⟩
  have hi1 := input_copy_scalar_bound certificate totalAddRows wire input h ⟨1, by decide⟩
  have hi2 := input_copy_scalar_bound certificate totalAddRows wire input h ⟨2, by decide⟩
  have hi3 := input_copy_scalar_bound certificate totalAddRows wire input h ⟨3, by decide⟩
  have hm0 := h.packMuls ⟨0, by decide⟩
  have hm1 := h.packMuls ⟨1, by decide⟩
  have hm2 := h.packMuls ⟨2, by decide⟩
  have ha0 := h.packAdds ⟨0, by decide⟩
  have ha1 := h.packAdds ⟨1, by decide⟩
  have ha2 := h.packAdds ⟨2, by decide⟩
  change wire 11 = base (Field.toZMod (input ⟨0, by decide⟩)) at hi0
  change wire 12 = base (Field.toZMod (input ⟨1, by decide⟩)) at hi1
  change wire 13 = base (Field.toZMod (input ⟨2, by decide⟩)) at hi2
  change wire 14 = base (Field.toZMod (input ⟨3, by decide⟩)) at hi3
  change accepts (encode .mul) (wire 15) (wire 12) (wire 17) at hm0
  change accepts (encode .mul) (wire 2) (wire 13) (wire 19) at hm1
  change accepts (encode .mul) (wire 16) (wire 14) (wire 21) at hm2
  change accepts (encode .add) (wire 11) (wire 17) (wire 18) at ha0
  change accepts (encode .add) (wire 18) (wire 19) (wire 20) at ha1
  change accepts (encode .add) (wire 20) (wire 21) (wire 22) at ha2
  rw [h.basis1, hi1] at hm0
  rw [h.basis2, hi2] at hm1
  rw [h.basis3, hi3] at hm2
  rw [hi0] at ha0
  exact S31.Gadgets.Air.PackRows.acceptsPack_sound input _ _ _ _ _ _
    ⟨hm0, hm1, hm2, ha0, ha1, ha2⟩

/-- The same accepted witness cannot satisfy two different public input
vectors. This is a value claim conditional on the native public pins. -/
theorem public_input_unique (certificate : Certificate)
    (totalAddRows : Nat) (wire : Nat → Quad) (left right : Fin 4 → M31)
    (hl : InputBoundary certificate totalAddRows wire left)
    (hr : InputBoundary certificate totalAddRows wire right) :
    left = right := by
  funext i
  have heq : base (Field.toZMod (left i)) =
      base (Field.toZMod (right i)) := (hl.pins i).symm.trans (hr.pins i)
  exact Field.toZMod_injective (congrArg Quad.a heq)

/-- The exact parsed source meaning and packed public input agree on the
same `input`; the bridge from local rows to authenticated native values is
intentionally an external proof obligation. -/
theorem checked_source_input_bound (sourceBytes normalizedBytes : List Nat)
    (certificate : Certificate) (totalAddRows : Nat)
    (observedCells : List S31.Functional.SSAAirColumnCells.ColumnCell)
    (wire : Nat → Quad) (input : Fin 4 → M31)
    (hrelation : checkRelation sourceBytes normalizedBytes = some certificate)
    (hcells : observedCells = expectedInputCells certificate totalAddRows)
    (hboundary : InputBoundary certificate totalAddRows wire input) :
    observedCells = expectedInputCells certificate totalAddRows ∧
      executeNormalized certificate input = denotation sourceBytes input ∧
      wire 22 = packM31 input := by
  exact ⟨hcells, checked_relation_sound sourceBytes normalizedBytes certificate input hrelation,
    packed_input_bound certificate totalAddRows wire input hboundary⟩

end S31.Functional.SSAPublicInputBinding
