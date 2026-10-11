import S31.Gadgets.Functional.TextSquare4Native
import S31.Gadgets.Air.PackRows

/-!
The gate IDs and node row spans come from the native Zig direct compiler run on
IR freshly emitted from the real `.s31` source. This theorem interprets those
gate IDs in the proved local AIR relation. A separate source check regenerates
the data byte for byte before the Lean audit.
-/

namespace S31.Functional.TextSquare4NativeProof

open S31
open S31.Functional.TextSquare4Air
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Packed

theorem gate_chain :
    TextSquare4Native.first.input0 = TextSquare4Native.first.input1 ∧
    TextSquare4Native.second.input0 = TextSquare4Native.second.input1 ∧
    TextSquare4Native.second.input0 = TextSquare4Native.first.output := by
  decide

theorem two_adjacent_arithmetic_rows :
    TextSquare4Native.nodeRowSpans = [(6, 7), (7, 8)] := by
  rfl

def inputWire (i : Nat) : Nat := TextSquare4Native.inputWires[i]!
def basisWire (i : Nat) : Nat := TextSquare4Native.inputBasisWires[i]!
def packMul (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.inputPackMul[i]!
def packAdd (i : Nat) : TextSquare4Native.Gate :=
  TextSquare4Native.inputPackAdd[i]!

/-- The native compiler's six input packing gates and its four constrained
scalar input wires. Basis wires carry the three pinned extension units. -/
def nativePackRows (wire : Nat → Quad) (input : Fin 4 → M31) : Prop :=
  wire (inputWire 0) = base (S31.Field.toZMod (input ⟨0, by decide⟩)) ∧
  wire (inputWire 1) = base (S31.Field.toZMod (input ⟨1, by decide⟩)) ∧
  wire (inputWire 2) = base (S31.Field.toZMod (input ⟨2, by decide⟩)) ∧
  wire (inputWire 3) = base (S31.Field.toZMod (input ⟨3, by decide⟩)) ∧
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
    (wire ((packAdd i.val).output)))

theorem native_pack_sound (wire : Nat → Quad) (input : Fin 4 → M31)
    (h : nativePackRows wire input) :
    wire TextSquare4Native.first.input0 = packM31 input := by
  rcases h with ⟨hi0, hi1, hi2, hi3, hb1, hb2, hb3, hm, ha⟩
  have hm1 := hm ⟨0, by decide⟩
  have hm2 := hm ⟨1, by decide⟩
  have hm3 := hm ⟨2, by decide⟩
  have ha1 := ha ⟨0, by decide⟩
  have ha2 := ha ⟨1, by decide⟩
  have ha3 := ha ⟨2, by decide⟩
  change wire 11 = base (S31.Field.toZMod (input ⟨0, by decide⟩)) at hi0
  change wire 12 = base (S31.Field.toZMod (input ⟨1, by decide⟩)) at hi1
  change wire 13 = base (S31.Field.toZMod (input ⟨2, by decide⟩)) at hi2
  change wire 14 = base (S31.Field.toZMod (input ⟨3, by decide⟩)) at hi3
  change wire 15 = unit ⟨1, by decide⟩ at hb1
  change wire 2 = unit ⟨2, by decide⟩ at hb2
  change wire 16 = unit ⟨3, by decide⟩ at hb3
  change accepts (encode .mul) (wire 15) (wire 12) (wire 17) at hm1
  change accepts (encode .mul) (wire 2) (wire 13) (wire 19) at hm2
  change accepts (encode .mul) (wire 16) (wire 14) (wire 21) at hm3
  change accepts (encode .add) (wire 11) (wire 17) (wire 18) at ha1
  change accepts (encode .add) (wire 18) (wire 19) (wire 20) at ha2
  change accepts (encode .add) (wire 20) (wire 21) (wire 22) at ha3
  rw [hb1, hi1] at hm1
  rw [hb2, hi2] at hm2
  rw [hb3, hi3] at hm3
  rw [hi0] at ha1
  have hpack : S31.Gadgets.Air.PackRows.acceptsPack input
      (wire 17) (wire 19) (wire 21) (wire 18) (wire 20) (wire 22) :=
    ⟨hm1, hm2, hm3, ha1, ha2, ha3⟩
  exact S31.Gadgets.Air.PackRows.acceptsPack_sound input _ _ _ _ _ _ hpack

/-- Interpret native gate variables as arbitrary packed field values. The
input packing and both arithmetic nodes are checked with local AIR rows. -/
def nativeRows (wire : Nat → Quad) (input : Fin 4 → M31) : Prop :=
  nativePackRows wire input ∧
  accepts (encode (s31Op true))
    (wire TextSquare4Native.first.input0)
    (wire TextSquare4Native.first.input1)
    (wire TextSquare4Native.first.output) ∧
  accepts (encode (s31Op true))
    (wire TextSquare4Native.second.input0)
    (wire TextSquare4Native.second.input1)
    (wire TextSquare4Native.second.output)

theorem native_rows_sound (wire : Nat → Quad) (input : Fin 4 → M31)
    (h : nativeRows wire input) :
    wire TextSquare4Native.second.output = packM31 (fourth input) := by
  rcases h with ⟨hinput, hfirst, hsecond⟩
  have hinput' : wire 22 = packM31 input := by
    simpa [TextSquare4Native.first] using native_pack_sound wire input hinput
  have hfirst' : accepts (encode (s31Op true))
      (packM31 input) (packM31 input)
      (wire TextSquare4Native.first.output) := by
    have hraw : accepts (encode (s31Op true))
        (wire 22) (wire 22) (wire 23) := by
      simpa [TextSquare4Native.first] using hfirst
    rw [hinput'] at hraw
    simpa [TextSquare4Native.first] using hraw
  have hsecond' : accepts (encode (s31Op true))
      (wire TextSquare4Native.first.output)
      (wire TextSquare4Native.first.output)
      (wire TextSquare4Native.second.output) := by
    simpa [TextSquare4Native.first, TextSquare4Native.second] using hsecond
  exact (two_rows_iff input _).mp ⟨wire TextSquare4Native.first.output,
    hfirst', hsecond'⟩

end S31.Functional.TextSquare4NativeProof
