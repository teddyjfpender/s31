import S31.Gadgets.Functional.TextSquare4Native

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

/-- Interpret native gate variables as arbitrary packed field values. The
first wire is the constrained packed public input, and each native operation
gate is checked with the nine-polynomial row model. -/
def nativeRows (wire : Nat → Quad) (input : Fin 4 → M31) : Prop :=
  wire TextSquare4Native.first.input0 = packM31 input ∧
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
    simpa [TextSquare4Native.first] using hinput
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
