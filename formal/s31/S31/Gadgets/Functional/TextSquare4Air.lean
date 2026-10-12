import S31.Gadgets.Functional.TextSquare4Proof
import S31.Gadgets.Air.Qm31Ops

/-!
Both packed multiplication rows of the real `functional_square4.s31` sample.
The two row outputs are arbitrary proof witnesses. This is a local AIR
constraint theorem; Gate lookup, trace scheduling and STARK verification have
their own separate obligations.
-/

namespace S31.Functional.TextSquare4Air

open S31
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Packed

def square (x : Fin 4 → M31) : Fin 4 → M31 := fun i => x i * x i
def fourth (x : Fin 4 → M31) : Fin 4 → M31 := fun i => square x i * square x i

theorem pointwise_pack (a b : Fin 4 → M31) :
    evaluate (s31Op true) (packM31 a) (packM31 b) =
      packM31 (fun i => a i * b i) := by
  apply Quad.ext
  · simpa [coord, coord_packM31] using (s31Op_coord true a b ⟨0, by decide⟩)
  · simpa [coord, coord_packM31] using (s31Op_coord true a b ⟨1, by decide⟩)
  · simpa [coord, coord_packM31] using (s31Op_coord true a b ⟨2, by decide⟩)
  · simpa [coord, coord_packM31] using (s31Op_coord true a b ⟨3, by decide⟩)

/-- The first and second packed outputs are arbitrary Quad witnesses. -/
def twoRows (input : Fin 4 → M31) (result : Quad) : Prop :=
  ∃ first : Quad,
    accepts (encode (s31Op true)) (packM31 input) (packM31 input) first ∧
    accepts (encode (s31Op true)) first first result

/-- There is no satisfying pair of local rows with a forged final value. -/
theorem two_rows_iff (input : Fin 4 → M31) (result : Quad) :
    twoRows input result ↔ result = packM31 (fourth input) := by
  constructor
  · rintro ⟨first, hfirst, hsecond⟩
    have hfirst' := (accepts_encoded (s31Op true) _ _ _).mp hfirst
    rw [pointwise_pack] at hfirst'
    have hsecond' := (accepts_encoded (s31Op true) _ _ _).mp hsecond
    rw [hfirst'] at hsecond'
    rw [pointwise_pack] at hsecond'
    exact hsecond'
  · intro h
    refine ⟨packM31 (square input), ?_, ?_⟩
    · apply (accepts_encoded (s31Op true) _ _ _).mpr
      rw [pointwise_pack]
      rfl
    · apply (accepts_encoded (s31Op true) _ _ _).mpr
      rw [pointwise_pack, h]
      rfl

theorem packM31_injective {a b : Fin 4 → M31}
    (h : packM31 a = packM31 b) : a = b := by
  funext i
  apply S31.Field.toZMod_injective
  simpa only [coord_packM31] using congrArg (fun q => coord q i) h

theorem two_rows_iff_values (input claimed : Fin 4 → M31) :
    twoRows input (packM31 claimed) ↔ claimed = fourth input := by
  rw [two_rows_iff]
  exact ⟨packM31_injective, fun h => congrArg packM31 h⟩

/-- Exact normalized output and both packed AIR rows agree for arbitrary
four-lane inputs and arbitrary claimed values. -/
theorem compiled_nodes_iff_two_rows (a b c d : M31)
    (claimed : Fin 4 → M31) :
    (TextSquare4.compiled.nodes.foldlM (fun env node => do
      return env ++ [(node.name, ← evaluateNode env node)])
        (TextSquare4Proof.inputEnv a b c d)) =
      .ok (TextSquare4Proof.inputEnv a b c d ++ [
        ("_s31_i1_0", ⟨.m31, [a * a, b * b, c * c, d * d]⟩),
        ("result", ⟨.m31, List.ofFn claimed⟩)]) ↔
      twoRows ![a, b, c, d] (packM31 claimed) := by
  rw [two_rows_iff_values]
  rw [TextSquare4Proof.text_compiler_nodes_correct]
  simp only [Except.ok.injEq]
  constructor
  · intro h
    apply List.ofFn_injective
    simpa [fourth, square, List.ofFn] using h.symm
  · intro h
    subst claimed
    rfl

end S31.Functional.TextSquare4Air
