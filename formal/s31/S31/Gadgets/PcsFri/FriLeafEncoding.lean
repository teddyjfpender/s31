import S31.Gadgets.Packed

/-!
The native S31 FRI leaf hasher receives four canonical M31 coordinates for
each QM31 value, with values ordered first and coordinates second. This file
proves that the corresponding Lean coordinate flattening loses no value or
position information. It does not prove that Zig's `QM31.toM31Array` and
`H.updateLeaf` execute this model; the source guard and native admission test
bind those steps only operationally.
-/

namespace S31.Gadgets.PcsFri.FriLeafEncoding

open S31.Gadgets.Packed

/-- Coordinates of one QM31 value in the native `(a,b,c,d)` order. -/
def coordinates (value : Quad) : List F :=
  [value.a, value.b, value.c, value.d]

/-- One packed FRI Merkle leaf row, with each value's four coordinates
consecutive before moving to the next value. -/
def encodeRow : List Quad → List F
  | [] => []
  | value :: rest => coordinates value ++ encodeRow rest

theorem coordinates_injective : Function.Injective coordinates := by
  intro x y h
  simp only [coordinates, List.cons.injEq] at h
  rcases h with ⟨ha, hb, hc, hd, _⟩
  exact Quad.ext ha hb hc hd

/-- Different extension-field rows have different M31 coordinate lists,
including rows of different lengths. -/
theorem encodeRow_injective : Function.Injective encodeRow := by
  intro xs ys h
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons head tail => simp [encodeRow, coordinates] at h
  | cons x rest ih =>
      cases ys with
      | nil => simp [encodeRow, coordinates] at h
      | cons y tail =>
          simp only [encodeRow, coordinates, List.cons_append,
            List.cons.injEq] at h
          rcases h with ⟨ha, hb, hc, hd, htail⟩
          have headEq : x = y := Quad.ext ha hb hc hd
          have tailEq : rest = tail := ih htail
          simp [headEq, tailEq]

/-- The leaf-hash collision in `FriMerkleBinding` can be stated as a collision
on distinct native coordinate preimages, conditional on the concrete hash
being applied to `encodeRow`. No hash injectivity is assumed. -/
theorem unequal_rows_equal_hash_give_encoded_collision {H : Type*}
    (hashM31Row : List F → H) (xs ys : List Quad)
    (different : xs ≠ ys)
    (sameHash : hashM31Row (encodeRow xs) = hashM31Row (encodeRow ys)) :
    encodeRow xs ≠ encodeRow ys ∧
      hashM31Row (encodeRow xs) = hashM31Row (encodeRow ys) := by
  exact ⟨fun h => different (encodeRow_injective h), sameHash⟩

end S31.Gadgets.PcsFri.FriLeafEncoding
