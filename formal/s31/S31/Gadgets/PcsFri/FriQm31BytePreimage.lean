import S31.Gadgets.PcsFri.MerkleBytePreimage
import Mathlib.Tactic

/-!
The native FRI capture stores QM31 evaluations, while the selected plain
Merkle leaf hashes four M31 coordinates per evaluation. This file connects
those two row types to the canonical-byte collision reduction. `Qm31Coords`
is the mathematical coordinate tuple; the pinned Zig `toM31Array` order and
`row[offset * 4 + coordinate]` assignment are source-bound separately.

The theorem assumes two accepted full paths at the same root, height and
position, canonical M31 coordinates, and distinct QM31 rows. It does not
derive the paths from Zig execution or bound BLAKE2s collisions.
-/

namespace S31.Gadgets.PcsFri.FriQm31BytePreimage

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.MerkleBytePreimage

structure Qm31Coords where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  deriving DecidableEq

def coordinates (q : Qm31Coords) : List Nat := [q.a, q.b, q.c, q.d]

def flatten (row : List Qm31Coords) : List Nat := row.flatMap coordinates

def canonical (q : Qm31Coords) : Prop :=
  q.a < m31Modulus ∧ q.b < m31Modulus ∧
    q.c < m31Modulus ∧ q.d < m31Modulus

theorem coordinates_injective {x y : Qm31Coords}
    (equal : coordinates x = coordinates y) : x = y := by
  cases x with
  | mk a b c d =>
    cases y with
    | mk a' b' c' d' =>
      simp only [coordinates, List.cons.injEq] at equal
      rcases equal with ⟨rfl, rfl, rfl, rfl, _⟩
      rfl

/-- Each fixed-width group can be recovered by taking four words; the
remaining row is recovered by dropping them. This includes different row
lengths and does not assume that the hash is injective. -/
theorem flatten_injective {xs ys : List Qm31Coords}
    (equal : flatten xs = flatten ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [flatten, coordinates] at equal
  | cons x xs ih =>
      cases ys with
      | nil => simp [flatten, coordinates] at equal
      | cons y ys =>
          have head := congrArg (List.take 4) equal
          have tail := congrArg (List.drop 4) equal
          have sameHead : coordinates x = coordinates y := by
            simpa [flatten, coordinates] using head
          have sameTail : flatten xs = flatten ys := by
            simpa [flatten, coordinates] using tail
          have xy : x = y := coordinates_injective sameHead
          subst y
          exact congrArg (List.cons x) (ih sameTail)

theorem flatten_canonical (row : List Qm31Coords)
    (hrow : ∀ q ∈ row, canonical q) :
    ∀ word ∈ flatten row, word < m31Modulus := by
  intro word member
  simp only [flatten, List.mem_flatMap] at member
  obtain ⟨q, inRow, inCoords⟩ := member
  obtain ⟨ha, hb, hc, hd⟩ := hrow q inRow
  simp [coordinates] at inCoords
  rcases inCoords with rfl | rfl | rfl | rfl <;> assumption

/-- Distinct QM31 rows have distinct plain Merkle byte messages, even when
one row contains one evaluation and the other contains four. -/
theorem distinct_qm31_rows_give_distinct_leaf_messages
    (row₁ row₂ : List Qm31Coords)
    (canonical₁ : ∀ q ∈ row₁, canonical q)
    (canonical₂ : ∀ q ∈ row₂, canonical q)
    (different : row₁ ≠ row₂) :
    leafMessage (flatten row₁) ≠ leafMessage (flatten row₂) := by
  apply distinct_rows_give_distinct_leaf_messages
    (flatten row₁) (flatten row₂)
    (flatten_canonical row₁ canonical₁) (flatten_canonical row₂ canonical₂)
  intro same
  exact different (flatten_injective same)

/-- The existing same-root, same-index, same-height collision reduction now
applies to the actual QM31 FRI row type after its four-coordinate packing.
Native path extraction and quantitative BLAKE2s security remain premises. -/
theorem conflicting_qm31_openings_give_plain_byte_collision
    (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (root : List Nat) (height position : Nat)
    (row₁ row₂ : List Qm31Coords)
    (siblings₁ siblings₂ : List (List Nat))
    (canonical₁ : ∀ q ∈ row₁, canonical q)
    (canonical₂ : ∀ q ∈ row₂, canonical q)
    (siblings32₁ : ∀ sibling ∈ siblings₁, sibling.length = 32)
    (siblings32₂ : ∀ sibling ∈ siblings₂, sibling.length = 32)
    (siblingsBytes₁ : ∀ sibling ∈ siblings₁, byteString sibling)
    (siblingsBytes₂ : ∀ sibling ∈ siblings₂, byteString sibling)
    (accepted₁ : acceptedOpening
      (fun row => hash (leafMessage (flatten row)))
      (fun pair => hash (parentMessage pair.1 pair.2))
      root height position row₁ siblings₁)
    (accepted₂ : acceptedOpening
      (fun row => hash (leafMessage (flatten row)))
      (fun pair => hash (parentMessage pair.1 pair.2))
      root height position row₂ siblings₂)
    (different : row₁ ≠ row₂) :
    ∃ message₁ message₂ : List Nat,
      byteString message₁ ∧ byteString message₂ ∧
      message₁ ≠ message₂ ∧ hash message₁ = hash message₂ := by
  exact conflicting_openings_give_plain_byte_collision hash hash32 hashBytes
    root height position (flatten row₁) (flatten row₂) siblings₁ siblings₂
    (flatten_canonical row₁ canonical₁) (flatten_canonical row₂ canonical₂)
    siblings32₁ siblings32₂ siblingsBytes₁ siblingsBytes₂
    accepted₁ accepted₂ (by intro same; exact different (flatten_injective same))

end S31.Gadgets.PcsFri.FriQm31BytePreimage
