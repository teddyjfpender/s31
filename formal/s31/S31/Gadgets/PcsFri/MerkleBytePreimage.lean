import S31.Gadgets.PcsFri.MerkleOpening
import Mathlib.Tactic

/-!
The selected plain BLAKE2s Merkle profile hashes canonical M31 words as
four little-endian bytes and hashes parents as left[32] ++ right[32]. This
module identifies the byte strings in the Merkle collision reduction. The
hash function remains an argument: no BLAKE2s security or Zig semantics is
assumed here.
-/

namespace S31.Gadgets.PcsFri.MerkleBytePreimage

open S31.Gadgets.PcsFri.MerkleOpening

def m31Modulus : Nat := 2147483647

def wordBytes (word : Nat) : List Nat :=
  [word % 256, word / 256 % 256, word / 65536 % 256,
    word / 16777216 % 256]

def byteString (message : List Nat) : Prop :=
  ∀ byte ∈ message, byte < 256

private theorem wordBytes_are_bytes (word : Nat) : byteString (wordBytes word) := by
  intro byte member
  simp [wordBytes] at member
  rcases member with h | h | h | h
  all_goals subst byte
  all_goals exact Nat.mod_lt _ (by omega)

def readWord : List Nat → Option Nat
  | [a, b, c, d] => some (a + 256 * b + 65536 * c + 16777216 * d)
  | _ => none

/-- Little-endian expansion recovers every canonical M31 representative. -/
theorem readWord_wordBytes (word : Nat) (canonical : word < m31Modulus) :
    readWord (wordBytes word) = some word := by
  simp only [readWord, wordBytes]
  dsimp [m31Modulus] at canonical
  have h0 := Nat.mod_add_div word 256
  have h1 := Nat.mod_add_div (word / 256) 256
  have h2 := Nat.mod_add_div (word / 65536) 256
  have d1 : (word / 256) / 256 = word / 65536 := by
    rw [Nat.div_div_eq_div_mul]
  have d2 : (word / 65536) / 256 = word / 16777216 := by
    rw [Nat.div_div_eq_div_mul]
  have h3 : word / 16777216 % 256 = word / 16777216 :=
    Nat.mod_eq_of_lt (by omega)
  rw [h3]
  congr 1
  calc
    word % 256 + 256 * (word / 256 % 256) +
        65536 * (word / 65536 % 256) +
        16777216 * (word / 16777216) =
      word % 256 + 256 *
        (word / 256 % 256 + 256 *
          (word / 65536 % 256 + 256 * (word / 16777216))) := by ring
    _ = word % 256 + 256 *
        (word / 256 % 256 + 256 * (word / 65536)) := by rw [← d2, h2]
    _ = word % 256 + 256 * (word / 256) := by rw [← d1, h1]
    _ = word := h0

theorem wordBytes_injective_on_canonical (a b : Nat)
    (ha : a < m31Modulus) (hb : b < m31Modulus)
    (equal : wordBytes a = wordBytes b) : a = b := by
  have left := readWord_wordBytes a ha
  have right := readWord_wordBytes b hb
  rw [equal] at left
  exact Option.some.inj (left.symm.trans right)

/-- The exact plain leaf message, without a leaf-domain prefix. -/
def leafMessage : List Nat → List Nat
  | [] => []
  | word :: rest => wordBytes word ++ leafMessage rest

theorem leafMessage_are_bytes (row : List Nat) : byteString (leafMessage row) := by
  induction row with
  | nil => simp [leafMessage, byteString]
  | cons word rest ih =>
      intro byte member
      simp only [leafMessage, List.mem_append] at member
      rcases member with head | tail
      · exact wordBytes_are_bytes word byte head
      · exact ih byte tail

theorem leafMessage_injective_on_canonical (xs ys : List Nat)
    (hx : ∀ x ∈ xs, x < m31Modulus)
    (hy : ∀ y ∈ ys, y < m31Modulus)
    (equal : leafMessage xs = leafMessage ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys => simp [leafMessage, wordBytes] at equal
  | cons x xs ih =>
      cases ys with
      | nil => simp [leafMessage, wordBytes] at equal
      | cons y ys =>
          simp only [leafMessage, wordBytes, List.cons_append,
            List.cons.injEq] at equal
          rcases equal with ⟨b0, b1, b2, b3, rest⟩
          have head : x = y := wordBytes_injective_on_canonical x y
            (hx x (by simp)) (hy y (by simp)) (by
              simp [wordBytes, b0, b1, b2, b3])
          have tail : xs = ys := ih ys
            (by intro z hz; exact hx z (by simp [hz]))
            (by intro z hz; exact hy z (by simp [hz])) rest
          simp [head, tail]

/-- Exact plain parent message; the caller supplies 32-byte digests. -/
def parentMessage (left right : List Nat) : List Nat := left ++ right

private theorem parentMessage_are_bytes (left right : List Nat)
    (hl : byteString left) (hr : byteString right) :
    byteString (parentMessage left right) := by
  intro byte member
  rcases List.mem_append.mp member with inLeft | inRight
  · exact hl byte inLeft
  · exact hr byte inRight

theorem parentMessage_injective_fixed32
    (l₁ r₁ l₂ r₂ : List Nat)
    (hl₁ : l₁.length = 32) (hl₂ : l₂.length = 32)
    (equal : parentMessage l₁ r₁ = parentMessage l₂ r₂) :
    l₁ = l₂ ∧ r₁ = r₂ := by
  have left := congrArg (List.take 32) equal
  have right := congrArg (List.drop 32) equal
  simp [parentMessage, hl₁, hl₂] at left right
  exact ⟨left, right⟩

/-- A leaf collision on distinct canonical rows is a collision on distinct
plain BLAKE2s message bytes, including the row-length distinction. -/
theorem distinct_rows_give_distinct_leaf_messages
    (xs ys : List Nat)
    (hx : ∀ x ∈ xs, x < m31Modulus)
    (hy : ∀ y ∈ ys, y < m31Modulus)
    (distinct : xs ≠ ys) : leafMessage xs ≠ leafMessage ys := by
  intro same
  exact distinct (leafMessage_injective_on_canonical xs ys hx hy same)

private theorem orderedChildren_width32 (position : Nat)
    (current sibling : List Nat)
    (hc : current.length = 32) (hs : sibling.length = 32) :
    (orderedChildren position current sibling).1.length = 32 ∧
    (orderedChildren position current sibling).2.length = 32 := by
  unfold orderedChildren
  split_ifs <;> simp [hc, hs]

private theorem pathInputs_width32
    (hash : List Nat → List Nat) (hash32 : ∀ message, (hash message).length = 32)
    (current : List Nat) (position : Nat) (siblings : List (List Nat))
    (current32 : current.length = 32)
    (siblings32 : ∀ sibling ∈ siblings, sibling.length = 32)
    (children : List Nat × List Nat)
    (member : children ∈ pathInputs
      (fun pair => hash (parentMessage pair.1 pair.2)) current position siblings) :
    children.1.length = 32 ∧ children.2.length = 32 := by
  induction siblings generalizing current position with
  | nil => simp [pathInputs] at member
  | cons sibling rest ih =>
      have sibling32 := siblings32 sibling (by simp)
      have rest32 : ∀ s ∈ rest, s.length = 32 := by
        intro s hs
        exact siblings32 s (by simp [hs])
      simp only [pathInputs, List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        exact orderedChildren_width32 position current sibling current32 sibling32
      · exact ih (hash (parentMessage
          (orderedChildren position current sibling).1
          (orderedChildren position current sibling).2))
          (position / 2) (hash32 _) rest32 tail

private theorem pathInputs_are_bytes
    (hash : List Nat → List Nat) (hashBytes : ∀ message, byteString (hash message))
    (current : List Nat) (position : Nat) (siblings : List (List Nat))
    (currentBytes : byteString current)
    (siblingsBytes : ∀ sibling ∈ siblings, byteString sibling)
    (children : List Nat × List Nat)
    (member : children ∈ pathInputs
      (fun pair => hash (parentMessage pair.1 pair.2)) current position siblings) :
    byteString children.1 ∧ byteString children.2 := by
  induction siblings generalizing current position with
  | nil => simp [pathInputs] at member
  | cons sibling rest ih =>
      have siblingBytes := siblingsBytes sibling (by simp)
      have restBytes : ∀ s ∈ rest, byteString s := by
        intro s hs
        exact siblingsBytes s (by simp [hs])
      simp only [pathInputs, List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        unfold orderedChildren
        split_ifs <;> simp [currentBytes, siblingBytes]
      · exact ih (hash (parentMessage
          (orderedChildren position current sibling).1
          (orderedChildren position current sibling).2))
          (position / 2) (hashBytes _) restBytes tail

/-- The symbolic same-root collision reduction becomes a collision on two
*different actual byte messages* for the selected plain BLAKE2s layout.
This is a reduction, not a numerical collision probability. The fixed 32-byte
digest and sibling premises state the exact hash type used by the native
Merkle tree. -/
theorem conflicting_openings_give_plain_byte_collision
    (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (root : List Nat) (height position : Nat)
    (row₁ row₂ : List Nat) (siblings₁ siblings₂ : List (List Nat))
    (canonical₁ : ∀ word ∈ row₁, word < m31Modulus)
    (canonical₂ : ∀ word ∈ row₂, word < m31Modulus)
    (siblings32₁ : ∀ sibling ∈ siblings₁, sibling.length = 32)
    (siblings32₂ : ∀ sibling ∈ siblings₂, sibling.length = 32)
    (siblingsBytes₁ : ∀ sibling ∈ siblings₁, byteString sibling)
    (siblingsBytes₂ : ∀ sibling ∈ siblings₂, byteString sibling)
    (accepted₁ : acceptedOpening (fun row => hash (leafMessage row))
      (fun pair => hash (parentMessage pair.1 pair.2))
      root height position row₁ siblings₁)
    (accepted₂ : acceptedOpening (fun row => hash (leafMessage row))
      (fun pair => hash (parentMessage pair.1 pair.2))
      root height position row₂ siblings₂)
    (differentRows : row₁ ≠ row₂) :
    ∃ message₁ message₂ : List Nat,
      byteString message₁ ∧ byteString message₂ ∧
      message₁ ≠ message₂ ∧ hash message₁ = hash message₂ := by
  obtain leaf | parent := conflicting_openings_produce_collision
    (fun row => hash (leafMessage row))
    (fun pair => hash (parentMessage pair.1 pair.2))
    root height position row₁ row₂ siblings₁ siblings₂
    accepted₁ accepted₂ differentRows
  · exact ⟨leafMessage row₁, leafMessage row₂,
      leafMessage_are_bytes row₁, leafMessage_are_bytes row₂,
      distinct_rows_give_distinct_leaf_messages row₁ row₂
        canonical₁ canonical₂ leaf.1, leaf.2⟩
  · rcases parent with ⟨children₁, children₂, in₁, in₂, different, same⟩
    have firstWidth := pathInputs_width32 hash hash32
      (hash (leafMessage row₁)) position siblings₁ (hash32 _)
      siblings32₁ children₁ in₁
    have secondWidth := pathInputs_width32 hash hash32
      (hash (leafMessage row₂)) position siblings₂ (hash32 _)
      siblings32₂ children₂ in₂
    have firstBytes := pathInputs_are_bytes hash hashBytes
      (hash (leafMessage row₁)) position siblings₁ (hashBytes _)
      siblingsBytes₁ children₁ in₁
    have secondBytes := pathInputs_are_bytes hash hashBytes
      (hash (leafMessage row₂)) position siblings₂ (hashBytes _)
      siblingsBytes₂ children₂ in₂
    refine ⟨parentMessage children₁.1 children₁.2,
      parentMessage children₂.1 children₂.2,
      parentMessage_are_bytes _ _ firstBytes.1 firstBytes.2,
      parentMessage_are_bytes _ _ secondBytes.1 secondBytes.2,
      ?_, same⟩
    intro sameMessage
    obtain ⟨leftEq, rightEq⟩ := parentMessage_injective_fixed32
      children₁.1 children₁.2 children₂.1 children₂.2
      firstWidth.1 secondWidth.1 sameMessage
    exact different (Prod.ext leftEq rightEq)

end S31.Gadgets.PcsFri.MerkleBytePreimage
