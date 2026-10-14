import S31.Gadgets.PcsFri.MultiproofCommittedColumns
import S31.Gadgets.PcsFri.MerkleBytePreimage
import Mathlib.Tactic

/-!
The complete mathematical multiproof decoder either returns the row in the
constructed lifted commitment or exposes two distinct byte strings with the
same hash. This composes the raw query/capture theorem with the exact plain
leaf and parent byte encodings. It does not assert global hash injectivity,
native Zig refinement, or a quantitative BLAKE2s collision bound.
-/

namespace S31.Gadgets.PcsFri.MultiproofByteCollisionReduction

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.MerkleBytePreimage
open S31.Gadgets.PcsFri.MultiproofRawQueries
open S31.Gadgets.PcsFri.MultiproofCommittedColumns

def byteLeaf (hash : List Nat → List Nat) (row : List Nat) : List Nat :=
  hash (leafMessage row)

def byteParent (hash : List Nat → List Nat)
    (children : List Nat × List Nat) : List Nat :=
  hash (parentMessage children.1 children.2)

private theorem constructed_layer_is_digest (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (height : Nat) (columns : List (Column Nat)) (level position : Nat) :
    (layerHash (byteLeaf hash) (byteParent hash) height columns
      level position).length = 32 ∧
    byteString (layerHash (byteLeaf hash) (byteParent hash) height
      columns level position) := by
  cases level with
  | zero => exact ⟨hash32 _, hashBytes _⟩
  | succ _ => exact ⟨hash32 _, hashBytes _⟩

/-- Every sibling in the *constructed* complete tree has the selected native
digest shape. Only the proof-supplied path needs a separate decoder bridge. -/
theorem committed_path_digest_shape (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (height position : Nat) (columns : List (Column Nat)) :
    (∀ sibling ∈ committedPath (byteLeaf hash) (byteParent hash)
      height position columns, sibling.length = 32) ∧
    (∀ sibling ∈ committedPath (byteLeaf hash) (byteParent hash)
      height position columns, byteString sibling) := by
  suffices all : ∀ level remaining current,
      (∀ sibling ∈ layerPath (byteLeaf hash) (byteParent hash)
        height columns level remaining current, sibling.length = 32) ∧
      (∀ sibling ∈ layerPath (byteLeaf hash) (byteParent hash)
        height columns level remaining current, byteString sibling) by
    simpa [committedPath] using all 0 height position
  intro level remaining
  induction remaining generalizing level with
  | zero => simp [layerPath]
  | succ remaining ih =>
      intro current
      have head := constructed_layer_is_digest hash hash32 hashBytes
        height columns level (siblingIndex current)
      have tail := ih (level + 1) (current / 2)
      constructor
      · intro sibling member
        rcases List.mem_cons.mp (by simpa [layerPath] using member) with
          rfl | inTail
        · exact head.1
        · exact tail.1 sibling inTail
      · intro sibling member
        rcases List.mem_cons.mp (by simpa [layerPath] using member) with
          rfl | inTail
        · exact head.2
        · exact tail.2 sibling inTail

/-- A conflicting raw query in a successful complete-tree decode gives an
actual collision on distinct *byte messages*. The captured and constructed
paths must be 32-byte digests; these are the native hash type's shape facts,
not a collision-resistance premise. -/
theorem conflicting_query_yields_byte_collision
    (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (height : Nat) (columns : List (Column Nat))
    (queries : List (RawQuery Nat)) (witnesses : List (List Nat))
    (captures : List (Option (List (List Nat))))
    (accepted : verifyRaw (byteLeaf hash) (byteParent hash) height
      (committedRoot (byteLeaf hash) (byteParent hash) height columns)
      queries witnesses = some captures)
    (i : Nat) (inRange : i < queries.length)
    (nativePath : List (List Nat))
    (captured : captures[i]'(by
      obtain ⟨_, layers, _, _, rfl⟩ :=
        verifyRaw_decomposes (byteLeaf hash) (byteParent hash) height
          (committedRoot (byteLeaf hash) (byteParent hash) height columns)
          queries witnesses captures accepted
      simpa [S31.Gadgets.PcsFri.MultiproofCallerOrder.captureInCallerOrder]
        using inRange) = some nativePath)
    (nativePath32 : ∀ sibling ∈ nativePath, sibling.length = 32)
    (nativePathBytes : ∀ sibling ∈ nativePath, byteString sibling)
    (canonicalQuery : ∀ word ∈ queries[i].row, word < m31Modulus)
    (canonicalCommitment : ∀ word ∈
      projectedRow height queries[i].position columns, word < m31Modulus)
    (different : queries[i].row ≠
      projectedRow height queries[i].position columns) :
    ∃ message₁ message₂ : List Nat,
      byteString message₁ ∧ byteString message₂ ∧
      message₁ ≠ message₂ ∧ hash message₁ = hash message₂ := by
  obtain ⟨path, observed, opened⟩ :=
    verifyRaw_each_opening (byteLeaf hash) (byteParent hash) height
      (committedRoot (byteLeaf hash) (byteParent hash) height columns)
      queries witnesses captures accepted i inRange
  have samePath : path = nativePath :=
    Option.some.inj (observed.symm.trans captured)
  subst path
  have domain : queries[i].position < 2 ^ height := opened.1
  have committed :=
    committedOpening (byteLeaf hash) (byteParent hash) height
      queries[i].position columns domain
  have ⟨committedPath32, committedPathBytes⟩ :=
    committed_path_digest_shape hash hash32 hashBytes height
      queries[i].position columns
  exact conflicting_openings_give_plain_byte_collision hash hash32 hashBytes
    (committedRoot (byteLeaf hash) (byteParent hash) height columns)
    height queries[i].position queries[i].row
    (projectedRow height queries[i].position columns) nativePath
    (committedPath (byteLeaf hash) (byteParent hash) height
      queries[i].position columns)
    canonicalQuery canonicalCommitment nativePath32 committedPath32
    nativePathBytes committedPathBytes opened committed different

/-- One caller slot in a successful modeled decode has the constructed
committed row, or the decode exposes a concrete distinct-message collision.
The claim is uniform in height, column count, query count, and duplicate raw
positions. It is conditional only on canonical rows and proof-path byte shape. -/
theorem query_row_or_byte_collision
    (hash : List Nat → List Nat)
    (hash32 : ∀ message, (hash message).length = 32)
    (hashBytes : ∀ message, byteString (hash message))
    (height : Nat) (columns : List (Column Nat))
    (queries : List (RawQuery Nat)) (witnesses : List (List Nat))
    (captures : List (Option (List (List Nat))))
    (accepted : verifyRaw (byteLeaf hash) (byteParent hash) height
      (committedRoot (byteLeaf hash) (byteParent hash) height columns)
      queries witnesses = some captures)
    (i : Nat) (inRange : i < queries.length)
    (nativePath : List (List Nat))
    (captured : captures[i]'(by
      obtain ⟨_, layers, _, _, rfl⟩ :=
        verifyRaw_decomposes (byteLeaf hash) (byteParent hash) height
          (committedRoot (byteLeaf hash) (byteParent hash) height columns)
          queries witnesses captures accepted
      simpa [S31.Gadgets.PcsFri.MultiproofCallerOrder.captureInCallerOrder]
        using inRange) = some nativePath)
    (nativePath32 : ∀ sibling ∈ nativePath, sibling.length = 32)
    (nativePathBytes : ∀ sibling ∈ nativePath, byteString sibling)
    (canonicalQuery : ∀ word ∈ queries[i].row, word < m31Modulus)
    (canonicalCommitment : ∀ word ∈
      projectedRow height queries[i].position columns, word < m31Modulus) :
    queries[i].row = projectedRow height queries[i].position columns ∨
      ∃ message₁ message₂ : List Nat,
        byteString message₁ ∧ byteString message₂ ∧
        message₁ ≠ message₂ ∧ hash message₁ = hash message₂ := by
  by_cases same : queries[i].row =
      projectedRow height queries[i].position columns
  · exact Or.inl same
  · exact Or.inr (conflicting_query_yields_byte_collision hash hash32
      hashBytes height columns queries witnesses captures accepted i inRange
      nativePath captured nativePath32 nativePathBytes canonicalQuery
      canonicalCommitment same)

/- A deliberately constant digest shows why the conclusion must expose a
collision rather than assert every accepted row is the committed row. -/
private def toyHash (_ : List Nat) : List Nat := List.replicate 32 0
private def toyColumns : List (Column Nat) :=
  [⟨0, fun _ => 1⟩]

example : projectedRow 0 0 toyColumns = [1] := by decide
example : verifyRaw (byteLeaf toyHash) (byteParent toyHash) 0
    (committedRoot (byteLeaf toyHash) (byteParent toyHash) 0 toyColumns)
    [⟨0, [2]⟩] [] = some [some []] := by decide

end S31.Gadgets.PcsFri.MultiproofByteCollisionReduction
