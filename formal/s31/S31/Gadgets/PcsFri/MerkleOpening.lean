import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
An abstract model of the **full authentication path reconstructed after** the
native lifted Merkle verifier succeeds. Native `vcs_lifted/verifier.zig` hashes
the leaf row, then combines each sibling bottom-up, choosing left/right from
the current index's low bit and shifting the index right after each level.

No cryptographic hash is assumed globally injective. The first theorem is a
collision reduction: two different leaves accepted at the same root, position
and path depth produce either a leaf-hash or a parent-hash collision. The
corollary uses an explicit absence-of-collision premise to refine an accepted
native opening to a committed projected row.

This model does not yet prove that the Zig multiproof decoder reconstructs the
modeled sibling path, that BLAKE2s is collision resistant, or that a prover's
committed tree was built from the modeled projected columns.
-/

namespace S31.Gadgets.PcsFri.MerkleOpening

variable {H V : Type*}

/-- Native Merkle child order: the low index bit selects the current node's side. -/
def orderedChildren (position : Nat) (current sibling : H) : H × H :=
  if position % 2 = 0 then (current, sibling) else (sibling, current)

/-- Bottom-up root reconstruction from a full path; one right shift per level. -/
def pathRoot (parentHash : H × H → H) (current : H) (position : Nat) : List H → H
  | [] => current
  | sibling :: rest =>
      pathRoot parentHash
        (parentHash (orderedChildren position current sibling))
        (position / 2) rest

/-- The ordered child pairs actually compressed along one authentication path. -/
def pathInputs (parentHash : H × H → H) (current : H) (position : Nat) :
    List H → List (H × H)
  | [] => []
  | sibling :: rest =>
      let children := orderedChildren position current sibling
      children :: pathInputs parentHash (parentHash children) (position / 2) rest

/-- If the two oriented child pairs agree at one level, their current nodes
agree, regardless of the parity of the common queried position. -/
theorem orderedChildren_current_injective (position : Nat)
    {current₁ current₂ sibling₁ sibling₂ : H}
    (h : orderedChildren position current₁ sibling₁ =
      orderedChildren position current₂ sibling₂) : current₁ = current₂ := by
  unfold orderedChildren at h
  split_ifs at h with parity
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Equal reconstructed roots at the same index and depth imply equal leaf
hashes or a concrete parent compression collision. The collision witnesses
are produced by the two compared paths, not postulated globally. -/
theorem equal_roots_force_leaf_hash_or_parent_collision
    (parentHash : H × H → H) (position : Nat)
    (leaf₁ leaf₂ : H) (siblings₁ siblings₂ : List H)
    (sameDepth : siblings₁.length = siblings₂.length)
    (sameRoot : pathRoot parentHash leaf₁ position siblings₁ =
      pathRoot parentHash leaf₂ position siblings₂) :
    leaf₁ = leaf₂ ∨
      ∃ children₁ children₂ : H × H,
        children₁ ∈ pathInputs parentHash leaf₁ position siblings₁ ∧
        children₂ ∈ pathInputs parentHash leaf₂ position siblings₂ ∧
        children₁ ≠ children₂ ∧ parentHash children₁ = parentHash children₂ := by
  induction siblings₁ generalizing siblings₂ leaf₁ leaf₂ position with
  | nil =>
      cases siblings₂ with
      | nil => exact Or.inl sameRoot
      | cons sibling rest => simp at sameDepth
  | cons sibling₁ rest₁ ih =>
      cases siblings₂ with
      | nil => simp at sameDepth
      | cons sibling₂ rest₂ =>
          have tailDepth : rest₁.length = rest₂.length := by
            simpa using sameDepth
          have tailRoot :
              pathRoot parentHash
                  (parentHash (orderedChildren position leaf₁ sibling₁))
                  (position / 2) rest₁ =
                pathRoot parentHash
                  (parentHash (orderedChildren position leaf₂ sibling₂))
                  (position / 2) rest₂ := by
            simpa [pathRoot] using sameRoot
          rcases ih (position / 2)
              (parentHash (orderedChildren position leaf₁ sibling₁))
              (parentHash (orderedChildren position leaf₂ sibling₂))
              rest₂ tailDepth tailRoot with nextEqual | collision
          · by_cases sameChildren :
                orderedChildren position leaf₁ sibling₁ =
                  orderedChildren position leaf₂ sibling₂
            · exact Or.inl (orderedChildren_current_injective position sameChildren)
            · exact Or.inr ⟨_, _, by simp [pathInputs], by simp [pathInputs],
                sameChildren, nextEqual⟩
          · rcases collision with ⟨children₁, children₂, inTail₁,
                inTail₂, distinct, sameHash⟩
            exact Or.inr ⟨children₁, children₂,
              by simpa [pathInputs] using Or.inr inTail₁,
              by simpa [pathInputs] using Or.inr inTail₂,
              distinct, sameHash⟩

/-- Full-path acceptance at the verifier's declared height and root. The
position-range premise is supplied by the masked FRI draw and tree projection.
The native multiproof must still be related to this full-path model. -/
def acceptedOpening (leafHash : List V → H) (parentHash : H × H → H)
    (root : H) (height position : Nat) (row : List V) (siblings : List H) : Prop :=
  position < 2 ^ height ∧ siblings.length = height ∧
    pathRoot parentHash (leafHash row) position siblings = root

/-- A collision produced by *these two openings*. This is a local event;
global injectivity of a finite-output cryptographic hash is not assumed. -/
def collisionOnOpenings (leafHash : List V → H) (parentHash : H × H → H)
    (position : Nat) (row₁ row₂ : List V) (siblings₁ siblings₂ : List H) : Prop :=
  (row₁ ≠ row₂ ∧ leafHash row₁ = leafHash row₂) ∨
    ∃ children₁ children₂ : H × H,
      children₁ ∈ pathInputs parentHash (leafHash row₁) position siblings₁ ∧
      children₂ ∈ pathInputs parentHash (leafHash row₂) position siblings₂ ∧
      children₁ ≠ children₂ ∧ parentHash children₁ = parentHash children₂

/-- Two accepted full-path openings of different rows at one root and index
yield a concrete hash collision. This is the symbolic Merkle binding reduction. -/
theorem conflicting_openings_produce_collision
    (leafHash : List V → H) (parentHash : H × H → H)
    (root : H) (height position : Nat)
    (row₁ row₂ : List V) (siblings₁ siblings₂ : List H)
    (accepted₁ : acceptedOpening leafHash parentHash root height position row₁ siblings₁)
    (accepted₂ : acceptedOpening leafHash parentHash root height position row₂ siblings₂)
    (differentRows : row₁ ≠ row₂) :
    collisionOnOpenings leafHash parentHash position row₁ row₂ siblings₁ siblings₂ := by
  rcases accepted₁ with ⟨_, depth₁, root₁⟩
  rcases accepted₂ with ⟨_, depth₂, root₂⟩
  have sameDepth : siblings₁.length = siblings₂.length := depth₁.trans depth₂.symm
  have sameRoot : pathRoot parentHash (leafHash row₁) position siblings₁ =
      pathRoot parentHash (leafHash row₂) position siblings₂ := root₁.trans root₂.symm
  rcases equal_roots_force_leaf_hash_or_parent_collision parentHash position
      (leafHash row₁) (leafHash row₂) siblings₁ siblings₂ sameDepth sameRoot with
    equalLeafHash | collision
  · exact Or.inl ⟨differentRows, equalLeafHash⟩
  · exact Or.inr collision

/-- A column's values in its own canonical circle-domain order. The verifier
and prover must agree on the list order used for leaf hashing. -/
structure Column (V : Type*) where
  logSize : Nat
  value : Nat → V

/-- Exact index expression used for a column above or below the lifted tree's
height. For the equal-height case both native branches reduce to `position`. -/
def projectedPosition (liftingLog columnLog position : Nat) : Nat :=
  if liftingLog < columnLog then
    2 * ((position / 2) * 2 ^ (columnLog - liftingLog)) + position % 2
  else
    2 * (position / 2 ^ (liftingLog - columnLog + 1)) + position % 2

/-- A valid query never addresses beyond the column's circle domain. The
positive-log condition matches native circle-domain construction; using a
total `Nat → V` column function does not silently excuse an out-of-range
projection. -/
theorem projectedPosition_lt (liftingLog columnLog position : Nat)
    (liftingPositive : 0 < liftingLog) (columnPositive : 0 < columnLog)
    (positionInDomain : position < 2 ^ liftingLog) :
    projectedPosition liftingLog columnLog position < 2 ^ columnLog := by
  have bitBound : position % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases smaller : liftingLog < columnLog
  · have sourcePower : 2 ^ liftingLog = 2 ^ (liftingLog - 1) * 2 := by
      have h : liftingLog - 1 + 1 = liftingLog := by omega
      calc
        2 ^ liftingLog = 2 ^ (liftingLog - 1 + 1) := by rw [h]
        _ = 2 ^ (liftingLog - 1) * 2 := by rw [pow_succ]
    have targetPower : 2 ^ columnLog =
        2 ^ liftingLog * 2 ^ (columnLog - liftingLog) := by
      rw [← pow_add]
      congr 1
      omega
    have halfBound : position / 2 < 2 ^ (liftingLog - 1) :=
      (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).2 (by
        simpa [sourcePower, Nat.mul_comm] using positionInDomain)
    have scaledBound :
        (position / 2) * 2 ^ (columnLog - liftingLog) <
          2 ^ (liftingLog - 1) * 2 ^ (columnLog - liftingLog) :=
      Nat.mul_lt_mul_of_pos_right halfBound (by positivity)
    simp only [projectedPosition, if_pos smaller]
    rw [targetPower, sourcePower]
    nlinarith
  · have liftingAtLeast : columnLog ≤ liftingLog := by omega
    have exponentSum :
        liftingLog - columnLog + 1 + (columnLog - 1) = liftingLog := by omega
    have sourcePower : 2 ^ liftingLog =
        2 ^ (liftingLog - columnLog + 1) * 2 ^ (columnLog - 1) := by
      rw [← pow_add, exponentSum]
    have targetPower : 2 ^ columnLog = 2 ^ (columnLog - 1) * 2 := by
      have h : columnLog - 1 + 1 = columnLog := by omega
      calc
        2 ^ columnLog = 2 ^ (columnLog - 1 + 1) := by rw [h]
        _ = 2 ^ (columnLog - 1) * 2 := by rw [pow_succ]
    have halfBound :
        position / 2 ^ (liftingLog - columnLog + 1) < 2 ^ (columnLog - 1) :=
      (Nat.div_lt_iff_lt_mul (by positivity :
        0 < 2 ^ (liftingLog - columnLog + 1))).2 (by
          simpa [sourcePower, Nat.mul_comm] using positionInDomain)
    simp only [projectedPosition, if_neg smaller]
    rw [targetPower]
    omega

/-- On a lifted tree at least as tall as a column, native projection divides
the coset index while retaining the conjugate-circle bit. -/
theorem projectedPosition_of_le (liftingLog columnLog position : Nat)
    (h : columnLog ≤ liftingLog) :
    projectedPosition liftingLog columnLog position =
      2 * ((position / 2) / 2 ^ (liftingLog - columnLog)) + position % 2 := by
  simp only [projectedPosition, if_neg (Nat.not_lt.mpr h)]
  have exponent : liftingLog - columnLog + 1 = 1 + (liftingLog - columnLog) := by omega
  rw [exponent, pow_add, pow_one]
  rw [Nat.div_div_eq_div_mul]

/-- Projecting a lifted query first to a shorter tree and then to a column
agrees exactly with direct projection to that column. This is a pure index
lemma; it does not assert that the native Merkle row contains that value. -/
theorem projectedPosition_compose (liftingLog treeLog columnLog position : Nat)
    (columnLeTree : columnLog ≤ treeLog) (treeLeLifting : treeLog ≤ liftingLog) :
    projectedPosition treeLog columnLog
      (projectedPosition liftingLog treeLog position) =
    projectedPosition liftingLog columnLog position := by
  rw [projectedPosition_of_le treeLog columnLog _ columnLeTree,
      projectedPosition_of_le liftingLog treeLog _ treeLeLifting,
      projectedPosition_of_le liftingLog columnLog _ (by omega)]
  have bitBound : position % 2 < 2 := Nat.mod_lt _ (by omega)
  have half :
      (2 * ((position / 2) / 2 ^ (liftingLog - treeLog)) + position % 2) / 2 =
        (position / 2) / 2 ^ (liftingLog - treeLog) := by omega
  have bit :
      (2 * ((position / 2) / 2 ^ (liftingLog - treeLog)) + position % 2) % 2 =
        position % 2 := by omega
  rw [half, bit, Nat.div_div_eq_div_mul, ← pow_add]
  have exponent : liftingLog - treeLog + (treeLog - columnLog) =
      liftingLog - columnLog := by omega
  rw [exponent]

/-- The explicit-height gate profile queries a tree at the full lifted
height, so its first projection is the identity. -/
theorem projectedPosition_same (liftingLog position : Nat) :
    projectedPosition liftingLog liftingLog position = position := by
  rw [projectedPosition_of_le liftingLog liftingLog position (Nat.le_refl _)]
  simp
  omega

/-- For the sealed fold-step-1 gate geometry with height 21, the per-column
index is the direct projection even when modeled via the tree query. The
premise `columnLog ≤ 21` is separately checked from the package roster. -/
theorem gate21_tree_column_position (columnLog position : Nat)
    (columnLeHeight : columnLog ≤ 21) :
    projectedPosition 21 columnLog (projectedPosition 21 21 position) =
      projectedPosition 21 columnLog position := by
  exact projectedPosition_compose 21 21 columnLog position columnLeHeight (Nat.le_refl _)

/-- Ideal lifted leaf row, in the same pre-agreed column order that the native
Merkle hasher uses after sorting columns by log size. -/
def projectedRow (liftingLog position : Nat) (columns : List (Column V)) : List V :=
  columns.map fun column =>
    column.value (projectedPosition liftingLog column.logSize position)

/-- Conditional native-to-ideal opening refinement at one queried leaf. The
committed opening premise must come from a tree whose leaves were built from
`projectedRow`; the native opening premise must come from verified multiproof
reconstruction. Without either cryptographic collision event, the native row
equals the projected committed row. -/
theorem accepted_row_refines_projected_commitment
    (leafHash : List V → H) (parentHash : H × H → H)
    (root : H) (height position : Nat) (columns : List (Column V))
    (nativeRow : List V) (committedPath nativePath : List H)
    (committed : acceptedOpening leafHash parentHash root height position
      (projectedRow height position columns) committedPath)
    (native : acceptedOpening leafHash parentHash root height position
      nativeRow nativePath)
    (noCollisionOnTheseOpenings :
      ¬collisionOnOpenings leafHash parentHash position nativeRow
        (projectedRow height position columns) nativePath committedPath) :
    nativeRow = projectedRow height position columns := by
  by_contra different
  have clash := conflicting_openings_produce_collision leafHash parentHash
    root height position nativeRow (projectedRow height position columns)
    nativePath committedPath native committed different
  exact noCollisionOnTheseOpenings clash

end S31.Gadgets.PcsFri.MerkleOpening
