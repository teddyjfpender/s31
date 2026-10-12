import S31.Gadgets.Air.Qm31Ops

/-!
S31 arrays are packed four M31 lanes per circuit wire. The final wire may have
one, two, or three active lanes. This module proves the local AIR row's active
lanes are correct for any padding of the unused input lanes, and constructs a
full packed output witness for every correct active-lane result.
-/

namespace S31.Gadgets.Air.SimdChunks

open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops

/-- Fill unused positions of a short final chunk with arbitrary M31 values. -/
def pad4 {n : Nat} (hn : n ≤ 4) (active : Fin n → S31.M31)
    (tail : Fin 4 → S31.M31) : Fin 4 → S31.M31 :=
  fun i => if hi : i.val < n then active ⟨i.val, hi⟩ else tail i

theorem pad4_active {n : Nat} (hn : n ≤ 4) (active : Fin n → S31.M31)
    (tail : Fin 4 → S31.M31) (i : Fin n) :
    pad4 hn active tail ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ = active i := by
  simp [pad4, i.isLt]

/-- One circuit AIR row accepts a short S31 array chunk exactly when all its
active claimed M31 lanes equal native source arithmetic. The unused input
lanes can be any M31 values, and the output's unused limbs are existential
witnesses constrained by the full row equation. -/
theorem partial_row_iff {n : Nat} (hn : n ≤ 4) (multiply : Bool)
    (a b claimed : Fin n → S31.M31)
    (tailA tailB : Fin 4 → S31.M31) :
    (∃ packedOutput : Quad,
      accepts (encode (s31Op multiply))
        (packM31 (pad4 hn a tailA))
        (packM31 (pad4 hn b tailB)) packedOutput ∧
      ∀ i : Fin n,
        coord packedOutput ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ =
          S31.Field.toZMod (claimed i)) ↔
    ∀ i : Fin n,
      claimed i = if multiply then a i * b i else a i + b i := by
  constructor
  · rintro ⟨packedOutput, hrow, hclaim⟩ i
    have hrow' := (s31_row_iff multiply (pad4 hn a tailA)
      (pad4 hn b tailB) packedOutput).mp hrow
      ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
    rw [pad4_active hn a tailA i, pad4_active hn b tailB i] at hrow'
    exact S31.Field.toZMod_injective ((hclaim i).symm.trans hrow')
  · intro h
    refine ⟨evaluate (s31Op multiply)
      (packM31 (pad4 hn a tailA))
      (packM31 (pad4 hn b tailB)), honest_row _ _ _, ?_⟩
    intro i
    rw [s31Op_coord]
    rw [pad4_active hn a tailA i, pad4_active hn b tailB i]
    rw [h i]

/-- Compose the short-chunk AIR relation with the executable normalized
relation node, including its exact output shape and native M31 values. -/
theorem partial_row_iff_normalized_node {n : Nat} (hn : n ≤ 4)
    (multiply : Bool) (a b claimed : Fin n → S31.M31)
    (tailA tailB : Fin 4 → S31.M31) :
    (∃ packedOutput : Quad,
      accepts (encode (s31Op multiply))
        (packM31 (pad4 hn a tailA))
        (packM31 (pad4 hn b tailB)) packedOutput ∧
      ∀ i : Fin n,
        coord packedOutput ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ =
          S31.Field.toZMod (claimed i)) ↔
    S31.evaluateNode (S31.Functional.arithmeticEnv a b)
      (S31.Functional.arithmeticNode multiply) =
        .ok ⟨.m31, List.ofFn claimed⟩ := by
  rw [partial_row_iff, S31.Functional.arithmeticNode_eval]
  constructor
  · intro h
    have heq : (fun i : Fin n => if multiply then a i * b i else a i + b i) =
        claimed := by
      funext i
      exact (h i).symm
    rw [heq]
  · intro h
    have hlist : List.ofFn
        (fun i : Fin n => if multiply then a i * b i else a i + b i) =
        List.ofFn claimed := by
      injection h with hvalue
      exact congrArg S31.Value.words hvalue
    have heq := List.ofFn_injective hlist
    intro i
    exact (congrFun heq i).symm

/-- Read one packed circuit wire from an arbitrary-length source array.
Inactive positions in the last wire receive explicit arbitrary padding. -/
def chunk4 {n : Nat} (values : Fin n → S31.M31) (block : Nat)
    (tail : Fin 4 → S31.M31) : Fin 4 → S31.M31 :=
  fun i => if h : block * 4 + i.val < n then
    values ⟨block * 4 + i.val, h⟩ else tail i

theorem chunk4_active {n : Nat} (values : Fin n → S31.M31)
    (block : Nat) (tail : Fin 4 → S31.M31) (i : Fin 4)
    (h : block * 4 + i.val < n) :
    chunk4 values block tail i = values ⟨block * 4 + i.val, h⟩ := by
  simp [chunk4, h]

/-- Exactly `ceil(n/4)` arithmetic rows constrain every active lane.
The unused limbs of a final short row are existential output witnesses. -/
def packedRows {n : Nat} (multiply : Bool)
    (a b claimed : Fin n → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) : Prop :=
  ∀ block : Fin ((n + 3) / 4), ∃ packedOutput : Quad,
    accepts (encode (s31Op multiply))
      (packM31 (chunk4 a block.val (tailA block.val)))
      (packM31 (chunk4 b block.val (tailB block.val))) packedOutput ∧
    ∀ (i : Fin 4) (h : block.val * 4 + i.val < n),
      coord packedOutput i =
        S31.Field.toZMod (claimed ⟨block.val * 4 + i.val, h⟩)

/-- Every active lane in an arbitrary-length normalized arithmetic node is
equivalent to a witness satisfying all of its packed AIR rows. No active
lane can be omitted at a four-lane boundary, and arbitrary inactive padding
cannot alter a claimed result. -/
theorem packedRows_iff {n : Nat} (multiply : Bool)
    (a b claimed : Fin n → S31.M31)
    (tailA tailB : Nat → Fin 4 → S31.M31) :
    packedRows multiply a b claimed tailA tailB ↔
      ∀ i : Fin n,
        claimed i = if multiply then a i * b i else a i + b i := by
  constructor
  · intro rows j
    have hblock : j.val / 4 < (n + 3) / 4 := by omega
    let block : Fin ((n + 3) / 4) := ⟨j.val / 4, hblock⟩
    have hlimb : j.val % 4 < 4 := by omega
    let limb : Fin 4 := ⟨j.val % 4, hlimb⟩
    have hindex : block.val * 4 + limb.val < n := by
      dsimp [block, limb]
      omega
    obtain ⟨output, hrow, hclaim⟩ := rows block
    have hvalue := (s31_row_iff multiply
      (chunk4 a block.val (tailA block.val))
      (chunk4 b block.val (tailB block.val)) output).mp hrow limb
    rw [chunk4_active a block.val (tailA block.val) limb hindex,
      chunk4_active b block.val (tailB block.val) limb hindex] at hvalue
    have hsource := S31.Field.toZMod_injective
      ((hclaim limb hindex).symm.trans hvalue)
    have hsame : (⟨block.val * 4 + limb.val, hindex⟩ : Fin n) = j := by
      apply Fin.ext
      dsimp [block, limb]
      omega
    simpa [hsame] using hsource
  · intro h block
    refine ⟨evaluate (s31Op multiply)
      (packM31 (chunk4 a block.val (tailA block.val)))
      (packM31 (chunk4 b block.val (tailB block.val))),
      honest_row _ _ _, ?_⟩
    intro i hi
    rw [s31Op_coord, chunk4_active a block.val (tailA block.val) i hi,
      chunk4_active b block.val (tailB block.val) i hi, h]

end S31.Gadgets.Air.SimdChunks
