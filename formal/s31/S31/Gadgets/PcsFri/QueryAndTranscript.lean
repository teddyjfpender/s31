import Mathlib.Data.Finset.Image

/-!
Small, source-bound PCS/FRI invariants for the selected
`Blake2sM31MerkleChannel` profile.

The native channel hashes `digest || root` for a Merkle commitment and hashes
`digest || little_endian_u32(draw_counter) || 0x00` for a draw. The functions
below model those *hash inputs*, not BLAKE2s or its collision resistance.
For a fixed state, a changed root or draw counter encoding cannot silently
disappear before hashing. These messages are not tagged by operation type;
the reviewed protocol's fixed call order remains a separate obligation.

The native verifier normalizes transcript queries to a sorted set and folds
their positions by right shifting. Finsets model the set semantics. All
logical raw draws, including duplicates, remain checked after each such
normalization. This does not establish uniform Fiat-Shamir sampling, Merkle
binding, low-degree testing, or overall STARK soundness.
-/

namespace S31.Gadgets.PcsFri.QueryAndTranscript

abbrev Bytes := List UInt8

/-- Input bytes to `Blake2sMerkleChannelGeneric.mixRoot`, before hashing. -/
def rootMessage (digest root : Bytes) : Bytes := digest ++ root

/-- Input bytes to `Blake2sChannelGeneric.drawU32s`, before hashing. -/
def drawMessage (digest counterLE : Bytes) : Bytes :=
  digest ++ counterLE ++ [0]

theorem root_message_injective_at_fixed_digest (digest root₁ root₂ : Bytes)
    (h : rootMessage digest root₁ = rootMessage digest root₂) :
    root₁ = root₂ := by
  simpa [rootMessage] using h

theorem draw_message_injective_at_fixed_digest (digest counter₁ counter₂ : Bytes)
    (h : drawMessage digest counter₁ = drawMessage digest counter₂) :
    counter₁ = counter₂ := by
  simpa [drawMessage] using h

/-- The sorted, deduplicated `Queries.positions` has exactly this support. -/
def normalized (raw : List Nat) : Finset Nat := raw.toFinset

/-- A native right shift by `k` on a nonnegative query position. -/
def foldPosition (k q : Nat) : Nat := q / 2 ^ k

/-- The support of a FRI query set after a `k`-level fold. -/
def folded (k : Nat) (raw : List Nat) : Finset Nat :=
  (raw.map (foldPosition k)).toFinset

theorem folded_eq_image_of_normalized (k : Nat) (raw : List Nat) :
    folded k raw = (normalized raw).image (foldPosition k) := by
  ext q
  simp [folded, normalized]

/-- Deduplication does not omit a logical query predicate, even with
colliding or repeated raw transcript draws. -/
theorem all_raw_iff_all_normalized (raw : List Nat) (P : Nat → Prop) :
    (∀ q ∈ raw, P q) ↔ (∀ q ∈ normalized raw, P q) := by
  simp [normalized]

/-- Query predicates after a fold cover exactly the folded raw draws. -/
theorem all_folded_iff_all_raw (k : Nat) (raw : List Nat) (P : Nat → Prop) :
    (∀ q ∈ folded k raw, P q) ↔
      (∀ q ∈ raw, P (foldPosition k q)) := by
  simp [folded]

/-- Every actual raw query has a corresponding authenticated folded position. -/
theorem every_raw_has_folded_position (k : Nat) (raw : List Nat)
    (q : Nat) (hq : q ∈ raw) :
    foldPosition k q ∈ folded k raw := by
  simp only [folded, List.mem_toFinset, List.mem_map]
  exact ⟨q, hq, rfl⟩

/-- Consecutive one- or four-level index folds address the same terminal
position as one fold by their total number of levels. This is an index
identity, not a proof that the field-valued butterfly is correct. -/
theorem fold_position_composes (a b q : Nat) :
    foldPosition a (foldPosition b q) = foldPosition (a + b) q := by
  simp [foldPosition, Nat.div_div_eq_div_mul, Nat.pow_add, Nat.mul_comm]

theorem folded_set_composes (a b : Nat) (raw : List Nat) :
    (folded b raw).image (foldPosition a) = folded (a + b) raw := by
  ext q
  simp [folded, fold_position_composes]

end S31.Gadgets.PcsFri.QueryAndTranscript
