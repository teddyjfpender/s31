import Mathlib.Tactic

/-!
Arithmetic refinement for the `usize` indices and flat capture buffers in the
pinned lifted Merkle verifier. This is an all-input theorem about the operations
used by `verifyImpl`; it is not a Zig operational-semantics theorem, nor a
collision-resistance claim.

The selected Gate trace capture has 70 raw query slots and height 21. The
machine-independent buffer result below applies to every word size at least
11 bits, so it includes the supported 32- and 64-bit targets. It does not
cover a differently configured FRI layer or an unbounded direct caller of the
engine verifier.
-/

namespace S31.Gadgets.PcsFri.NativeCaptureIndexBounds

/-- The native guard skips its shift when `height` reaches the machine width.
The representation premise describes a `usize` input. -/
def nativeRangeGuard (wordBits height position : Nat) : Prop :=
  position < 2 ^ wordBits ∧
    (if height < wordBits then position < 2 ^ height else True)

/-- At every representable `usize`, the native branch has exactly the ideal
tree-domain meaning, including at and above the machine-word boundary. -/
theorem nativeRangeGuard_iff (wordBits height position : Nat) :
    nativeRangeGuard wordBits height position ↔
      position < 2 ^ wordBits ∧ position < 2 ^ height := by
  unfold nativeRangeGuard
  by_cases below : height < wordBits
  · simp [below]
  · have order : wordBits ≤ height := Nat.le_of_not_gt below
    have power : 2 ^ wordBits ≤ 2 ^ height :=
      Nat.pow_le_pow_right (by omega) order
    simp only [if_neg below, and_true]
    constructor
    · intro represented
      exact ⟨represented, lt_of_lt_of_le represented power⟩
    · exact And.left

/-- The source's unsigned right shift is the mathematical division used by
the Lean full-opening and caller-order models. -/
theorem nativeAncestor_eq_div (position layer : Nat) :
    position >>> layer = position / 2 ^ layer :=
  Nat.shiftRight_eq_div_pow position layer

/-- A well-shaped height-level opening necessarily has final index zero;
there is no high-bit alias after the native range guard. -/
theorem nativeFinalIndex_zero (wordBits height position : Nat)
    (accepted : nativeRangeGuard wordBits height position) :
    position >>> height = 0 := by
  rw [nativeAncestor_eq_div]
  exact Nat.div_eq_of_lt ((nativeRangeGuard_iff wordBits height position).mp accepted).2

/-- Native adjacent-position deduplication can never create more unique slots
than the original list, independently of sorting and duplicate placement. -/
def dedupTail (previous : Nat) : List Nat → List Nat
  | [] => []
  | position :: rest =>
      if position == previous then dedupTail position rest
      else position :: dedupTail position rest

def dedupAdjacent : List Nat → List Nat
  | [] => []
  | position :: rest => position :: dedupTail position rest

theorem dedupTail_length_le (previous : Nat) :
    ∀ positions : List Nat, (dedupTail previous positions).length ≤ positions.length := by
  intro positions
  induction positions generalizing previous with
  | nil => simp [dedupTail]
  | cons position rest ih =>
      simp only [dedupTail]
      split_ifs
      · have bound := ih position
        simp at bound ⊢
        omega
      · simpa using Nat.succ_le_succ (ih position)

theorem dedupAdjacent_length_le (positions : List Nat) :
    (dedupAdjacent positions).length ≤ positions.length := by
  cases positions with
  | nil => simp [dedupAdjacent]
  | cons position rest =>
      simpa [dedupAdjacent] using
        Nat.succ_le_succ (dedupTail_length_le position rest)

/-- Exact cursor updates of the native final copy loop on a sorted position
sequence. The caller's original slot is a separate destination index. -/
def copyTail (previous cursor : Nat) : List Nat → List Nat
  | [] => []
  | position :: rest =>
      let next := if position == previous then cursor else cursor + 1
      next :: copyTail position next rest

def copyCursors : List Nat → List Nat
  | [] => []
  | position :: rest => 0 :: copyTail position 0 rest

theorem copyTail_length (previous cursor : Nat) (positions : List Nat) :
    (copyTail previous cursor positions).length = positions.length := by
  induction positions generalizing previous cursor with
  | nil => rfl
  | cons position rest ih =>
      simp [copyTail, ih]

theorem copyCursors_length (positions : List Nat) :
    (copyCursors positions).length = positions.length := by
  cases positions with
  | nil => rfl
  | cons position rest => simp [copyCursors, copyTail_length]

/-- Every cursor emitted by the source-shaped transition loop refers to a
member of the source-shaped adjacent-deduplicated path array. This holds for
all finite position lists; the native heap-sort order is not needed for the
memory-bound result. -/
theorem copyTail_cursor_bound (previous cursor : Nat) :
    ∀ positions : List Nat, ∀ index ∈ copyTail previous cursor positions,
      index < cursor + 1 + (dedupTail previous positions).length := by
  intro positions
  induction positions generalizing previous cursor with
  | nil => simp [copyTail]
  | cons position rest ih =>
      intro index member
      by_cases equal : position == previous
      · simp only [copyTail, dedupTail, equal,
          ↓reduceIte, List.mem_cons] at member ⊢
        rcases member with rfl | member
        · omega
        · have bound := ih position cursor index member
          omega
      · simp only [copyTail, dedupTail, equal, Bool.false_eq_true,
          ↓reduceIte, List.mem_cons, List.length_cons] at member ⊢
        rcases member with rfl | member
        · omega
        · have bound := ih position (cursor + 1) index member
          omega

theorem copyCursors_in_unique_range (positions : List Nat)
    (cursor : Nat) (member : cursor ∈ copyCursors positions) :
    cursor < (dedupAdjacent positions).length := by
  cases positions with
  | nil => simp [copyCursors] at member
  | cons position rest =>
      simp only [copyCursors, List.mem_cons] at member
      rcases member with rfl | member
      · simp [dedupAdjacent]
      · have bound := copyTail_cursor_bound position 0 rest cursor member
        simp only [dedupAdjacent, List.length_cons]
        omega

/-- The native flat-array address for one whole path stays within its
allocated `count * depth` elements. -/
theorem pathSlice_end_le (count depth slot : Nat) (slotInRange : slot < count) :
    slot * depth + depth ≤ count * depth := by
  calc
    slot * depth + depth = (slot + 1) * depth := by ring
    _ ≤ count * depth := Nat.mul_le_mul_right depth (by omega)

/-- Every selected Gate trace capture buffer length and element offset fits a
machine word. The premise describes the reviewed 70-slot/21-height roster;
it is not asserted for a different Gate package or a FRI-layer opening. -/
theorem gateTrace_capacity_lt_word (wordBits count depth : Nat)
    (wordWideEnough : 11 ≤ wordBits)
    (queryBound : count ≤ 70) (heightBound : depth ≤ 21) :
    count * depth < 2 ^ wordBits := by
  have productBound : count * depth ≤ 70 * 21 :=
    Nat.mul_le_mul queryBound heightBound
  have powerBound : 2 ^ 11 ≤ 2 ^ wordBits :=
    Nat.pow_le_pow_right (by omega) wordWideEnough
  calc
    count * depth ≤ 70 * 21 := productBound
    _ < 2 ^ 11 := by norm_num
    _ ≤ 2 ^ wordBits := powerBound

/-- With 32-byte BLAKE2s digests, the whole selected trace capture also fits
in byte-address arithmetic on any machine with at least 16-bit words. -/
theorem gateTrace_bytes_lt_word (wordBits count depth : Nat)
    (wordWideEnough : 16 ≤ wordBits)
    (queryBound : count ≤ 70) (heightBound : depth ≤ 21) :
    count * depth * 32 < 2 ^ wordBits := by
  have productBound : count * depth ≤ 70 * 21 :=
    Nat.mul_le_mul queryBound heightBound
  have byteBound : count * depth * 32 ≤ (70 * 21) * 32 :=
    Nat.mul_le_mul_right 32 productBound
  have powerBound : 2 ^ 16 ≤ 2 ^ wordBits :=
    Nat.pow_le_pow_right (by omega) wordWideEnough
  calc
    count * depth * 32 ≤ 70 * 21 * 32 := byteBound
    _ < 2 ^ 16 := by norm_num
    _ ≤ 2 ^ wordBits := powerBound

/-- The path copy's source and destination ends fit the selected Gate trace
buffer for all slot counts, including zero and repeated query positions. -/
theorem gateTrace_copy_offsets_safe (wordBits count unique depth source dest : Nat)
    (wordWideEnough : 11 ≤ wordBits)
    (queryBound : count ≤ 70) (heightBound : depth ≤ 21)
    (uniqueBound : unique ≤ count)
    (sourceInRange : source < unique) (destInRange : dest < count) :
    source * depth + depth ≤ unique * depth ∧
    dest * depth + depth ≤ count * depth ∧
    unique * depth < 2 ^ wordBits ∧ count * depth < 2 ^ wordBits := by
  refine ⟨pathSlice_end_le unique depth source sourceInRange,
    pathSlice_end_le count depth dest destInRange, ?_,
    gateTrace_capacity_lt_word wordBits count depth wordWideEnough queryBound heightBound⟩
  exact gateTrace_capacity_lt_word wordBits unique depth wordWideEnough
    (uniqueBound.trans queryBound) heightBound

/-- Composing the source-shaped adjacent deduplication and cursor update
eliminates both assumed source-index bounds from the selected trace path.
It covers every finite query list, including empty lists and duplicates. -/
theorem gateTrace_copy_model_safe (wordBits depth dest cursor : Nat)
    (positions : List Nat)
    (wordWideEnough : 11 ≤ wordBits)
    (queryBound : positions.length ≤ 70) (heightBound : depth ≤ 21)
    (destinationInRange : dest < positions.length)
    (cursorEmitted : cursor ∈ copyCursors positions) :
    cursor * depth + depth ≤ (dedupAdjacent positions).length * depth ∧
    dest * depth + depth ≤ positions.length * depth ∧
    (dedupAdjacent positions).length * depth < 2 ^ wordBits ∧
    positions.length * depth < 2 ^ wordBits := by
  exact gateTrace_copy_offsets_safe wordBits positions.length
    (dedupAdjacent positions).length depth cursor dest wordWideEnough
    queryBound heightBound (dedupAdjacent_length_le positions)
    (copyCursors_in_unique_range positions cursor cursorEmitted)
    destinationInRange

end S31.Gadgets.PcsFri.NativeCaptureIndexBounds
