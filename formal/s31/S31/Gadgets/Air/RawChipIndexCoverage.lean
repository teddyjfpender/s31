import Mathlib.Tactic

/-!
The native tagged chip does not locally range-check or sort its witness step
column. This module begins the missing arbitrary-row reduction. It models
one call's exact tagged event balance, projects away state values, and proves
that every canonical index `0..R-1` is represented by a different native row
when there are exactly `R` rows and `0 < R < p`. Thus an unattached cycle has
no spare row. The actual native profile has `16 ≤ R ≤ 32768 < p`.

This exact permutation is an explicit premise, not a theorem about the
production random-challenge LogUp AIR or PCS. The full value-bearing row
reindexing and composition with `IndexedChipPath` remain separate obligations.
-/

namespace S31.Gadgets.Air.RawChipIndexCoverage

variable {F : Type*}

structure RawRow (F : Type*) where
  index : Nat
  input : F
  output : F

/-- One call's consumed index events, including the authenticated end. -/
def useIndices {R : Nat} (index : Fin R → Nat) : List Nat :=
  R :: List.ofFn index

/-- One call's produced index events, including the authenticated start.
The modulo operation models the M31 step-field addition in the native AIR. -/
def yieldIndices {R : Nat} (p : Nat) (index : Fin R → Nat) : List Nat :=
  0 :: List.ofFn (fun row => (index row + 1) % p)

def useEvents {R : Nat} (rows : Fin R → RawRow F) (finish : F) :
    List (Nat × F) :=
  (R, finish) :: List.ofFn (fun row => ((rows row).index, (rows row).input))

def yieldEvents {R : Nat} (p : Nat) (rows : Fin R → RawRow F)
    (start : F) : List (Nat × F) :=
  (0, start) :: List.ofFn
    (fun row => (((rows row).index + 1) % p, (rows row).output))

/-- Full state-event balance entails balance after projecting to the witness
step coordinate. The omitted call tag is a verifier-fixed constant for each
of the two native chip components. Separating the calls from the single
five-component compressed closure remains an earlier probabilistic step. -/
theorem index_balance_of_event_balance {R p : Nat}
    (rows : Fin R → RawRow F) (start finish : F)
    (hbalance : (useEvents rows finish).Perm
      (yieldEvents p rows start)) :
    (useIndices (fun row => (rows row).index)).Perm
      (yieldIndices p (fun row => (rows row).index)) := by
  simpa [useEvents, yieldEvents, useIndices, yieldIndices] using
    hbalance.map Prod.fst

private theorem row_of_use_index {R : Nat} (index : Fin R → Nat)
    (value : Nat) (hvalue : value < R)
    (hmember : value ∈ useIndices index) :
    ∃ row : Fin R, index row = value := by
  simp only [useIndices, List.mem_cons] at hmember
  rcases hmember with hterminal | hrow
  · omega
  · exact List.mem_ofFn.mp hrow

/-- Exact index balance forces coverage of every canonical step. Starting at
index zero, each produced index `n+1` must be consumed by another row until
the terminal index `R` is reached. `R < p` prevents wrap along this path. -/
theorem every_canonical_index_covered {R p : Nat}
    (index : Fin R → Nat) (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useIndices index).Perm (yieldIndices p index)) :
    ∀ canonical : Fin R, ∃ row : Fin R,
      index row = canonical.val := by
  have hstart : ∃ row : Fin R, index row = 0 := by
    apply row_of_use_index index 0 hpositive
    apply hbalance.mem_iff.mpr
    simp [yieldIndices]
  have hprefix (n : Nat) (hn : n < R) :
      ∃ row : Fin R, index row = n := by
    induction n generalizing hn with
    | zero => exact hstart
    | succ n ih =>
        obtain ⟨previous, hprevious⟩ := ih (by omega)
        have hnext_lt_p : n + 1 < p := by omega
        have hyield : (index previous + 1) % p ∈
            yieldIndices p index := by
          simp only [yieldIndices, List.mem_cons]
          exact Or.inr (List.mem_ofFn.mpr ⟨previous, rfl⟩)
        have huse := hbalance.mem_iff.mpr hyield
        have hnext : (index previous + 1) % p = n + 1 := by
          rw [hprevious, Nat.mod_eq_of_lt hnext_lt_p]
        have hcanonical_use : n + 1 ∈ useIndices index := by
          simpa only [hnext] using huse
        exact row_of_use_index index (n + 1) hn hcanonical_use
  intro canonical
  exact hprefix canonical.val canonical.isLt

/-- Choose one native row for each canonical index. These chosen rows are
injective because distinct canonical indices cannot label the same row.
Since both finite sets have cardinality `R`, this is mathematically a
permutation; the stronger Lean equivalence and value-bearing joins are the
next composition step. -/
theorem injective_canonical_order {R p : Nat}
    (index : Fin R → Nat) (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useIndices index).Perm (yieldIndices p index)) :
    ∃ order : Fin R → Fin R,
      Function.Injective order ∧
      ∀ canonical : Fin R, index (order canonical) = canonical.val := by
  classical
  have hcovered := every_canonical_index_covered index hpositive
    hmodulus hbalance
  let order : Fin R → Fin R := fun canonical =>
    Classical.choose (hcovered canonical)
  have horder (canonical : Fin R) :
      index (order canonical) = canonical.val :=
    Classical.choose_spec (hcovered canonical)
  have hinjective : Function.Injective order := by
    intro left right heq
    apply Fin.ext
    calc
      left.val = index (order left) := (horder left).symm
      _ = index (order right) := congrArg index heq
      _ = right.val := horder right
  exact ⟨order, hinjective, horder⟩

/-- The arbitrary-row theorem starts from the full value-bearing event
multiset, not a prover-supplied canonical order. It currently concludes the
injective canonical row selection. -/
theorem canonical_order_of_exact_events {R p : Nat}
    (rows : Fin R → RawRow F) (start finish : F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useEvents rows finish).Perm
      (yieldEvents p rows start)) :
    ∃ order : Fin R → Fin R,
      Function.Injective order ∧
      ∀ canonical : Fin R,
        (rows (order canonical)).index = canonical.val := by
  exact injective_canonical_order
    (fun row => (rows row).index) hpositive hmodulus
    (index_balance_of_event_balance rows start finish hbalance)

end S31.Gadgets.Air.RawChipIndexCoverage
