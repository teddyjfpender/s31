import Mathlib.Tactic

/-!
The native tagged chip does not locally range-check or sort its witness step
column. This module begins the missing arbitrary-row reduction. It models
one call's exact tagged event balance, projects away state values, and proves
that every canonical index `0..R-1` is represented by a different native row
when there are exactly `R` rows and `0 < R < p`. Thus an unattached cycle has
no spare row. It then proves the unique finite reindexing, all state-value
joins, and the two-call end-state theorem. The actual native profile has
`16 ≤ R ≤ 32768 < p`.

This exact permutation is an explicit premise, not a theorem about the
production random-challenge LogUp AIR or PCS. Correspondence to the native
seven-coordinate tuples, bridge AIR, and verifier remains a separate
obligation.
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
    induction n with
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

/-- Equal finite row sets turn the injective canonical selection into a
bijective reindexing. This proves that every raw row, including a potentially
malformed witness row, is used by exactly one canonical step. -/
theorem canonical_equiv_of_exact_events {R p : Nat}
    (rows : Fin R → RawRow F) (start finish : F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useEvents rows finish).Perm
      (yieldEvents p rows start)) :
    ∃ order : Fin R ≃ Fin R,
      ∀ canonical : Fin R,
        (rows (order canonical)).index = canonical.val := by
  obtain ⟨order, hinjective, hindex⟩ :=
    canonical_order_of_exact_events rows start finish hpositive hmodulus
      hbalance
  let equivalent : Fin R ≃ Fin R := Equiv.ofBijective order
    ⟨hinjective, Finite.surjective_of_injective hinjective⟩
  exact ⟨equivalent, hindex⟩

/-- There is only one bijection assigning every raw row its canonical step
index. A proposed alternative row order cannot change the authenticated
path while preserving the same witness indices. -/
theorem canonical_equiv_unique {R : Nat}
    (rows : Fin R → RawRow F)
    (left right : Fin R ≃ Fin R)
    (hleft : ∀ i, (rows (left i)).index = i.val)
    (hright : ∀ i, (rows (right i)).index = i.val) :
    left = right := by
  have hindexInjective : Function.Injective
      (fun row : Fin R => (rows row).index) := by
    intro a b heq
    obtain ⟨i, rfl⟩ := left.surjective a
    obtain ⟨j, rfl⟩ := left.surjective b
    have hij : i = j := Fin.ext (by
      calc
        i.val = (rows (left i)).index := (hleft i).symm
        _ = (rows (left j)).index := heq
        _ = j.val := hleft j)
    exact congrArg left hij
  apply Equiv.ext
  intro i
  apply hindexInjective
  change (rows (left i)).index = (rows (right i)).index
  rw [hleft i, hright i]

private theorem raw_index_injective {R : Nat}
    (rows : Fin R → RawRow F) (order : Fin R ≃ Fin R)
    (hindex : ∀ i, (rows (order i)).index = i.val) :
    Function.Injective (fun row : Fin R => (rows row).index) := by
  intro a b heq
  obtain ⟨i, rfl⟩ := order.surjective a
  obtain ⟨j, rfl⟩ := order.surjective b
  have hij : i = j := Fin.ext (by
    calc
      i.val = (rows (order i)).index := (hindex i).symm
      _ = (rows (order j)).index := heq
      _ = j.val := hindex j)
  exact congrArg order hij

private theorem raw_index_lt {R : Nat}
    (rows : Fin R → RawRow F) (order : Fin R ≃ Fin R)
    (hindex : ∀ i, (rows (order i)).index = i.val)
    (row : Fin R) : (rows row).index < R := by
  obtain ⟨i, rfl⟩ := order.surjective row
  rw [hindex i]
  exact i.isLt

private theorem use_event_is_row_or_end {R : Nat}
    (rows : Fin R → RawRow F) (finish : F)
    (key : Nat) (value : F)
    (hmember : (key, value) ∈ useEvents rows finish) :
    (key = R ∧ value = finish) ∨
      ∃ row : Fin R,
        (rows row).index = key ∧ (rows row).input = value := by
  simp only [useEvents, List.mem_cons] at hmember
  rcases hmember with hterminal | hrow
  · exact Or.inl ⟨congrArg Prod.fst hterminal,
      congrArg Prod.snd hterminal⟩
  · obtain ⟨row, hrow⟩ := List.mem_ofFn.mp hrow
    exact Or.inr ⟨row, congrArg Prod.fst hrow,
      congrArg Prod.snd hrow⟩

/-- Once raw rows are reindexed by their proved witness indices, the full
value-bearing multiset forces the authenticated start, every adjacency, and
the authenticated end. No row ordering is trusted from the prover. -/
theorem raw_value_joins {R p : Nat}
    (rows : Fin R → RawRow F) (start finish : F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useEvents rows finish).Perm
      (yieldEvents p rows start))
    (order : Fin R ≃ Fin R)
    (hindex : ∀ i, (rows (order i)).index = i.val) :
    (rows (order ⟨0, hpositive⟩)).input = start ∧
    (∀ i : Fin R, ∀ hnext : i.val + 1 < R,
      (rows (order ⟨i.val + 1, hnext⟩)).input =
        (rows (order i)).output) ∧
    (rows (order ⟨R - 1, by omega⟩)).output = finish := by
  have hindexInjective := raw_index_injective rows order hindex
  have hstart : (rows (order ⟨0, hpositive⟩)).input = start := by
    have hyield : (0, start) ∈ yieldEvents p rows start := by
      simp [yieldEvents]
    have huse := hbalance.mem_iff.mpr hyield
    rcases use_event_is_row_or_end rows finish 0 start huse with
      hterminal | ⟨row, hrowIndex, hrowValue⟩
    · omega
    · have hrow : row = order ⟨0, hpositive⟩ := by
        apply hindexInjective
        change (rows row).index = (rows (order ⟨0, hpositive⟩)).index
        rw [hrowIndex, hindex]
      rw [← hrow]
      exact hrowValue
  have hlinks : ∀ i : Fin R, ∀ hnext : i.val + 1 < R,
      (rows (order ⟨i.val + 1, hnext⟩)).input =
        (rows (order i)).output := by
    intro i hnext
    have hyield :
        (((rows (order i)).index + 1) % p,
          (rows (order i)).output) ∈ yieldEvents p rows start := by
      simp only [yieldEvents, List.mem_cons]
      exact Or.inr (List.mem_ofFn.mpr ⟨order i, rfl⟩)
    have huse := hbalance.mem_iff.mpr hyield
    have hkey : ((rows (order i)).index + 1) % p = i.val + 1 := by
      rw [hindex i, Nat.mod_eq_of_lt (by omega : i.val + 1 < p)]
    rcases use_event_is_row_or_end rows finish _ _ huse with
      hterminal | ⟨row, hrowIndex, hrowValue⟩
    · omega
    · have hrow : row = order ⟨i.val + 1, hnext⟩ := by
        apply hindexInjective
        change (rows row).index =
          (rows (order ⟨i.val + 1, hnext⟩)).index
        rw [hrowIndex, hkey, hindex]
      rw [← hrow]
      exact hrowValue
  have hend : (rows (order ⟨R - 1, by omega⟩)).output = finish := by
    let last : Fin R := ⟨R - 1, by omega⟩
    have hyield :
        (((rows (order last)).index + 1) % p,
          (rows (order last)).output) ∈ yieldEvents p rows start := by
      simp only [yieldEvents, List.mem_cons]
      exact Or.inr (List.mem_ofFn.mpr ⟨order last, rfl⟩)
    have huse := hbalance.mem_iff.mpr hyield
    have hkey : ((rows (order last)).index + 1) % p = R := by
      rw [hindex last]
      have hlast : last.val + 1 = R := by simp [last]; omega
      rw [hlast, Nat.mod_eq_of_lt hmodulus]
    rcases use_event_is_row_or_end rows finish _ _ huse with
      hterminal | ⟨row, hrowIndex, _⟩
    · simpa only [last] using hterminal.2
    · have hrowLt := raw_index_lt rows order hindex row
      omega
  exact ⟨hstart, hlinks, hend⟩

def iterateStep (step : F → F) : Nat → F → F
  | 0, initial => initial
  | n + 1, initial => step (iterateStep step n initial)

/-- Arbitrary witness-indexed rows, exact value-bearing event balance,
authenticated endpoints, `0 < R < p`, and the local step equation suffice
for the claimed end state. The event permutation is an explicit ideal
premise, not a conclusion of the production LogUp/PCS verifier. -/
theorem exact_events_complete_path {R p : Nat}
    (rows : Fin R → RawRow F) (start finish : F) (step : F → F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : (useEvents rows finish).Perm
      (yieldEvents p rows start))
    (hstep : ∀ row, (rows row).output = step (rows row).input) :
    finish = iterateStep step R start := by
  obtain ⟨order, hindex⟩ := canonical_equiv_of_exact_events
    rows start finish hpositive hmodulus hbalance
  obtain ⟨hstart, hlinks, hend⟩ := raw_value_joins
    rows start finish hpositive hmodulus hbalance order hindex
  have hstate (n : Nat) (hn : n < R) :
      (rows (order ⟨n, hn⟩)).input = iterateStep step n start := by
    induction n with
    | zero => simpa using hstart
    | succ n ih =>
        let previous : Fin R := ⟨n, by omega⟩
        calc
          (rows (order ⟨n + 1, hn⟩)).input =
              (rows (order previous)).output := by
                simpa only [previous] using hlinks previous hn
          _ = step (rows (order previous)).input := hstep (order previous)
          _ = step (iterateStep step n start) := by
                rw [ih (by omega)]
          _ = iterateStep step (n + 1) start := rfl
  let last : Fin R := ⟨R - 1, by omega⟩
  have hlast : (rows (order last)).input =
      iterateStep step (R - 1) start := by
    simpa only [last] using hstate (R - 1) (by omega)
  calc
    finish = (rows (order last)).output := by
      simpa only [last] using hend.symm
    _ = step (rows (order last)).input := hstep (order last)
    _ = step (iterateStep step (R - 1) start) := by rw [hlast]
    _ = iterateStep step (R - 1 + 1) start := rfl
    _ = iterateStep step R start := by
      have hR : R - 1 + 1 = R := by omega
      rw [hR]

/-- Two verifier-fixed call IDs obey the same theorem independently. A
joint seven-coordinate challenge argument must first extract each per-call
exact event permutation from the shared compressed closure. -/
theorem two_call_exact_events_complete_path {R p : Nat}
    (rows : Fin 2 → Fin R → RawRow F)
    (start finish : Fin 2 → F)
    (step : Fin 2 → F → F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hbalance : ∀ call,
      (useEvents (rows call) (finish call)).Perm
        (yieldEvents p (rows call) (start call)))
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call = iterateStep (step call) R (start call) := by
  intro call
  exact exact_events_complete_path (rows call) (start call)
    (finish call) (step call) hpositive hmodulus
    (hbalance call) (hstep call)

abbrev TaggedEvent (F : Type*) := Fin 2 × (Nat × F)

/-- Both calls' full state-event multisets, with verifier-fixed call tags. -/
def jointUseEvents {R : Nat} (rows : Fin 2 → Fin R → RawRow F)
    (finish : Fin 2 → F) : List (TaggedEvent F) :=
  (useEvents (rows 0) (finish 0)).map (fun event => ((0 : Fin 2), event)) ++
    (useEvents (rows 1) (finish 1)).map
      (fun event => ((1 : Fin 2), event))

def jointYieldEvents {R : Nat} (p : Nat)
    (rows : Fin 2 → Fin R → RawRow F)
    (start : Fin 2 → F) : List (TaggedEvent F) :=
  (yieldEvents p (rows 0) (start 0)).map
      (fun event => ((0 : Fin 2), event)) ++
    (yieldEvents p (rows 1) (start 1)).map
      (fun event => ((1 : Fin 2), event))

def selectCall (call : Fin 2) (event : TaggedEvent F) :
    Option (Nat × F) :=
  if event.1 = call then some event.2 else none

/-- Full tuple balance with canonical call tags separates into exact balance
for each chip call. This is an exact-multiset statement; obtaining its premise
from the one random compressed five-component native lookup remains open. -/
theorem per_call_balance_of_joint {R p : Nat}
    (rows : Fin 2 → Fin R → RawRow F)
    (start finish : Fin 2 → F)
    (hjoint : (jointUseEvents rows finish).Perm
      (jointYieldEvents p rows start)) (call : Fin 2) :
    (useEvents (rows call) (finish call)).Perm
      (yieldEvents p (rows call) (start call)) := by
  have hfiltered := hjoint.filterMap (selectCall call)
  fin_cases call <;>
    simpa [jointUseEvents, jointYieldEvents, selectCall] using hfiltered

/-- A single exact multiset of both tagged calls plus local chip steps proves
both endpoint claims. The two tags cannot cancel one another. -/
theorem two_call_joint_exact_events_complete_path {R p : Nat}
    (rows : Fin 2 → Fin R → RawRow F)
    (start finish : Fin 2 → F)
    (step : Fin 2 → F → F)
    (hpositive : 0 < R) (hmodulus : R < p)
    (hjoint : (jointUseEvents rows finish).Perm
      (jointYieldEvents p rows start))
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call = iterateStep (step call) R (start call) := by
  apply two_call_exact_events_complete_path rows start finish step
    hpositive hmodulus
  · intro call
    exact per_call_balance_of_joint rows start finish hjoint call
  · exact hstep

end S31.Gadgets.Air.RawChipIndexCoverage
