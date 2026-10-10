import Mathlib.Tactic

/-!
An ideal, indexed state-event model for the staged two-call private chip.

For each canonical call ID `Fin 2`, there are exactly `R` transition rows,
indexed by `Fin R`. A row consumes its input at state key `(call, index)` and
produces its output at `(call, index + 1)`. The authenticated start produces
key zero, and the authenticated end consumes key `R`. Exact multiset balance
of these **indexed** state events makes every row join its predecessor and
successor. Together with a locally enforced step equation, this rules out a
disconnected cycle or an unused row and determines the end state after `R`
steps. The result is valid for `R = 0` too.

The exact balance premise is deliberately stronger than the production
random-challenge LogUp check. This file does not prove that the native chip
AIR emits these indexed events, that the circuit/chip bridge authenticates the
start and end, or that Fiat–Shamir and PCS soundness establish exact balance.
The usual `R < p` multiplicity condition is needed in that missing reduction;
this pure exact-multiset theorem is valid in every value type and needs no
field characteristic assumption.
-/

namespace S31.Gadgets.Air.IndexedChipPath

variable {F : Type*}

structure Row (F : Type*) where
  input : F
  output : F

abbrev StateKey (R : Nat) := Fin 2 × Fin (R + 1)

/-- The value consumed at each canonical `(call, state index)` key. -/
def useValue {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (finish : Fin 2 → F) (key : StateKey R) : F :=
  if h : key.2.val < R then
    (rows key.1 ⟨key.2.val, h⟩).input
  else
    finish key.1

/-- The value produced at each canonical `(call, state index)` key. -/
def yieldValue {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (start : Fin 2 → F) (key : StateKey R) : F :=
  if h : key.2.val = 0 then
    start key.1
  else
    (rows key.1 ⟨key.2.val - 1, by omega⟩).output

def useEvents {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (finish : Fin 2 → F) : List (StateKey R × F) :=
  (Finset.univ : Finset (StateKey R)).toList.map
    (fun key => (key, useValue rows finish key))

def yieldEvents {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (start : Fin 2 → F) : List (StateKey R × F) :=
  (Finset.univ : Finset (StateKey R)).toList.map
    (fun key => (key, yieldValue rows start key))

/-- Exact balance of one event per canonical key identifies values pointwise.
The call ID and state index are both part of the event, so an event from the
other call or another round cannot cancel it. -/
theorem balance_at_key {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (start finish : Fin 2 → F)
    (hbalance : (useEvents rows finish).Perm (yieldEvents rows start))
    (key : StateKey R) :
    useValue rows finish key = yieldValue rows start key := by
  have huse : (key, useValue rows finish key) ∈ useEvents rows finish := by
    unfold useEvents
    exact List.mem_map.mpr ⟨key, by simp, rfl⟩
  have hyield := hbalance.mem_iff.mp huse
  unfold yieldEvents at hyield
  obtain ⟨other, _, hother⟩ := List.mem_map.mp hyield
  have hkey : other = key := congrArg Prod.fst hother
  subst other
  exact (congrArg Prod.snd hother).symm

private theorem use_row {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (finish : Fin 2 → F) (call : Fin 2) (index : Fin R) :
    useValue rows finish (call, ⟨index.val, by omega⟩) =
      (rows call index).input := by
  have hindex : (⟨index.val, by omega⟩ : Fin R) = index := Fin.ext rfl
  simp [useValue, index.isLt, hindex]

private theorem yield_row {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (start : Fin 2 → F) (call : Fin 2) (index : Fin R) :
    yieldValue rows start (call, ⟨index.val + 1, by omega⟩) =
      (rows call index).output := by
  have hindex : (⟨(index.val + 1) - 1, by omega⟩ : Fin R) = index :=
    Fin.ext (by omega)
  simp [yieldValue, hindex]

private theorem use_finish {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (finish : Fin 2 → F) (call : Fin 2) :
    useValue rows finish (call, ⟨R, by omega⟩) = finish call := by
  simp [useValue]

private theorem yield_start {R : Nat} (rows : Fin 2 → Fin R → Row F)
    (start : Fin 2 → F) (call : Fin 2) :
    yieldValue rows start (call, ⟨0, by omega⟩) = start call := by
  simp [yieldValue]

def iterateStep (step : F → F) : Nat → F → F
  | 0, initial => initial
  | n + 1, initial => step (iterateStep step n initial)

/-- Both calls follow one complete `R`-step path from their authenticated
starts to their authenticated ends. The theorem does not infer the exact
multiset balance or local step equation from the native STARK proof. -/
theorem two_call_complete_path {R : Nat}
    (rows : Fin 2 → Fin R → Row F)
    (start finish : Fin 2 → F) (step : Fin 2 → F → F)
    (hbalance : (useEvents rows finish).Perm (yieldEvents rows start))
    (hstep : ∀ call index,
      (rows call index).output = step call (rows call index).input) :
    ∀ call, finish call = iterateStep (step call) R (start call) := by
  have hpoint := balance_at_key rows start finish hbalance
  have hpath (call : Fin 2) (n : Nat) (hn : n ≤ R) :
      useValue rows finish (call, ⟨n, by omega⟩) =
        iterateStep (step call) n (start call) := by
    induction n generalizing hn with
    | zero =>
        calc
          useValue rows finish (call, ⟨0, by omega⟩) =
              yieldValue rows start (call, ⟨0, by omega⟩) :=
                hpoint (call, ⟨0, by omega⟩)
          _ = start call := yield_start rows start call
          _ = iterateStep (step call) 0 (start call) := rfl
    | succ n ih =>
        have hnlt : n < R := by omega
        let index : Fin R := ⟨n, hnlt⟩
        have hcurrent :
            useValue rows finish (call, ⟨n, by omega⟩) =
              (rows call index).input := by
          simpa only [index] using use_row rows finish call index
        calc
          useValue rows finish (call, ⟨n + 1, by omega⟩) =
              yieldValue rows start (call, ⟨n + 1, by omega⟩) :=
                hpoint (call, ⟨n + 1, by omega⟩)
          _ = (rows call index).output := by
                simpa only [index] using yield_row rows start call index
          _ = step call (rows call index).input := hstep call index
          _ = step call (useValue rows finish (call, ⟨n, by omega⟩)) := by
                rw [hcurrent]
          _ = step call (iterateStep (step call) n (start call)) := by
                rw [ih (by omega)]
          _ = iterateStep (step call) (n + 1) (start call) := rfl
  intro call
  simpa only [use_finish] using hpath call R (le_refl R)

/-- The two canonical calls cannot exchange endpoints: their call tags are
different keys even when all four endpoint values happen to be equal. -/
theorem calls_have_distinct_state_keys {R : Nat} (left right : Fin 2)
    (h : left ≠ right) (a b : Fin (R + 1)) :
    ((left, a) : StateKey R) ≠ ((right, b) : StateKey R) := by
  intro heq
  exact h (congrArg Prod.fst heq)

end S31.Gadgets.Air.IndexedChipPath
