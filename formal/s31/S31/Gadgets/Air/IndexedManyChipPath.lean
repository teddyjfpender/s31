import S31.Gadgets.Air.RawChipIndexCoverage

/-!
Exact tagged-event path reduction for any finite roster of native chip calls.
The joint event permutation is an ideal lookup premise; this module does not
derive it from challenge-compressed LogUp or PCS verifier acceptance.
-/

namespace S31.Gadgets.Air.IndexedManyChipPath

open S31.Gadgets.Air.RawChipIndexCoverage

variable {F : Type*}

/-- The admitted one-to-eight call IDs embed injectively in the M31 step
field. The source-to-roster mapping is a separate verifier obligation. -/
def nativeCallId {N : Nat} (call : Fin N) : ZMod 2147483647 :=
  call.val

theorem nativeCallId_injective {N : Nat} (hN : N ≤ 8) :
    Function.Injective (nativeCallId (N := N)) := by
  intro a b heq
  apply Fin.ext
  have ha : (nativeCallId a).val = a.val := by
    exact ZMod.val_natCast_of_lt (by omega)
  have hb : (nativeCallId b).val = b.val := by
    exact ZMod.val_natCast_of_lt (by omega)
  calc
    a.val = (nativeCallId a).val := ha.symm
    _ = (nativeCallId b).val := congrArg ZMod.val heq
    _ = b.val := hb

def taggedUses {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → RawRow F)
    (finish : Fin N → F) : List (Fin N × (Nat × F)) :=
  (List.finRange N).flatMap fun call =>
    (useEvents (rows call) (finish call)).map (fun event => (call, event))

def taggedYields {N : Nat} {R : Fin N → Nat} (p : Nat)
    (rows : ∀ call, Fin (R call) → RawRow F)
    (start : Fin N → F) : List (Fin N × (Nat × F)) :=
  (List.finRange N).flatMap fun call =>
    (yieldEvents p (rows call) (start call)).map (fun event => (call, event))

private def selectTag {N : Nat} (call : Fin N)
    (event : Fin N × (Nat × F)) : Option (Nat × F) :=
  if event.1 = call then some event.2 else none

private theorem select_map {N : Nat} (tag call : Fin N)
    (events : List (Nat × F)) :
    ((events.map fun event => (tag, event)).filterMap (selectTag call)) =
      if tag = call then events else [] := by
  by_cases h : tag = call
  · simp [selectTag, h]
  · simp [selectTag, h]

private theorem select_flatMap_absent {N : Nat} (xs : List (Fin N))
    (call : Fin N) (f : Fin N → List (Nat × F))
    (hnot : call ∉ xs) :
    (xs.flatMap fun tag =>
      (f tag).map (fun event => (tag, event))).filterMap (selectTag call) =
      [] := by
  induction xs with
  | nil => simp
  | cons tag rest ih =>
    have hneq : tag ≠ call := by
      intro heq
      exact hnot (by simp [heq])
    have hrest : call ∉ rest := by
      intro hmem
      exact hnot (by simp [hmem])
    rw [List.flatMap_cons, List.filterMap_append, select_map,
      if_neg hneq, ih hrest, List.nil_append]

private theorem select_flatMap_list {N : Nat} (xs : List (Fin N))
    (call : Fin N) (f : Fin N → List (Nat × F))
    (hnodup : xs.Nodup) (hmem : call ∈ xs) :
    (xs.flatMap fun tag =>
      (f tag).map (fun event => (tag, event))).filterMap (selectTag call) =
      f call := by
  induction xs with
  | nil => simp at hmem
  | cons tag rest ih =>
    have htail : rest.Nodup := (List.nodup_cons.mp hnodup).2
    by_cases htag : tag = call
    · subst tag
      have hnot : call ∉ rest := (List.nodup_cons.mp hnodup).1
      rw [List.flatMap_cons, List.filterMap_append, select_map,
        if_pos rfl, select_flatMap_absent rest call f hnot,
        List.append_nil]
    · have htailmem : call ∈ rest := by
        rcases List.mem_cons.mp hmem with hhead | hrest
        · exact False.elim (htag hhead.symm)
        · exact hrest
      rw [List.flatMap_cons, List.filterMap_append, select_map,
        if_neg htag, ih htail htailmem, List.nil_append]

private theorem select_flatMap (N : Nat) (call : Fin N)
    (f : Fin N → List (Nat × F)) :
    ((List.finRange N).flatMap fun tag =>
      (f tag).map (fun event => (tag, event))).filterMap (selectTag call) =
      f call := by
  exact select_flatMap_list (List.finRange N) call f
    (List.nodup_finRange N) (List.mem_finRange call)

/-- Distinct verifier-fixed call tags prevent cancellation between calls in
an exact joint multiset, for an arbitrary number of calls and row counts. -/
theorem per_call_balance {N p : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → RawRow F)
    (start finish : Fin N → F)
    (hjoint : (taggedUses rows finish).Perm
      (taggedYields p rows start)) (call : Fin N) :
    (useEvents (rows call) (finish call)).Perm
      (yieldEvents p (rows call) (start call)) := by
  have filtered := hjoint.filterMap (selectTag call)
  simpa only [taggedUses, taggedYields, select_flatMap] using filtered

/-- Per-call exact event balance plus each local transition gives every
endpoint claim, even when calls have different round counts and steps. -/
theorem every_call_complete_path {N p : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → RawRow F)
    (start finish : Fin N → F)
    (step : Fin N → F → F)
    (hpositive : ∀ call, 0 < R call)
    (hmodulus : ∀ call, R call < p)
    (hjoint : (taggedUses rows finish).Perm
      (taggedYields p rows start))
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call = iterateStep (step call) (R call) (start call) := by
  intro call
  exact exact_events_complete_path (rows call) (start call)
    (finish call) (step call) (hpositive call) (hmodulus call)
    (per_call_balance rows start finish hjoint call) (hstep call)

end S31.Gadgets.Air.IndexedManyChipPath
