import S31.Gadgets.Air.IndexedManyChipPath
import S31.Gadgets.Air.TaggedPairEventDecode

/-!
Seven-coordinate native-shaped events for any finite roster of one to eight
chip calls. This module connects exact tuple balance to the previously proved
arbitrary-row path theorem. Exact balance, native AIR acceptance, and the
fixed source-to-manifest roster are separate obligations; PCS/FRI verifier
acceptance is not inferred here.
-/

namespace S31.Gadgets.Air.IndexedManyTaggedTupleBridge

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.RawChipIndexCoverage
open S31.Gadgets.Air.IndexedManyChipPath
open S31.Gadgets.Air.TaggedPairChallenge
open S31.Gadgets.Air.TaggedPairSourceComposition
open S31.Gadgets.Air.TaggedPairEventProjection
open S31.Gadgets.Air.TaggedPairEventDecode

abbrev State := Fin 4 → F

/-- The native step is an M31 word; its canonical natural value is used by
the index-coverage theorem. No witness-supplied range assertion is needed. -/
structure NativeRow where
  step : F
  input : State
  output : State

def rawRow (row : NativeRow) : RawRow State :=
  ⟨row.step.val, row.input, row.output⟩

def nativeTuple {N : Nat} (call : Fin N) (step : F)
    (state : State) : JointTuple :=
  chipTuple7 (nativeCallId call) step state

/-- The bridge's terminal field step is the natural round count exactly
when that verifier-fixed count is below the M31 modulus. -/
theorem round_tag_canonical (rounds : Nat)
    (hrounds : rounds < 2147483647) :
    ((rounds : F)).val = rounds :=
  ZMod.val_natCast_of_lt hrounds

/-- Native M31 addition implements the modulo-index successor used by the
arbitrary-row path theorem. -/
theorem successor_step_canonical (step : F) :
    (step + 1).val = (step.val + 1) % 2147483647 := by
  congr 1

/-- The relation, call, step, and four lane words identify one native event.
Call tags are injective for the admitted roster size. -/
theorem nativeTuple_injective {N : Nat} (hN : N ≤ 8)
    {call₁ call₂ : Fin N} {step₁ step₂ : F}
    {state₁ state₂ : State}
    (heq : nativeTuple call₁ step₁ state₁ =
      nativeTuple call₂ step₂ state₂) :
    call₁ = call₂ ∧ step₁ = step₂ ∧ state₁ = state₂ := by
  obtain ⟨hcall, hstep, hstate⟩ :=
    chipTuple7_injective _ _ _ _ _ _ heq
  exact ⟨nativeCallId_injective hN hcall, hstep, hstate⟩

def callUses {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) (call : Fin N) : List JointTuple :=
  nativeTuple call (R call) (finish call) ::
    List.ofFn (fun row =>
      nativeTuple call (rows call row).step (rows call row).input)

def callYields {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) (call : Fin N) : List JointTuple :=
  nativeTuple call 0 (start call) ::
    List.ofFn (fun row =>
      nativeTuple call ((rows call row).step + 1)
        (rows call row).output)

def jointUses {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) : List JointTuple :=
  (List.finRange N).flatMap (callUses rows finish)

def jointYields {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) : List JointTuple :=
  (List.finRange N).flatMap (callYields rows start)

private theorem nativeTuple_own_call {N : Nat}
    (call : Fin N) (step : F) (state : State) :
    IsChipCallEvent (nativeCallId call)
      (nativeTuple call step state) := ⟨rfl, rfl⟩

private theorem callUses_own_call {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) (call : Fin N) :
    ∀ event ∈ callUses rows finish call,
      IsChipCallEvent (nativeCallId call) event := by
  intro event hmem
  simp only [callUses, List.mem_cons, List.mem_ofFn] at hmem
  rcases hmem with rfl | ⟨row, rfl⟩
  · exact nativeTuple_own_call _ _ _
  · exact nativeTuple_own_call _ _ _

private theorem callYields_own_call {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) (call : Fin N) :
    ∀ event ∈ callYields rows start call,
      IsChipCallEvent (nativeCallId call) event := by
  intro event hmem
  simp only [callYields, List.mem_cons, List.mem_ofFn] at hmem
  rcases hmem with rfl | ⟨row, rfl⟩
  · exact nativeTuple_own_call _ _ _
  · exact nativeTuple_own_call _ _ _

private theorem select_absent {N : Nat} (hN : N ≤ 8)
    (xs : List (Fin N)) (call : Fin N)
    (events : Fin N → List JointTuple)
    (htags : ∀ tag event, event ∈ events tag →
      IsChipCallEvent (nativeCallId tag) event)
    (hnot : call ∉ xs) :
    callTaggedEvents (nativeCallId call)
      (xs.flatMap events) = [] := by
  induction xs with
  | nil => simp [callTaggedEvents]
  | cons tag rest ih =>
    have hne : nativeCallId call ≠ nativeCallId tag := by
      intro heq
      exact hnot (by simp [nativeCallId_injective hN heq])
    have hrest : call ∉ rest := by
      intro hmem
      exact hnot (by simp [hmem])
    rw [List.flatMap_cons, callTaggedEvents_append,
      callTaggedEvents_other_call _ _ hne _ (htags tag),
      ih hrest, List.nil_append]

private theorem select_finRange {N : Nat} (hN : N ≤ 8)
    (call : Fin N) (events : Fin N → List JointTuple)
    (htags : ∀ tag event, event ∈ events tag →
      IsChipCallEvent (nativeCallId tag) event) :
    callTaggedEvents (nativeCallId call)
      ((List.finRange N).flatMap events) = events call := by
  have select_list (xs : List (Fin N))
      (hnodup : xs.Nodup) (hmem : call ∈ xs) :
      callTaggedEvents (nativeCallId call) (xs.flatMap events) =
        events call := by
    induction xs with
    | nil => simp at hmem
    | cons tag rest ih =>
      have htail := (List.nodup_cons.mp hnodup).2
      by_cases htag : tag = call
      · subst tag
        have hnot := (List.nodup_cons.mp hnodup).1
        rw [List.flatMap_cons, callTaggedEvents_append,
          callTaggedEvents_own_call _ _ (htags call),
          select_absent hN rest call events htags hnot,
          List.append_nil]
      · have hne : nativeCallId call ≠ nativeCallId tag := by
          intro heq
          exact htag (nativeCallId_injective hN heq).symm
        have htailmem : call ∈ rest := by
          rcases List.mem_cons.mp hmem with hhead | hrest
          · exact False.elim (htag hhead.symm)
          · exact hrest
        rw [List.flatMap_cons, callTaggedEvents_append,
          callTaggedEvents_other_call _ _ hne _ (htags tag),
          ih htail htailmem, List.nil_append]
  exact select_list (List.finRange N)
    (List.nodup_finRange N) (List.mem_finRange call)

theorem selected_call_uses {N : Nat} {R : Fin N → Nat}
    (hN : N ≤ 8) (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) (call : Fin N) :
    callTaggedEvents (nativeCallId call) (jointUses rows finish) =
      callUses rows finish call := by
  exact select_finRange hN call (callUses rows finish)
    (fun tag => callUses_own_call rows finish tag)

theorem selected_call_yields {N : Nat} {R : Fin N → Nat}
    (hN : N ≤ 8) (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) (call : Fin N) :
    callTaggedEvents (nativeCallId call) (jointYields rows start) =
      callYields rows start call := by
  exact select_finRange hN call (callYields rows start)
    (fun tag => callYields_own_call rows start tag)

private theorem jointUses_chip_only {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) :
    ∀ event ∈ jointUses rows finish, IsChipEvent event := by
  intro event hmem
  obtain ⟨call, _, hevent⟩ := List.mem_flatMap.mp hmem
  exact (callUses_own_call rows finish call event hevent).1

private theorem jointYields_chip_only {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) :
    ∀ event ∈ jointYields rows start, IsChipEvent event := by
  intro event hmem
  obtain ⟨call, _, hevent⟩ := List.mem_flatMap.mp hmem
  exact (callYields_own_call rows start call event hevent).1

/-- Gate-only circuit events cannot cancel any native chip event: the fixed
relation tags project the exact joint seven-word multiset to chip balance. -/
theorem chip_balance_of_gate_prefixed_joint {N : Nat}
    {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (gateYields gateUses : List JointTuple)
    (hgateYields : ∀ event ∈ gateYields, IsGateEvent event)
    (hgateUses : ∀ event ∈ gateUses, IsGateEvent event)
    (hjoint : (gateYields ++ jointUses rows finish).Perm
      (gateUses ++ jointYields rows start)) :
    (jointUses rows finish).Perm (jointYields rows start) := by
  have hprojected := chip_balance_of_joint_gate_prefixes
    gateYields gateUses (jointUses rows finish)
    (jointYields rows start) hgateYields hgateUses hjoint
  simpa only [chipTaggedEvents_chip_only
    (jointUses rows finish) (jointUses_chip_only rows finish),
    chipTaggedEvents_chip_only
      (jointYields rows start) (jointYields_chip_only rows start)]
    using hprojected

theorem decode_call_uses {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (finish : Fin N → State) (call : Fin N)
    (hR : R call < 2147483647) :
    (callUses rows finish call).map decodeChipEvent =
      useEvents (fun row => rawRow (rows call row)) (finish call) := by
  simp [callUses, useEvents, nativeTuple, rawRow,
    decode_chipTuple7, round_tag_canonical _ hR]
  funext row
  exact decode_chipTuple7 _ _ _

theorem decode_call_yields {N : Nat} {R : Fin N → Nat}
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start : Fin N → State) (call : Fin N) :
    (callYields rows start call).map decodeChipEvent =
      yieldEvents 2147483647
        (fun row => rawRow (rows call row)) (start call) := by
  simp [callYields, yieldEvents, nativeTuple, rawRow,
    decode_chipTuple7]
  funext row
  simp only [Function.comp_apply, decode_chipTuple7]
  congr 1

/-- Exact balance of seven native-shaped coordinates projects to every
call's natural-indexed event balance, without assuming row ordering. -/
theorem every_call_raw_balance {N : Nat} {R : Fin N → Nat}
    (hN : N ≤ 8) (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (hR : ∀ call, R call < 2147483647)
    (hjoint : (jointUses rows finish).Perm (jointYields rows start)) :
    ∀ call, (useEvents (fun row => rawRow (rows call row))
      (finish call)).Perm
      (yieldEvents 2147483647
        (fun row => rawRow (rows call row)) (start call)) := by
  intro call
  have hselected := callTaggedEvents_perm (nativeCallId call) hjoint
  rw [selected_call_uses hN rows finish call,
    selected_call_yields hN rows start call] at hselected
  have hdecoded := hselected.map decodeChipEvent
  simpa only [decode_call_uses rows finish call (hR call),
    decode_call_yields rows start call] using hdecoded

/-- The native seven-coordinate permutation supplies precisely the abstract
tagged-event premise of `IndexedManyChipPath`, for the same fixed roster. -/
theorem abstract_joint_balance {N : Nat} {R : Fin N → Nat}
    (hN : N ≤ 8) (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (hR : ∀ call, R call < 2147483647)
    (hjoint : (jointUses rows finish).Perm (jointYields rows start)) :
    (taggedUses (fun call row => rawRow (rows call row)) finish).Perm
      (taggedYields 2147483647
        (fun call row => rawRow (rows call row)) start) := by
  unfold taggedUses taggedYields
  apply List.Perm.flatMap_left
  intro call _
  exact (every_call_raw_balance hN rows start finish hR hjoint call).map
    (fun event => (call, event))

/-- The exact tuple multiset and accepted local transition equation imply
all endpoint claims. AIR enforcement of the transition and authentication of
the multiset remain external premises. -/
theorem every_call_complete_path_of_joint {N : Nat}
    {R : Fin N → Nat} (hN : N ≤ 8)
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (step : Fin N → State → State)
    (hpositive : ∀ call, 0 < R call)
    (hR : ∀ call, R call < 2147483647)
    (hjoint : (jointUses rows finish).Perm (jointYields rows start))
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call =
      iterateStep (step call) (R call) (start call) := by
  exact every_call_complete_path
    (fun call row => rawRow (rows call row)) start finish step
    hpositive hR
    (abstract_joint_balance hN rows start finish hR hjoint)
    hstep

/-- End-to-end algebraic reduction from an exact, Gate-prefixed native-shaped
joint tuple balance. This does not discharge native AIR/PCS acceptance or
source-to-manifest correspondence premises. -/
theorem every_call_complete_path_of_gate_prefixed_joint {N : Nat}
    {R : Fin N → Nat} (hN : N ≤ 8)
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (step : Fin N → State → State)
    (gateYields gateUses : List JointTuple)
    (hgateYields : ∀ event ∈ gateYields, IsGateEvent event)
    (hgateUses : ∀ event ∈ gateUses, IsGateEvent event)
    (hpositive : ∀ call, 0 < R call)
    (hR : ∀ call, R call < 2147483647)
    (hjoint : (gateYields ++ jointUses rows finish).Perm
      (gateUses ++ jointYields rows start))
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call =
      iterateStep (step call) (R call) (start call) := by
  exact every_call_complete_path_of_joint hN rows start finish step
    hpositive hR
    (chip_balance_of_gate_prefixed_joint rows start finish
      gateYields gateUses hgateYields hgateUses hjoint)
    hstep

/-- Algebraic challenge reduction for an arbitrary admitted call roster.
The reciprocal equation and good challenge are explicit; no theorem here
derives either from an accepted native proof or its Fiat–Shamir transcript. -/
theorem every_call_complete_path_of_good_challenge {N : Nat}
    {R : Fin N → Nat} (hN : N ≤ 8)
    (rows : ∀ call, Fin (R call) → NativeRow)
    (start finish : Fin N → State)
    (step : Fin N → State → State)
    (gateYields gateUses : List JointTuple)
    (hgateYields : ∀ event ∈ gateYields, IsGateEvent event)
    (hgateUses : ∀ event ∈ gateUses, IsGateEvent event)
    (hpositive : ∀ call, 0 < R call)
    (hR : ∀ call, R call < 2147483647)
    (alpha z : GateSecure)
    (hgood : (alpha, z) ∉ badPairs7
      (gateYields ++ jointUses rows finish)
      (gateUses ++ jointYields rows start))
    (hclosed : productionReciprocalSum7
      (gateYields ++ jointUses rows finish) alpha z =
      productionReciprocalSum7
        (gateUses ++ jointYields rows start) alpha z)
    (hstep : ∀ call row,
      (rows call row).output = step call (rows call row).input) :
    ∀ call, finish call =
      iterateStep (step call) (R call) (start call) := by
  exact every_call_complete_path_of_gate_prefixed_joint hN rows
    start finish step gateYields gateUses hgateYields hgateUses
    hpositive hR
    (exact_joint_events_outside_badPairs7 _ _ alpha z hgood hclosed)
    hstep

end S31.Gadgets.Air.IndexedManyTaggedTupleBridge
