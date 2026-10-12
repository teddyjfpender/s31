import S31.Gadgets.Functional.Correspondence.CanonicalDagOptimization

/-!
Completeness of the independent symbolic audit for the bounded, positional
four-lane add/mul optimizer. The state invariant relates every source wire to
its compact term, including aliases created by common-subexpression
elimination. It also relates each canonical cache key to the instruction term
stored at that key's compact ID. Both operand orders are covered.

The result is about the Lean optimizer model. Native Zig serialization, AIR
emission, and verifier authentication have separate correspondence obligations.
-/

namespace S31.Functional.Correspondence.CanonicalDagOptimization

open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes

private theorem lookup_append_old {α : Type} (xs : List α) (x : α)
    (i : Nat) (a : α) (h : xs[i]? = some a) :
    (xs ++ [x])[i]? = some a := by
  have hi : i < xs.length := (List.getElem?_eq_some_iff.mp h).choose
  simpa [List.getElem?_append_left hi] using h

private theorem lookup_append_new {α : Type} (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]? = some x := by simp

private theorem lookup_append_cases {α : Type} (xs : List α) (x : α)
    (i : Nat) (a : α) (h : (xs ++ [x])[i]? = some a) :
    (i < xs.length ∧ xs[i]? = some a) ∨
      (i = xs.length ∧ a = x) := by
  by_cases hi : i < xs.length
  · left
    exact ⟨hi, by simpa [List.getElem?_append_left hi] using h⟩
  · right
    have hbound : i < xs.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp h).choose
      simpa using this
    have hid : i = xs.length := by omega
    subst i
    simp at h
    exact ⟨rfl, h.symm⟩


private def SourceAgreement (mapping : List Nat)
    (sourceTerms compactTerms : List Term) : Prop :=
  ∀ (i j : Nat), mapping[i]? = some j →
    ∃ source compact, sourceTerms[i]? = some source ∧
      compactTerms[j]? = some compact ∧ equivalent source compact = true

private def KeyRepresentation (keys : List Key) (compactTerms : List Term) : Prop :=
  ∀ (i : Nat) (op : Bool) (lhs rhs : Nat), keys[i]? = some (op, lhs, rhs) →
    ∃ left right, compactTerms[lhs]? = some left ∧
      compactTerms[rhs]? = some right ∧
      compactTerms[i + 1]? = some (instructionTerm op left right)

private theorem agreement_compact_append (mapping : List Nat)
    (sourceTerms compactTerms : List Term) (newTerm : Term)
    (h : SourceAgreement mapping sourceTerms compactTerms) :
    SourceAgreement mapping sourceTerms (compactTerms ++ [newTerm]) := by
  intro i j hmap
  obtain ⟨source, compact, hs, hc, heq⟩ := h i j hmap
  exact ⟨source, compact, hs, lookup_append_old compactTerms newTerm j compact hc, heq⟩

private theorem keys_compact_append (keys : List Key) (compactTerms : List Term)
    (newTerm : Term) (h : KeyRepresentation keys compactTerms) :
    KeyRepresentation keys (compactTerms ++ [newTerm]) := by
  intro i op lhs rhs hkey
  obtain ⟨left, right, hl, hr, hv⟩ := h i op lhs rhs hkey
  exact ⟨left, right,
    lookup_append_old compactTerms newTerm lhs left hl,
    lookup_append_old compactTerms newTerm rhs right hr,
    lookup_append_old compactTerms newTerm (i + 1)
      (instructionTerm op left right) hv⟩

private theorem agreement_empty :
    SourceAgreement [0] [.input] [.input] := by
  intro i j hmap
  have hi : i = 0 := by
    have := (List.getElem?_eq_some_iff.mp hmap).choose
    simp at this
    omega
  subst i
  have hj : j = 0 := by simpa using hmap.symm
  subst j
  exact ⟨.input, .input, rfl, rfl, rfl⟩

private theorem keys_empty : KeyRepresentation [] [.input] := by
  intro i op lhs rhs hkey
  simp at hkey


private theorem agreement_extend (mapping : List Nat)
    (sourceTerms compactTerms : List Term) (newCid : Nat) (newSource : Term)
    (hlen : mapping.length = sourceTerms.length)
    (hOld : SourceAgreement mapping sourceTerms compactTerms)
    (hNew : ∃ compact, compactTerms[newCid]? = some compact ∧
      equivalent newSource compact = true) :
    SourceAgreement (mapping ++ [newCid])
      (sourceTerms ++ [newSource]) compactTerms := by
  intro i j hmap
  rcases lookup_append_cases mapping newCid i j hmap with
    ⟨hi, hprior⟩ | ⟨hi, hj⟩
  · obtain ⟨source, compact, hs, hc, heq⟩ := hOld i j hprior
    have hs' := lookup_append_old sourceTerms newSource i source hs
    exact ⟨source, compact, hs', hc, heq⟩
  · subst i
    subst j
    obtain ⟨compact, hc, heq⟩ := hNew
    exact ⟨newSource, compact,
      by simp [hlen],
      hc, heq⟩

private theorem keys_extend (keys : List Key) (compactTerms : List Term)
    (op : Bool) (lhs rhs : Nat) (left right : Term)
    (hlen : compactTerms.length = keys.length + 1)
    (hrep : KeyRepresentation keys compactTerms)
    (hl : compactTerms[lhs]? = some left)
    (hr : compactTerms[rhs]? = some right) :
    KeyRepresentation (keys ++ [(op, lhs, rhs)])
      (compactTerms ++ [instructionTerm op left right]) := by
  intro i op' lhs' rhs' hkey
  rcases lookup_append_cases keys (op, lhs, rhs) i
    (op', lhs', rhs') hkey with ⟨hi, hprior⟩ | ⟨hi, hsame⟩
  · exact keys_compact_append keys compactTerms
      (instructionTerm op left right) hrep i op' lhs' rhs' hprior
  · subst i
    cases hsame
    exact ⟨left, right,
      lookup_append_old compactTerms (instructionTerm op left right) lhs left hl,
      lookup_append_old compactTerms (instructionTerm op left right) rhs right hr,
      by simp [hlen]⟩

private theorem equivalent_instruction_sorted (multiply : Bool)
    (lhs rhs : Nat) (sourceLeft sourceRight compactLeft compactRight
      orderedLeft orderedRight : Term) (compactTerms : List Term)
    (hleft : compactTerms[lhs]? = some compactLeft)
    (hright : compactTerms[rhs]? = some compactRight)
    (horderedLeft : compactTerms[min lhs rhs]? = some orderedLeft)
    (horderedRight : compactTerms[max lhs rhs]? = some orderedRight)
    (heqLeft : equivalent sourceLeft compactLeft = true)
    (heqRight : equivalent sourceRight compactRight = true) :
    equivalent (instructionTerm multiply sourceLeft sourceRight)
      (instructionTerm multiply orderedLeft orderedRight) = true := by
  by_cases horder : lhs ≤ rhs
  · have hsameLeft : orderedLeft = compactLeft := by
      have h' : compactTerms[lhs]? = some orderedLeft := by
        simpa [Nat.min_eq_left horder] using horderedLeft
      exact Option.some.inj (h'.symm.trans hleft)
    have hsameRight : orderedRight = compactRight := by
      have h' : compactTerms[rhs]? = some orderedRight := by
        simpa [Nat.max_eq_right horder] using horderedRight
      exact Option.some.inj (h'.symm.trans hright)
    subst orderedLeft
    subst orderedRight
    exact equivalent_instruction multiply heqLeft heqRight
  · have hreverse : rhs ≤ lhs := by omega
    have hsameLeft : orderedLeft = compactRight := by
      have h' : compactTerms[rhs]? = some orderedLeft := by
        simpa [Nat.min_eq_right hreverse] using horderedLeft
      exact Option.some.inj (h'.symm.trans hright)
    have hsameRight : orderedRight = compactLeft := by
      have h' : compactTerms[lhs]? = some orderedRight := by
        simpa [Nat.max_eq_left hreverse] using horderedRight
      exact Option.some.inj (h'.symm.trans hleft)
    subst orderedLeft
    subst orderedRight
    exact equivalent_instruction_swap multiply heqLeft heqRight

private theorem sorted_lookup_exists (terms : List Term) (lhs rhs : Nat)
    (left right : Term) (hl : terms[lhs]? = some left)
    (hr : terms[rhs]? = some right) :
    ∃ orderedLeft orderedRight,
      terms[min lhs rhs]? = some orderedLeft ∧
      terms[max lhs rhs]? = some orderedRight := by
  by_cases h : lhs ≤ rhs
  · exact ⟨left, right,
      by simpa [Nat.min_eq_left h] using hl,
      by simpa [Nat.max_eq_right h] using hr⟩
  · have hrev : rhs ≤ lhs := by omega
    exact ⟨right, left,
      by simpa [Nat.min_eq_right hrev] using hr,
      by simpa [Nat.max_eq_left hrev] using hl⟩

private structure Invariant (state : State)
    (sourceTerms compactTerms : List Term) : Prop where
  sourceLength : sourceTerms.length = state.sourceToCanonical.length
  compactLength : compactTerms.length = state.keys.length + 1
  keysMatch : state.keysMatchInstructions
  agreement : SourceAgreement state.sourceToCanonical sourceTerms compactTerms
  keysRepresent : KeyRepresentation state.keys compactTerms

private theorem invariant_initial : Invariant ({} : State) [.input] [.input] := by
  refine ⟨rfl, rfl, rfl, agreement_empty, keys_empty⟩

private theorem invariant_step (state next : State) (raw : Instruction)
    (sourceTerms compactTerms : List Term)
    (hinv : Invariant state sourceTerms compactTerms)
    (hfold : state.instructions.foldlM checkStep [.input] = some compactTerms)
    (hstep : step state raw = some next) :
    ∃ sourceNext compactNext,
      checkStep sourceTerms raw = some sourceNext ∧
      next.instructions.foldlM checkStep [.input] = some compactNext ∧
      Invariant next sourceNext compactNext := by
  have hkeysNext := step_keys_match state next raw hinv.keysMatch hstep
  have hid : raw.id = state.sourceToCanonical.length := by
    by_contra h
    simp [step, h] at hstep
  cases hleft : state.sourceToCanonical[raw.lhs]? with
  | none => simp [step, hid, hleft] at hstep
  | some lhs =>
    cases hright : state.sourceToCanonical[raw.rhs]? with
    | none => simp [step, hid, hleft, hright] at hstep
    | some rhs =>
      obtain ⟨sourceLeft, compactLeft, hsLeft, hcLeft, heqLeft⟩ :=
        hinv.agreement raw.lhs lhs hleft
      obtain ⟨sourceRight, compactRight, hsRight, hcRight, heqRight⟩ :=
        hinv.agreement raw.rhs rhs hright
      let newSource := instructionTerm raw.multiply sourceLeft sourceRight
      have hidSource : raw.id = sourceTerms.length := by
        exact hid.trans hinv.sourceLength.symm
      have hcheckRaw : checkStep sourceTerms raw =
          some (sourceTerms ++ [newSource]) := by
        simp [checkStep, hidSource, hsLeft, hsRight, newSource]
      let key : Key := (raw.multiply, min lhs rhs, max lhs rhs)
      cases hfind : findKey key state.keys with
      | some existing =>
        have hnext : next = {state with sourceToCanonical :=
            state.sourceToCanonical ++ [existing + 1]} := by
          simpa [step, hid, hleft, hright, key, hfind] using hstep.symm
        have hkey : state.keys[existing]? = some key :=
          findKey_sound key state.keys existing hfind
        obtain ⟨orderedLeft, orderedRight, hoLeft, hoRight, hterm⟩ :=
          hinv.keysRepresent existing raw.multiply (min lhs rhs) (max lhs rhs) hkey
        have hsame : equivalent newSource
            (instructionTerm raw.multiply orderedLeft orderedRight) = true :=
          equivalent_instruction_sorted raw.multiply lhs rhs
            sourceLeft sourceRight compactLeft compactRight
            orderedLeft orderedRight compactTerms hcLeft hcRight
            hoLeft hoRight heqLeft heqRight
        have hnew : ∃ compact,
            compactTerms[existing + 1]? = some compact ∧
            equivalent newSource compact = true :=
          ⟨instructionTerm raw.multiply orderedLeft orderedRight, hterm, hsame⟩
        have hagree := agreement_extend state.sourceToCanonical sourceTerms
          compactTerms (existing + 1) newSource
          hinv.sourceLength.symm hinv.agreement hnew
        subst next
        refine ⟨sourceTerms ++ [newSource], compactTerms,
          hcheckRaw, hfold, ?_⟩
        refine ⟨?_, hinv.compactLength, hkeysNext, hagree,
          hinv.keysRepresent⟩
        simp [hinv.sourceLength]
      | none =>
        have hnext : next = {
            instructions := state.instructions ++
              [{ id := state.instructions.length + 1,
                 lhs := min lhs rhs, rhs := max lhs rhs,
                 multiply := raw.multiply }],
            keys := state.keys ++ [key],
            sourceToCanonical := state.sourceToCanonical ++
              [state.instructions.length + 1]} := by
          simpa [step, hid, hleft, hright, key, hfind] using hstep.symm
        obtain ⟨orderedLeft, orderedRight, hoLeft, hoRight⟩ :=
          sorted_lookup_exists compactTerms lhs rhs compactLeft compactRight
            hcLeft hcRight
        let newCompact := instructionTerm raw.multiply orderedLeft orderedRight
        have hsame : equivalent newSource newCompact = true :=
          equivalent_instruction_sorted raw.multiply lhs rhs
            sourceLeft sourceRight compactLeft compactRight
            orderedLeft orderedRight compactTerms hcLeft hcRight
            hoLeft hoRight heqLeft heqRight
        have hkeylen : state.keys.length = state.instructions.length := by
          simpa using congrArg List.length hinv.keysMatch
        have hnewid : state.instructions.length + 1 = compactTerms.length := by
          calc
            state.instructions.length + 1 = state.keys.length + 1 := by omega
            _ = compactTerms.length := hinv.compactLength.symm
        let newInstruction : Instruction :=
          { id := state.instructions.length + 1,
            lhs := min lhs rhs, rhs := max lhs rhs,
            multiply := raw.multiply }
        have hcompactStep : checkStep compactTerms newInstruction =
            some (compactTerms ++ [newCompact]) := by
          simp [checkStep, newInstruction, hnewid, hoLeft, hoRight, newCompact]
        have hfoldNext : (state.instructions ++ [newInstruction]).foldlM
            checkStep [.input] = some (compactTerms ++ [newCompact]) := by
          simp [hfold, hcompactStep]
        have hrep := keys_extend state.keys compactTerms raw.multiply
          (min lhs rhs) (max lhs rhs) orderedLeft orderedRight
          hinv.compactLength hinv.keysRepresent hoLeft hoRight
        have hagreeOld := agreement_compact_append state.sourceToCanonical
          sourceTerms compactTerms newCompact hinv.agreement
        have hcompactNew :
            (compactTerms ++ [newCompact])[state.instructions.length + 1]? =
              some newCompact := by
          simp [hnewid]
        have hagree := agreement_extend state.sourceToCanonical sourceTerms
          (compactTerms ++ [newCompact]) (state.instructions.length + 1)
          newSource hinv.sourceLength.symm hagreeOld
          ⟨newCompact, hcompactNew, hsame⟩
        subst next
        refine ⟨sourceTerms ++ [newSource], compactTerms ++ [newCompact],
          hcheckRaw, ?_, ?_⟩
        · simpa [newInstruction] using hfoldNext
        refine ⟨?_, ?_, hkeysNext, hagree, ?_⟩
        · simp [hinv.sourceLength]
        · simp [hinv.compactLength]
        · simpa [key] using hrep

private theorem invariant_fold (instructions : List Instruction)
    (state : State) (sourceTerms compactTerms : List Term)
    (hinv : Invariant state sourceTerms compactTerms)
    (hvalid : validScheduleFrom state.sourceToCanonical.length instructions)
    (hcompactFold : state.instructions.foldlM checkStep [.input] =
      some compactTerms) :
    ∃ final sourceFinal compactFinal,
      instructions.foldlM step state = some final ∧
      instructions.foldlM checkStep sourceTerms = some sourceFinal ∧
      final.instructions.foldlM checkStep [.input] = some compactFinal ∧
      Invariant final sourceFinal compactFinal := by
  induction instructions generalizing state sourceTerms compactTerms with
  | nil =>
      exact ⟨state, sourceTerms, compactTerms, rfl, rfl,
        hcompactFold, hinv⟩
  | cons raw rest ih =>
      obtain ⟨hid, hlhs, hrhs, hrest⟩ := hvalid
      obtain ⟨middle, hstep⟩ := step_exists state raw hid hlhs hrhs
      obtain ⟨sourceMiddle, compactMiddle, hcheck, hmiddleFold, hmiddleInv⟩ :=
        invariant_step state middle raw sourceTerms compactTerms
          hinv hcompactFold hstep
      have hlength := step_source_length state middle raw hstep
      have hrestValid :
          validScheduleFrom middle.sourceToCanonical.length rest := by
        simpa [hlength] using hrest
      obtain ⟨final, sourceFinal, compactFinal,
        htailOpt, htailSource, htailCompact, hfinalInv⟩ :=
        ih middle sourceMiddle compactMiddle hmiddleInv hrestValid hmiddleFold
      exact ⟨final, sourceFinal, compactFinal,
        by simpa [List.foldlM_cons, hstep] using htailOpt,
        by simpa [List.foldlM_cons, hcheck] using htailSource,
        htailCompact, hfinalInv⟩

/-- Every structurally valid bounded positional add/mul source produced by
`optimize` passes the independent symbolic equivalence audit. -/
theorem audit_complete_of_valid (raw compact : Certificate)
    (hvalid : validCertificate raw)
    (hopt : optimize raw = some compact) :
    audit raw compact = true := by
  obtain ⟨hcount, hsched, _houtput⟩ := hvalid
  obtain ⟨final, sourceFinal, compactFinal,
    hfold, hsourceFold, hcompactFold, hinv⟩ :=
    invariant_fold raw.instructions ({} : State) [.input] [.input]
      invariant_initial hsched rfl
  have hsmall : ¬raw.instructions.length > 16 := by omega
  unfold optimize at hopt
  simp only [hsmall, ↓reduceIte, hfold] at hopt
  cases hout : final.sourceToCanonical[raw.output]? with
  | none => simp [hout] at hopt
  | some cid =>
      have hsame : compact =
          { instructions := final.instructions, output := cid } := by
        simpa [hout] using hopt.symm
      obtain ⟨sourceTerm, compactTerm, hsourceTerm,
        hcompactTerm, heq⟩ := hinv.agreement raw.output cid hout
      subst compact
      have htermRaw : termFor raw = some sourceTerm := by
        simp [termFor, hsourceFold, hsourceTerm]
      have htermCompact :
          termFor { instructions := final.instructions, output := cid } =
            some compactTerm := by
        simp [termFor, hcompactFold, hcompactTerm]
      simpa [audit, htermRaw, htermCompact] using heq

/-- The checked optimizer is total on the structural source fragment: the
symbolic audit never rejects an actually generated canonical DAG. -/
theorem optimizeChecked_exists_of_valid (raw : Certificate)
    (hvalid : validCertificate raw) :
    ∃ compact, optimizeChecked raw = some compact := by
  obtain ⟨compact, hopt⟩ := optimize_exists_of_valid raw hvalid
  have haudit := audit_complete_of_valid raw compact hvalid hopt
  exact ⟨compact, by simp [optimizeChecked, hopt, haudit]⟩

end S31.Functional.Correspondence.CanonicalDagOptimization
