import S31.Gadgets.Functional.SSACertificate

/-!
Universal acceptance of the deterministic positional SSA emitter. The
induction maintains a checked prefix, fresh next ID, preservation of earlier
wires, and a relation between the emitted output and source elaboration.
-/

namespace S31.Functional.SSAEmitterProof

open S31.Functional.SSACertificate

private def envTerms {n : Nat} (terms : List Term)
    (env : Fin n → Nat) : Fin n → Term :=
  fun i => terms.getD (env i) .input

private theorem getElem?_eq_some_getD {α : Type} (values : List α)
    (default : α) (index : Nat) (h : index < values.length) :
    values[index]? = some (values.getD index default) := by
  have hsome : values[index]? = some values[index] := by simp [h]
  simp [List.getD_eq_getElem?_getD, hsome]

private theorem getD_append_left {α : Type} (values suffix : List α)
    (default : α) (index : Nat) (h : index < values.length) :
    (values ++ suffix).getD index default = values.getD index default := by
  simp only [List.getD_eq_getElem?_getD,
    List.getElem?_append_left h]

private theorem envTerms_append {n : Nat} (terms suffix : List Term)
    (env : Fin n → Nat) (hbound : ∀ i, env i < terms.length) :
    envTerms (terms ++ suffix) env = envTerms terms env := by
  funext i
  exact getD_append_left terms suffix .input (env i) (hbound i)

private theorem bound_append {n : Nat} (terms suffix : List Term)
    (env : Fin n → Nat) (hbound : ∀ i, env i < terms.length) :
    ∀ i, env i < (terms ++ suffix).length := by
  intro i
  simp only [List.length_append]
  have hi := hbound i
  omega

private theorem check_new_step (terms : List Term)
    (id lhs rhs : Nat) (multiply : Bool)
    (hid : id = terms.length)
    (hlhs : lhs < terms.length) (hrhs : rhs < terms.length) :
    checkStep terms { id, lhs, rhs, multiply } =
      some (terms ++ [instructionTerm multiply
        (terms.getD lhs .input) (terms.getD rhs .input)]) := by
  unfold checkStep
  simp only [hid, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  rw [getElem?_eq_some_getD terms .input lhs hlhs,
    getElem?_eq_some_getD terms .input rhs hrhs]
  rfl

private def EmitOK {n : Nat} (source : Source n)
    (env : Fin n → Nat) (prior : List Instruction)
    (terms : List Term) : Prop :=
  let (after, output) := source.emit env prior
  ∃ (suffix : List Instruction) (extra : List Term),
    after = prior ++ suffix ∧
    suffix.foldlM checkStep terms = some (terms ++ extra) ∧
    (terms ++ extra).length = after.length + 1 ∧
    (terms ++ extra)[output]? =
      some (source.elaborate (envTerms terms env))

private theorem emit_ok {n : Nat} (source : Source n)
    (env : Fin n → Nat) (prior : List Instruction)
    (terms : List Term)
    (hlen : terms.length = prior.length + 1)
    (hbound : ∀ i, env i < terms.length) :
    EmitOK source env prior terms := by
  induction source generalizing prior terms with
  | var index =>
      refine ⟨[], [], ?_, ?_, ?_, ?_⟩
      · simp
      · simp
      · simpa using hlen
      · simpa [envTerms] using
          getElem?_eq_some_getD terms .input (env index) (hbound index)
  | add left right ihLeft ihRight =>
      have hleft := ihLeft env prior terms hlen hbound
      simp only [EmitOK] at hleft
      cases hleftRun : left.emit env prior with
      | mk afterLeft leftWire =>
          simp only [hleftRun] at hleft
          obtain ⟨leftSuffix, leftExtra, hleftPrefix, hleftCheck,
            hleftLength, hleftOutput⟩ := hleft
          have hbound1 : ∀ i, env i < (terms ++ leftExtra).length :=
            bound_append terms leftExtra env hbound
          have hright := ihRight env afterLeft (terms ++ leftExtra)
            hleftLength hbound1
          simp only [EmitOK] at hright
          cases hrightRun : right.emit env afterLeft with
          | mk afterRight rightWire =>
              simp only [hrightRun] at hright
              obtain ⟨rightSuffix, rightExtra, hrightPrefix, hrightCheck,
                hrightLength, hrightOutput⟩ := hright
              have henv := envTerms_append terms leftExtra env hbound
              rw [henv] at hrightOutput
              have hleftBound : leftWire < (terms ++ leftExtra).length :=
                (List.getElem?_eq_some_iff.mp hleftOutput).1
              have hleftOutput2 :
                  (terms ++ leftExtra ++ rightExtra)[leftWire]? =
                    some (left.elaborate (envTerms terms env)) := by
                rw [List.getElem?_append_left hleftBound]
                exact hleftOutput
              have hleftBound2 :
                  leftWire < (terms ++ leftExtra ++ rightExtra).length := by
                simp only [List.length_append]
                simp only [List.length_append] at hleftBound
                omega
              have hrightBound :
                  rightWire < (terms ++ leftExtra ++ rightExtra).length :=
                (List.getElem?_eq_some_iff.mp hrightOutput).1
              have hleftGetD :
                  (terms ++ leftExtra ++ rightExtra).getD leftWire .input =
                    left.elaborate (envTerms terms env) := by
                simpa [List.getD_eq_getElem?_getD] using
                  congrArg (fun o : Option Term => o.getD .input) hleftOutput2
              have hrightGetD :
                  (terms ++ leftExtra ++ rightExtra).getD rightWire .input =
                    right.elaborate (envTerms terms env) := by
                simpa [List.getD_eq_getElem?_getD] using
                  congrArg (fun o : Option Term => o.getD .input) hrightOutput
              let newInstruction : Instruction :=
                { id := afterRight.length + 1, lhs := leftWire,
                  rhs := rightWire, multiply := false }
              let newTerm : Term :=
                .add (left.elaborate (envTerms terms env))
                  (right.elaborate (envTerms terms env))
              have hstep :
                  checkStep (terms ++ leftExtra ++ rightExtra) newInstruction =
                    some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                have hid : afterRight.length + 1 =
                    (terms ++ leftExtra ++ rightExtra).length :=
                  hrightLength.symm
                have hraw := check_new_step (terms ++ leftExtra ++ rightExtra)
                    (afterRight.length + 1) leftWire rightWire false
                    hid hleftBound2 hrightBound
                rw [hleftGetD, hrightGetD] at hraw
                simpa [newInstruction, newTerm] using hraw
              unfold EmitOK
              simp only [Source.emit, hleftRun, hrightRun]
              refine ⟨leftSuffix ++ rightSuffix ++ [newInstruction],
                leftExtra ++ rightExtra ++ [newTerm], ?_, ?_, ?_, ?_⟩
              · have hp : afterRight = prior ++ (leftSuffix ++ rightSuffix) := by
                  rw [hrightPrefix, hleftPrefix, List.append_assoc]
                simpa [newInstruction, List.append_assoc] using
                  congrArg (fun p => p ++ [newInstruction]) hp
              · have hfold :
                    (leftSuffix ++ rightSuffix ++ [newInstruction]).foldlM
                      checkStep terms =
                        some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                  calc
                    _ = (rightSuffix ++ [newInstruction]).foldlM
                          checkStep (terms ++ leftExtra) := by
                            simp [List.foldlM_append, hleftCheck]
                    _ = [newInstruction].foldlM checkStep
                          (terms ++ leftExtra ++ rightExtra) := by
                            simp [List.foldlM_append, hrightCheck]
                    _ = some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                          simpa using hstep
                simpa [List.append_assoc] using hfold
              · simp only [List.length_append, List.length_singleton] at *
                omega
              · let finished :=
                    (terms ++ leftExtra ++ rightExtra) ++ [newTerm]
                have hlast :
                    finished[(terms ++ leftExtra ++ rightExtra).length]? =
                      some newTerm := by simp [finished]
                rw [← hrightLength]
                simpa [newInstruction, newTerm, Source.elaborate,
                  List.append_assoc, finished] using hlast
  | mul left right ihLeft ihRight =>
      have hleft := ihLeft env prior terms hlen hbound
      simp only [EmitOK] at hleft
      cases hleftRun : left.emit env prior with
      | mk afterLeft leftWire =>
          simp only [hleftRun] at hleft
          obtain ⟨leftSuffix, leftExtra, hleftPrefix, hleftCheck,
            hleftLength, hleftOutput⟩ := hleft
          have hbound1 : ∀ i, env i < (terms ++ leftExtra).length :=
            bound_append terms leftExtra env hbound
          have hright := ihRight env afterLeft (terms ++ leftExtra)
            hleftLength hbound1
          simp only [EmitOK] at hright
          cases hrightRun : right.emit env afterLeft with
          | mk afterRight rightWire =>
              simp only [hrightRun] at hright
              obtain ⟨rightSuffix, rightExtra, hrightPrefix, hrightCheck,
                hrightLength, hrightOutput⟩ := hright
              have henv := envTerms_append terms leftExtra env hbound
              rw [henv] at hrightOutput
              have hleftBound : leftWire < (terms ++ leftExtra).length :=
                (List.getElem?_eq_some_iff.mp hleftOutput).1
              have hleftOutput2 :
                  (terms ++ leftExtra ++ rightExtra)[leftWire]? =
                    some (left.elaborate (envTerms terms env)) := by
                rw [List.getElem?_append_left hleftBound]
                exact hleftOutput
              have hleftBound2 :
                  leftWire < (terms ++ leftExtra ++ rightExtra).length := by
                simp only [List.length_append]
                simp only [List.length_append] at hleftBound
                omega
              have hrightBound :
                  rightWire < (terms ++ leftExtra ++ rightExtra).length :=
                (List.getElem?_eq_some_iff.mp hrightOutput).1
              have hleftGetD :
                  (terms ++ leftExtra ++ rightExtra).getD leftWire .input =
                    left.elaborate (envTerms terms env) := by
                simpa [List.getD_eq_getElem?_getD] using
                  congrArg (fun o : Option Term => o.getD .input) hleftOutput2
              have hrightGetD :
                  (terms ++ leftExtra ++ rightExtra).getD rightWire .input =
                    right.elaborate (envTerms terms env) := by
                simpa [List.getD_eq_getElem?_getD] using
                  congrArg (fun o : Option Term => o.getD .input) hrightOutput
              let newInstruction : Instruction :=
                { id := afterRight.length + 1, lhs := leftWire,
                  rhs := rightWire, multiply := true }
              let newTerm : Term :=
                .mul (left.elaborate (envTerms terms env))
                  (right.elaborate (envTerms terms env))
              have hstep :
                  checkStep (terms ++ leftExtra ++ rightExtra) newInstruction =
                    some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                have hid : afterRight.length + 1 =
                    (terms ++ leftExtra ++ rightExtra).length :=
                  hrightLength.symm
                have hraw := check_new_step (terms ++ leftExtra ++ rightExtra)
                    (afterRight.length + 1) leftWire rightWire true
                    hid hleftBound2 hrightBound
                rw [hleftGetD, hrightGetD] at hraw
                simpa [newInstruction, newTerm] using hraw
              unfold EmitOK
              simp only [Source.emit, hleftRun, hrightRun]
              refine ⟨leftSuffix ++ rightSuffix ++ [newInstruction],
                leftExtra ++ rightExtra ++ [newTerm], ?_, ?_, ?_, ?_⟩
              · have hp : afterRight = prior ++ (leftSuffix ++ rightSuffix) := by
                  rw [hrightPrefix, hleftPrefix, List.append_assoc]
                simpa [newInstruction, List.append_assoc] using
                  congrArg (fun p => p ++ [newInstruction]) hp
              · have hfold :
                    (leftSuffix ++ rightSuffix ++ [newInstruction]).foldlM
                      checkStep terms =
                        some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                  calc
                    _ = (rightSuffix ++ [newInstruction]).foldlM
                          checkStep (terms ++ leftExtra) := by
                            simp [List.foldlM_append, hleftCheck]
                    _ = [newInstruction].foldlM checkStep
                          (terms ++ leftExtra ++ rightExtra) := by
                            simp [List.foldlM_append, hrightCheck]
                    _ = some ((terms ++ leftExtra ++ rightExtra) ++ [newTerm]) := by
                          simpa using hstep
                simpa [List.append_assoc] using hfold
              · simp only [List.length_append, List.length_singleton] at *
                omega
              · let finished :=
                    (terms ++ leftExtra ++ rightExtra) ++ [newTerm]
                have hlast :
                    finished[(terms ++ leftExtra ++ rightExtra).length]? =
                      some newTerm := by simp [finished]
                rw [← hrightLength]
                simpa [newInstruction, newTerm, Source.elaborate,
                  List.append_assoc, finished] using hlast
  | letValue value body ihValue ihBody =>
      rename_i m
      have hvalue := ihValue env prior terms hlen hbound
      simp only [EmitOK] at hvalue
      cases hvalueRun : value.emit env prior with
      | mk afterValue valueWire =>
          simp only [hvalueRun] at hvalue
          obtain ⟨valueSuffix, valueExtra, hvaluePrefix, hvalueCheck,
            hvalueLength, hvalueOutput⟩ := hvalue
          have hvalueBound : valueWire < (terms ++ valueExtra).length :=
            (List.getElem?_eq_some_iff.mp hvalueOutput).1
          have hboundBody :
              ∀ i : Fin (m + 1),
                ((Fin.cons valueWire env : Fin (m + 1) → Nat) i) <
                (terms ++ valueExtra).length := by
            intro i
            refine Fin.cases ?_ ?_ i
            · exact hvalueBound
            · intro j
              exact (bound_append terms valueExtra env hbound) j
          have hbody := ihBody (Fin.cons valueWire env) afterValue
            (terms ++ valueExtra) hvalueLength hboundBody
          simp only [EmitOK] at hbody
          cases hbodyRun : body.emit (Fin.cons valueWire env) afterValue with
          | mk afterBody bodyWire =>
              simp only [hbodyRun] at hbody
              obtain ⟨bodySuffix, bodyExtra, hbodyPrefix, hbodyCheck,
                hbodyLength, hbodyOutput⟩ := hbody
              have henvBody :
                  envTerms (terms ++ valueExtra) (Fin.cons valueWire env) =
                    Fin.cons (value.elaborate (envTerms terms env))
                      (envTerms terms env) := by
                funext i
                refine Fin.cases ?_ ?_ i
                · simpa [envTerms, List.getD_eq_getElem?_getD,
                    hvalueOutput] using
                    congrArg (fun o : Option Term => o.getD .input)
                      hvalueOutput
                · intro j
                  exact getD_append_left terms valueExtra .input
                    (env j) (hbound j)
              rw [henvBody] at hbodyOutput
              unfold EmitOK
              simp only [Source.emit, hvalueRun, hbodyRun]
              refine ⟨valueSuffix ++ bodySuffix,
                valueExtra ++ bodyExtra, ?_, ?_, ?_, ?_⟩
              · rw [hbodyPrefix, hvaluePrefix]
                simp [List.append_assoc]
              · have hfold :
                    (valueSuffix ++ bodySuffix).foldlM checkStep terms =
                      some (terms ++ valueExtra ++ bodyExtra) := by
                  simp [List.foldlM_append, hvalueCheck, hbodyCheck]
                simpa [List.append_assoc] using hfold
              · simpa [List.append_assoc] using hbodyLength
              · simpa [Source.elaborate, List.append_assoc] using
                  hbodyOutput

/-- Every source term in this total four-lane add/mul/let fragment has an
accepted emitted SSA certificate. Together with the checker soundness theorem,
this closes local compiler completeness and soundness for the positional IR. -/
theorem compile_checked (source : Source 1) :
    check source (compile source) = some () := by
  have hbound : ∀ i : Fin 1, (fun _ : Fin 1 => (0 : Nat)) i <
      ([Term.input] : List Term).length := by
    intro i
    fin_cases i
    decide
  have h := emit_ok source (fun _ : Fin 1 => 0) [] [Term.input]
    (by decide) hbound
  unfold EmitOK at h
  cases hrun : source.emit (fun _ : Fin 1 => 0) [] with
  | mk instructions output =>
      simp only [hrun] at h
      obtain ⟨suffix, extra, hprefix, hcheck, _, houtput⟩ := h
      have hinstructions : instructions = suffix := by
        simpa using hprefix
      have henv : envTerms [Term.input] (fun _ : Fin 1 => 0) =
          (fun _ : Fin 1 => Term.input) := by
        funext i
        fin_cases i
        rfl
      rw [henv] at houtput
      simp only [List.singleton_append] at houtput
      simp [check, compile, hrun, hinstructions, hcheck,
        houtput]

/-- The deterministic positional emitter is accepted for every supported
source program, including arbitrary nested and shared `let` expressions. -/
theorem compiled_normalized_sound (source : Source 1) (input : Lanes) :
    executeNormalized (compile source) input =
      some (source.value (fun _ => input)) :=
  checked_certificate_normalized_sound source (compile source) input
    (compile_checked source)

end S31.Functional.SSAEmitterProof
