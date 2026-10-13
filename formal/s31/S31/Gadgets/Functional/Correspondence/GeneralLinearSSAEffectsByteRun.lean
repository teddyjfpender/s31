import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAEffectsInputState
import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAByteRun

/-!
Exact-byte effectful source/certificate/relation/ABI admission, followed by
the real normalized interpreter. The theorem quantifies over arbitrary M31
input lanes and does not compare source and interpreter final values in the
checker. Native gate-row ownership is a separate proof obligation.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAEffectsByteRun

open S31.Functional.Correspondence
open GeneralLinearSSAProgramEvaluate
open GeneralLinearSSAEffectsEvaluator
open GeneralLinearSSAPublicABI

abbrev Check := Except String

def checkEffectsAlignment (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (certificate : GeneralLinearSSAEffects.Certificate) : Bool :=
  decide (expectedEffectsNodes ssa = some
      (certificate.steps.map (namedEffectNode ssa.names)) ∧
    expectedEffectsAssertions ssa = some
      (namedAssertions ssa.names certificate.assertions) ∧
    ssa.names.Nodup ∧ certificate.inputs = ssa.inputs.length ∧
    certificate.steps.length = ssa.nodes.length ∧
    certificate.output = ssa.output)

theorem checked_effects_alignment (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (h : checkEffectsAlignment ssa certificate = true) :
    expectedEffectsNodes ssa = some
      (certificate.steps.map (namedEffectNode ssa.names)) ∧
    expectedEffectsAssertions ssa = some
      (namedAssertions ssa.names certificate.assertions) ∧
    ssa.names.Nodup ∧ certificate.inputs = ssa.inputs.length ∧
    certificate.steps.length = ssa.nodes.length ∧
    certificate.output = ssa.output := by
  exact of_decide_eq_true (by simpa [checkEffectsAlignment] using h)

private theorem distinct_of_nodup (names : List String) (maximum : Nat)
    (hmax : maximum ≤ names.length) (hnames : names.Nodup) :
    Distinct names maximum := by
  intro i j hi hj heq
  have hi' : i < names.length := by omega
  have hj' : j < names.length := by omega
  have hnamesEq : names[i] = names[j] := by
    simpa only [nameAt, List.getD_eq_getElem names "" hi',
      List.getD_eq_getElem names "" hj'] using heq
  exact (List.Nodup.getElem_inj_iff hnames).mp hnamesEq

/-- Given exact source/certificate and relation bytes, finite alignment and
typed input-state checks plus successful evaluation force the effectful
source's output and assertions. The executable admission below supplies all
of these premises. -/
theorem checked_effects_source_program_evaluate {n : Nat}
    (sourceBytes : List Nat) (certificateBytes relationBytes : String)
    (ssa : GeneralLinearSSAEffects.EmittedSSA)
    (meaning : GeneralLinearSSAEffects.Source)
    (certificate : GeneralLinearSSAEffects.Certificate)
    (program : S31.Program) (assignment : S31.Assignment)
    (inputEnv : S31.Env) (values : Nat → Lanes n)
    (words : List S31.M31)
    (hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes = .ok (ssa, meaning, certificate))
    (hrelation : checkEffectsSourceRelationSSA sourceBytes relationBytes ssa =
      .ok program)
    (halign : checkEffectsAlignment ssa certificate = true)
    (hstate : GeneralLinearSSAEffectsInputState.checkInputState program
      assignment ssa.names certificate values = some inputEnv)
    (haccept : program.evaluate assignment = .ok words) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes values
      (meaning.output.eval values) ∧
    ∃ outputName,
      ssa.names[ssa.output]? = some outputName ∧
      S31.assigned assignment.publicOutputs outputName ⟨.m31, n⟩ =
        .ok (laneValue (meaning.output.eval values)) := by
  obtain ⟨hparse, _, hmeaning, hssa⟩ :=
    GeneralLinearSSAEffectsSourceBytes.checked_source_parts
      sourceBytes certificateBytes ssa meaning certificate hsource
  have hcertificate : GeneralLinearSSAEffects.check certificate meaning =
      some () :=
    (GeneralLinearSSAEffects.checked_emitted_certificate ssa meaning
      certificate hssa).2
  obtain ⟨halignNodes, halignAssertions, hnodup, hinputCount,
    hstepCount, houtputId⟩ := checked_effects_alignment ssa certificate halign
  obtain ⟨hprivate, hinputs, hcarries, habent⟩ :=
    GeneralLinearSSAEffectsInputState.checked_input_state program assignment
      ssa.names certificate values inputEnv hstate
  have hmaximum :
      (GeneralLinearSSAEffects.initialValues certificate.inputs values).length +
        certificate.steps.length = ssa.names.length := by
    simp [GeneralLinearSSAEffects.initialValues,
      GeneralLinearSSAEffects.EmittedSSA.names, hinputCount, hstepCount]
  have hdistinct : Distinct ssa.names
      ((GeneralLinearSSAEffects.initialValues certificate.inputs values).length +
        certificate.steps.length) :=
    distinct_of_nodup ssa.names _ (by omega) hnodup
  have hrelationBase : checkEffectsRelationSSA relationBytes ssa =
      .ok program :=
    (checked_relation_name
      (GeneralLinearSSAEffectsSourceBytes.parseSourceName sourceBytes)
      (checkEffectsRelationSSA relationBytes ssa) program hrelation).2
  obtain ⟨hbase, hnodes, hassertions, _⟩ :=
    checked_effects_relation_graph relationBytes ssa program hrelationBase
  obtain ⟨outputName, hname, _, hmatch⟩ :=
    checked_relation_ssa relationBytes ssa.lane_count ssa.inputs
      ssa.names ssa.output program hbase
  have hlayout : checkRelationLayout relationBytes ssa.lane_count
      ssa.inputs outputName = .ok program := by
    simpa [checkRelationSSA, hname] using hbase
  obtain ⟨_, _, hvalid⟩ :=
    checked_relation_layout relationBytes ssa.lane_count ssa.inputs
      outputName program hlayout
  have hgraph : program.nodes =
      certificate.steps.map (namedEffectNode ssa.names) :=
    Option.some.inj (hnodes.symm.trans halignNodes)
  have hassertGraph : program.assertions =
      namedAssertions ssa.names certificate.assertions :=
    Option.some.inj (hassertions.symm.trans halignAssertions)
  have hselected : program.outputs =
      [nameAt ssa.names certificate.output] := by
    rw [houtputId]
    simpa [nameAt, hname] using hmatch.2.2.2
  have hsem := GeneralLinearSSAEffects.checked_execution certificate
    meaning values hcertificate
  have hfinal : ∃ final : List (Lanes n),
      GeneralLinearSSAEffects.AcceptsTrace
        (GeneralLinearSSAEffects.initialValues certificate.inputs values)
        certificate.steps final := by
    unfold GeneralLinearSSAEffects.execute at hsem
    cases hfold : certificate.steps.foldlM GeneralLinearSSAEffects.executeStep
        (GeneralLinearSSAEffects.initialValues certificate.inputs values) with
    | none => simp [hfold] at hsem
    | some final =>
        exact ⟨final, GeneralLinearSSAEffects.executing_trace_has_air_rows
          certificate.steps _ final hfold⟩
  obtain ⟨final, hrows⟩ := hfinal
  have hclaim := effectful_interpreter_public_output_claim
    program assignment ssa.names certificate meaning values inputEnv
    final words hcertificate hvalid hprivate hinputs hgraph hassertGraph
    hselected hrows hcarries habent hdistinct haccept
  have hsourceAccept := effectful_interpreter_preserves_source_assertions
    program assignment ssa.names certificate meaning values inputEnv
    final words hcertificate hvalid hprivate hinputs hgraph hassertGraph
    hrows hcarries habent hdistinct haccept
  refine ⟨⟨ssa, meaning, hparse, hmeaning, hsourceAccept⟩,
    outputName, hname, ?_⟩
  have hsame : outputName = nameAt ssa.names certificate.output := by
    rw [houtputId]
    simpa [nameAt, hname]
  rw [hsame]
  exact hclaim

structure EffectsByteRun where
  ssa : GeneralLinearSSAEffects.EmittedSSA
  meaning : GeneralLinearSSAEffects.Source
  certificate : GeneralLinearSSAEffects.Certificate
  program : S31.Program
  assignment : S31.Assignment
  inputEnv : S31.Env
  words : List S31.M31

/-- Exact-byte effectful admission includes the actual assertion-checking
interpreter. It does not directly compare independently computed final values. -/
def checkEffectsByteRun {n : Nat} (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (values : Nat → Lanes n)
    (claimed : Lanes n) : Check EffectsByteRun := do
  let (ssa, meaning, certificate) ←
    GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate sourceBytes
      certificateBytes
  let program ← checkEffectsSourceRelationSSA sourceBytes relationBytes ssa
  if !checkEffectsAlignment ssa certificate then
    throw "effects SSA alignment differs"
  let outputName ← match ssa.names[ssa.output]? with
    | none => throw "selected output name missing"
    | some name => pure name
  checkBoundary abiBytes assignmentBytes rawPublicBytes ssa.lane_count
    ssa.inputs outputName values claimed
  let assignment ← GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes
  let inputEnv ← match GeneralLinearSSAEffectsInputState.checkInputState
      program assignment ssa.names certificate values with
    | none => throw "typed assignment differs from effectful initial SSA state"
    | some env => pure env
  if S31.assigned assignment.publicOutputs outputName ⟨.m31, n⟩ !=
      .ok (laneValue claimed) then
    throw "typed public output differs from ABI claim"
  let words ← match program.evaluate assignment with
    | .error _ => throw "normalized interpreter rejected assignment"
    | .ok words => pure words
  if words != orderedPublicWords ssa.inputs values claimed then
    throw "normalized public words differ from ABI words"
  return ⟨ssa, meaning, certificate, program, assignment, inputEnv, words⟩

private theorem laneValue_injective {n : Nat} :
    Function.Injective (laneValue (n := n)) := by
  intro left right h
  exact List.ofFn_inj.mp (congrArg S31.Value.words h)

/-- Successful exact-byte effectful admission proves the claimed value and
every source assertion, with the ABI bytes bound to the same assignment.
The assertion conclusion follows from `Program.evaluate` acceptance; it is
not an independent input or a direct source-output comparison. -/
theorem checked_effects_byte_run {n : Nat} (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (values : Nat → Lanes n)
    (claimed : Lanes n) (run : EffectsByteRun)
    (hcheck : checkEffectsByteRun sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes rawPublicBytes values claimed = .ok run) :
    GeneralLinearSSAEffectsSourceBytes.denotation sourceBytes values claimed ∧
    rawPublicBytes = publicWordBytes
      (orderedPublicWords run.ssa.inputs values claimed) ∧
    GeneralLinearSSAByteRun.parseTypedAssignment assignmentBytes =
      .ok run.assignment ∧
    run.program.evaluate run.assignment = .ok run.words := by
  unfold checkEffectsByteRun at hcheck
  cases hsource : GeneralLinearSSAEffectsSourceBytes.checkSourceCertificate
      sourceBytes certificateBytes with
  | error err => simp [hsource, Bind.bind, Except.bind] at hcheck
  | ok triple =>
      obtain ⟨ssa, meaning, certificate⟩ := triple
      cases hrelation : checkEffectsSourceRelationSSA sourceBytes
          relationBytes ssa with
      | error err =>
          simp [hsource, hrelation, Bind.bind, Except.bind] at hcheck
      | ok program =>
          by_cases halign : checkEffectsAlignment ssa certificate = true
          · cases hname : ssa.names[ssa.output]? with
            | none =>
                simp [hsource, hrelation, halign, hname,
                  Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
            | some outputName =>
                cases hboundary : checkBoundary abiBytes assignmentBytes
                    rawPublicBytes ssa.lane_count ssa.inputs outputName
                    values claimed with
                | error err =>
                    simp [hsource, hrelation, halign, hname, hboundary,
                      Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
                | ok success =>
                    cases success
                    cases hparse : GeneralLinearSSAByteRun.parseTypedAssignment
                        assignmentBytes with
                    | error err =>
                        simp [hsource, hrelation, halign, hname, hboundary,
                          hparse, Bind.bind, Except.bind, Pure.pure,
                          Except.pure] at hcheck
                    | ok assignment =>
                        cases hstate : GeneralLinearSSAEffectsInputState.checkInputState
                            program assignment ssa.names certificate values with
                        | none =>
                            simp [hsource, hrelation, halign, hname,
                              hboundary, hparse, hstate, Bind.bind,
                              Except.bind, Pure.pure, Except.pure] at hcheck
                        | some inputEnv =>
                            by_cases hclaimed : S31.assigned
                                assignment.publicOutputs outputName ⟨.m31, n⟩ =
                                  .ok (laneValue claimed)
                            · cases heval : program.evaluate assignment with
                              | error err =>
                                  simp [hsource, hrelation, halign,
                                    hname, hboundary, hparse, hstate,
                                    hclaimed, heval, Bind.bind,
                                    Except.bind, Pure.pure, Except.pure]
                                    at hcheck
                              | ok words =>
                                  by_cases hwords : words =
                                      orderedPublicWords ssa.inputs values claimed
                                  · have hresult :
                                        (Except.ok (EffectsByteRun.mk ssa meaning
                                          certificate program assignment inputEnv
                                          words) : Check EffectsByteRun) =
                                          .ok run := by
                                      simpa [hsource, hrelation, halign,
                                        hname, hboundary, hparse, hstate,
                                        hclaimed, heval, hwords,
                                        Bind.bind, Except.bind, Pure.pure,
                                        Except.pure] using hcheck
                                    have hrun : run = EffectsByteRun.mk ssa meaning
                                        certificate program assignment inputEnv
                                        words := (Except.ok.inj hresult).symm
                                    subst run
                                    obtain ⟨hdenotation, selectedName,
                                      hselected, hassigned⟩ :=
                                      checked_effects_source_program_evaluate
                                        sourceBytes certificateBytes relationBytes
                                        ssa meaning certificate program assignment
                                        inputEnv values words hsource hrelation
                                        halign hstate heval
                                    have hsame : selectedName = outputName :=
                                      Option.some.inj (hselected.symm.trans hname)
                                    subst selectedName
                                    have houtput : claimed =
                                        meaning.output.eval values := by
                                      apply laneValue_injective
                                      exact Except.ok.inj
                                        (hclaimed.symm.trans hassigned)
                                    rw [← houtput] at hdenotation
                                    have hraw := (checked_boundary_parts
                                      abiBytes assignmentBytes rawPublicBytes
                                      ssa.lane_count ssa.inputs outputName
                                      values claimed hboundary).2.2.2.2
                                    exact ⟨hdenotation, hraw,
                                      (by simp), (by simpa using heval)⟩
                                  · simp [hsource, hrelation, halign,
                                      hname, hboundary, hparse, hstate,
                                      hclaimed, heval, hwords, Bind.bind,
                                      Except.bind, Pure.pure, Except.pure]
                                      at hcheck
                            · simp [hsource, hrelation, halign, hname,
                                hboundary, hparse, hstate, hclaimed,
                                Bind.bind, Except.bind, Pure.pure,
                                Except.pure] at hcheck
          · simp [hsource, hrelation, halign, Bind.bind,
              Except.bind] at hcheck

end S31.Functional.Correspondence.GeneralLinearSSAEffectsByteRun
