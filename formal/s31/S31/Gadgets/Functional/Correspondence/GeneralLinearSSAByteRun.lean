import S31.Gadgets.Functional.Correspondence.GeneralLinearSSAInputState

/-!
The pure source, normalized relation, ABI and interpreter gates consume the
same exact assignment JSON bytes. Each of the independently implemented Lean
parsers must accept those bytes; the actual normalized interpreter receives
the strict typed parse. The semantic theorem composes these gates without
assuming equal final source/interpreter values.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAByteRun

open S31.Functional.Correspondence
open GeneralLinearSSAProgramEvaluate
open GeneralLinearSSAInputState
open GeneralLinearSSAPublicABI

abbrev Check := Except String

def parseTypedAssignment (bytes : String) : Check S31.Assignment := do
  if bytes.utf8ByteSize > 65536 then throw "assignment exceeds 65536 bytes"
  let json ← Lean.Json.parse bytes
  if GeneralLinearSSABytes.pythonCanonical 0 json ++ "\n" != bytes then
    throw "noncanonical assignment JSON"
  S31.Json.assignment json

structure PureByteRun where
  ssa : GeneralLinearSSA.EmittedSSA
  meaning : GeneralLinearSSA.Term
  certificate : GeneralLinearSSA.Certificate
  program : S31.Program
  assignment : S31.Assignment
  inputEnv : S31.Env
  words : List S31.M31

private theorem laneValue_injective {n : Nat} :
    Function.Injective (laneValue (n := n)) := by
  intro left right h
  exact List.ofFn_inj.mp (congrArg S31.Value.words h)

/-- A bounded pure-source run is admitted only when exact source/certificate,
normalized relation, public ABI bytes, typed assignment, initial SSA state,
public output, and actual interpreter all agree on the supplied statement.
There is no source-vs-interpreter final output comparison. -/
def checkPureByteRun {n : Nat} (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (values : Nat → Lanes n)
    (claimed : Lanes n) : Check PureByteRun := do
  let (ssa, meaning, certificate) ←
    GeneralLinearSSASourceBytes.checkSourceCertificate sourceBytes certificateBytes
  let program ← checkPureSourceRelationSSA sourceBytes relationBytes ssa
  if !checkPureAlignment ssa certificate then
    throw "SSA instruction alignment differs"
  let outputName ← match ssa.names[ssa.output]? with
    | none => throw "selected output name missing"
    | some name => pure name
  checkBoundary abiBytes assignmentBytes rawPublicBytes ssa.lane_count
    ssa.inputs outputName values claimed
  let assignment ← parseTypedAssignment assignmentBytes
  let inputEnv ← match checkInputState program assignment ssa.names
      certificate values with
    | none => throw "typed assignment differs from indexed initial SSA state"
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

/-- A successful exact-byte run binds the ABI claim to the independently
parsed source denotation through the actual normalized interpreter. -/
theorem checked_pure_byte_run {n : Nat} (sourceBytes : List Nat)
    (certificateBytes relationBytes abiBytes assignmentBytes : String)
    (rawPublicBytes : List Nat) (values : Nat → Lanes n)
    (claimed : Lanes n) (run : PureByteRun)
    (hcheck : checkPureByteRun sourceBytes certificateBytes relationBytes
      abiBytes assignmentBytes rawPublicBytes values claimed = .ok run) :
    GeneralLinearSSASourceBytes.denotation sourceBytes values =
      some (run.meaning.eval values) ∧
    claimed = run.meaning.eval values ∧
    rawPublicBytes = publicWordBytes
      (orderedPublicWords run.ssa.inputs values claimed) ∧
    parseTypedAssignment assignmentBytes = .ok run.assignment ∧
    run.program.evaluate run.assignment = .ok run.words := by
  unfold checkPureByteRun at hcheck
  cases hsource : GeneralLinearSSASourceBytes.checkSourceCertificate
      sourceBytes certificateBytes with
  | error err => simp [hsource, Bind.bind, Except.bind] at hcheck
  | ok triple =>
      obtain ⟨ssa, meaning, certificate⟩ := triple
      cases hrelation : checkPureSourceRelationSSA sourceBytes relationBytes ssa with
      | error err =>
          simp [hsource, hrelation, Bind.bind, Except.bind] at hcheck
      | ok program =>
          by_cases halign : checkPureAlignment ssa certificate = true
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
                    cases hparse : parseTypedAssignment assignmentBytes with
                    | error err =>
                        simp [hsource, hrelation, halign, hname, hboundary,
                          hparse, Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
                    | ok assignment =>
                        cases hstate : checkInputState program assignment
                            ssa.names certificate values with
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
                                    Except.bind, Pure.pure, Except.pure] at hcheck
                              | ok words =>
                                  by_cases hwords : words =
                                      orderedPublicWords ssa.inputs values claimed
                                  · have hresult :
                                        (Except.ok (PureByteRun.mk ssa meaning
                                          certificate program assignment inputEnv
                                          words) : Check PureByteRun) =
                                          .ok run := by
                                      simpa [hsource, hrelation, halign,
                                        hname, hboundary, hparse, hstate,
                                        hclaimed, heval, hwords,
                                        Bind.bind, Except.bind, Pure.pure,
                                        Except.pure] using hcheck
                                    have hrun : run = PureByteRun.mk ssa meaning
                                        certificate program assignment inputEnv
                                        words := (Except.ok.inj hresult).symm
                                    subst run
                                    obtain ⟨hdenotation, outputName',
                                      hname', _, hassigned⟩ :=
                                      checked_pure_source_program_evaluate_with_state_check
                                        sourceBytes certificateBytes relationBytes
                                        ssa meaning certificate program assignment
                                        inputEnv values words hsource hrelation
                                        halign hstate heval
                                    have hsame : outputName' = outputName :=
                                      Option.some.inj (hname'.symm.trans hname)
                                    subst outputName'
                                    have houtput : claimed = meaning.eval values := by
                                      apply laneValue_injective
                                      exact Except.ok.inj (hclaimed.symm.trans hassigned)
                                    have hraw := (checked_boundary_parts
                                      abiBytes assignmentBytes rawPublicBytes
                                      ssa.lane_count ssa.inputs outputName
                                      values claimed hboundary).2.2.2.2
                                    exact ⟨hdenotation, houtput, hraw,
                                      (by simp),
                                      (by simpa using heval)⟩
                                  · simp [hsource, hrelation, halign,
                                      hname, hboundary, hparse, hstate,
                                      hclaimed, heval, hwords, Bind.bind,
                                      Except.bind, Pure.pure, Except.pure] at hcheck
                            · simp [hsource, hrelation, halign, hname,
                                hboundary, hparse, hstate, hclaimed,
                                Bind.bind, Except.bind, Pure.pure, Except.pure] at hcheck
          · simp [hsource, hrelation, halign, Bind.bind,
              Except.bind] at hcheck

end S31.Functional.Correspondence.GeneralLinearSSAByteRun
