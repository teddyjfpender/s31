import S31.Gadgets.Functional.Correspondence.GeneralLinearSSABytes
import S31.Gadgets.Functional.SSANormalizedBytes
import S31.Gadgets.Functional.SSANativeTopologyCheck

/-!
The exact overlap between the older public-four-lane direct-Gate checker and
the new emitted linear SSA checker. Both admit the same ordered add/mul graph
when the certificates are *equal after the explicit lift below*. The first
theorem joins their byte-level source/relation checkers. The second also
uses the older modeled topology and authenticated-row premises; neither
premise is supplied by, or claimed for, a native proof verifier here.
-/

namespace S31.Functional.Correspondence.GeneralLinearSSAJoin

open GeneralLinearSSA

def liftInstruction (instruction : SSACertificate.Instruction) : Instruction :=
  { id := instruction.id, lhs := instruction.lhs, rhs := instruction.rhs,
    op := if instruction.multiply then .mul else .add }

def liftCertificate (certificate : SSACertificate.Certificate) : Certificate :=
  { inputs := 1, instructions := certificate.instructions.map liftInstruction,
    output := certificate.output }

theorem lift_step (values : List (Lanes 4))
    (instruction : SSACertificate.Instruction) :
    executeStep values (liftInstruction instruction) =
      SSACertificate.executeStep values instruction := by
  cases instruction with
  | mk id lhs rhs multiply =>
      cases multiply <;> rfl

theorem lift_steps (instructions : List SSACertificate.Instruction)
    (values : List (Lanes 4)) :
    (instructions.map liftInstruction).foldlM executeStep values =
      instructions.foldlM SSACertificate.executeStep values := by
  induction instructions generalizing values with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [List.map_cons, List.foldlM_cons, lift_step]
      cases hstep : SSACertificate.executeStep values instruction with
      | none => simp
      | some next => simpa using ih next

theorem lifted_execute (certificate : SSACertificate.Certificate)
    (input : Lanes 4) :
    execute (liftCertificate certificate) (fun _ => input) =
      SSACertificate.execute certificate input := by
  have hfold := lift_steps certificate.instructions [input]
  unfold execute SSACertificate.execute liftCertificate
  simp only [initialValues, List.range_one, List.map_singleton]
  rw [hfold]

/-- If the old exact source/relation-byte check and the new canonical
certificate-byte check return literally the same add/mul graph after lifting,
they assign the same four-lane output to every input. The new `sourceTerm`
is still supplied separately; neither check proves the Python parser correct.
-/
theorem public4_byte_checkers_join
    (sourceBytes relationBytes : List Nat) (certificateBytes : String)
    (old : SSACertificate.Certificate) (sourceTerm : Term)
    (ssa : EmittedSSA) (new : Certificate) (input : Lanes 4)
    (hOld : SSANormalizedBytes.checkRelation sourceBytes relationBytes = some old)
    (hNew : GeneralLinearSSABytes.checkCertificate certificateBytes sourceTerm =
      .ok (ssa, new))
    (hSame : new = liftCertificate old) :
    SSATextBytes.denotation sourceBytes input =
      some (sourceTerm.eval (fun _ => input)) := by
  have hchecked :=
    (GeneralLinearSSABytes.checked_certificate_parts
      certificateBytes sourceTerm ssa new hNew).2
  have hrun : execute new (fun _ => input) =
      some (sourceTerm.eval (fun _ => input)) :=
    checked_execution new sourceTerm (fun _ => input)
      (checked_emitted_certificate ssa sourceTerm new hchecked).2
  rw [hSame, lifted_execute] at hrun
  rw [← SSANormalizedBytes.checked_relation_sound sourceBytes relationBytes
    old input hOld, SSACertificate.execute_normalized_eq_execute]
  exact hrun

/-- For the intersection, the *modeled* authenticated native Gate rows
compute the very source value independently admitted by the new certificate.
`AuthenticatedRows` is an explicit assumption; no native PCS/FRI link follows.
-/
theorem public4_modeled_rows_join
    (sourceBytes relationBytes : List Nat) (certificateBytes : String)
    (old : SSACertificate.Certificate) (sourceTerm : Term)
    (ssa : EmittedSSA) (new : Certificate) (input claimed : Lanes 4)
    (addresses finalAddresses : List Nat)
    (rows : List SSANativeTopologyCheck.Row)
    (finalValues : List (Lanes 4))
    (hOld : SSANormalizedBytes.checkRelation sourceBytes relationBytes = some old)
    (hNew : GeneralLinearSSABytes.checkCertificate certificateBytes sourceTerm =
      .ok (ssa, new))
    (hSame : new = liftCertificate old)
    (hTopology : SSANativeTopologyCheck.checkRows addresses old.instructions
      (rows.map SSANativeTopologyCheck.Row.gate) = some finalAddresses)
    (hAuthenticated : SSANativeTopologyCheck.AuthenticatedRows addresses
      [input] rows finalAddresses finalValues)
    (hOutput : finalValues[old.output]? = some claimed) :
    claimed = sourceTerm.eval (fun _ => input) ∧
    SSATextBytes.denotation sourceBytes input = some claimed := by
  have hrows := SSANativeTopologyCheck.checked_rows_air hTopology hAuthenticated
  have hrun := SSAAirRows.accepted_trace_executes hrows
  have hOldRun : SSACertificate.execute old input = some claimed := by
    simpa [SSACertificate.execute, hrun] using hOutput
  have hjoin := public4_byte_checkers_join sourceBytes relationBytes
    certificateBytes old sourceTerm ssa new input hOld hNew hSame
  have hchecked :=
    (GeneralLinearSSABytes.checked_certificate_parts
      certificateBytes sourceTerm ssa new hNew).2
  have hNewRun : execute new (fun _ => input) =
      some (sourceTerm.eval (fun _ => input)) :=
    checked_execution new sourceTerm (fun _ => input)
      (checked_emitted_certificate ssa sourceTerm new hchecked).2
  rw [hSame, lifted_execute, hOldRun] at hNewRun
  have hclaim : claimed = sourceTerm.eval (fun _ => input) :=
    Option.some.inj hNewRun
  exact ⟨hclaim, hjoin.trans (congrArg some hclaim.symm)⟩

end S31.Functional.Correspondence.GeneralLinearSSAJoin
