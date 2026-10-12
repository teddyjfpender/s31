import S31.Gadgets.Functional.SSANamedExecution

/-!
The named SSA execution theorem reaches the normalized program environment.
This module closes the next local boundary: an accepted public output claim
must equal that environment's source value. The theorem is still conditional
on the canonical named-program checker and accepted four-lane input; it does
not speak about Python serialization or native proof verification.
-/

namespace S31.Functional.SSANamedPublicClaim

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSANamedProgram
open S31.Functional.SSANamedExecution

private theorem value_beq_eq (a b : Value) (h : (a == b) = true) : a = b := by
  cases a with
  | mk ak aw =>
    cases b with
    | mk bk bw =>
      change instBEqValue.beq ⟨ak, aw⟩ ⟨bk, bw⟩ = true at h
      cases ak <;> cases bk
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, instBEqValue.beq, instBEqKind.beq] using h)
        simp [hw]
      · simp only [instBEqValue.beq, BEq.beq, instBEqKind.beq,
          Bool.and_eq_true] at h
        have hc := h.1
        cases hc
      · simp only [instBEqValue.beq, BEq.beq, instBEqKind.beq,
          Bool.and_eq_true] at h
        have hc := h.1
        cases hc
      · have hw : aw = bw := (beq_iff_eq).mp
          (by simpa [BEq.beq, instBEqValue.beq, instBEqKind.beq] using h)
        simp [hw]

theorem outputs_agree_source (source : Source 1)
    (certificate : Certificate) (program : Program)
    (assignment : Assignment) (input : Lanes) (env : S31.Env)
    (hcanonical : program = encode certificate)
    (houtput : lookup env (wireName certificate.output) =
      some (laneValue (source.value (fun _ => input))))
    (hagree : program.outputsAgree assignment env = .ok ()) :
    assigned assignment.publicOutputs (wireName certificate.output)
      ⟨.m31, 4⟩ =
      .ok (laneValue (source.value (fun _ => input))) := by
  rw [hcanonical] at hagree
  unfold Program.outputsAgree at hagree
  simp only [encode, outputsAgreeNames, houtput] at hagree
  cases hassigned : assigned assignment.publicOutputs
      (wireName certificate.output)
      (laneValue (source.value (fun _ => input))).shape with
  | error err => simp [hassigned] at hagree
  | ok expected =>
      have heq : laneValue (source.value (fun _ => input)) = expected := by
        have hbeq :
            (laneValue (source.value (fun _ => input)) == expected) = true := by
          simpa [hassigned] using hagree
        exact value_beq_eq _ _ hbeq
      rw [← heq] at hassigned
      simpa [laneValue, Value.shape] using hassigned

theorem checked_public_claim_sound (source : Source 1)
    (certificate : Certificate) (program : Program)
    (assignment : Assignment) (input : Lanes)
    (hNamed : checkNamed source certificate program = some ())
    (hdistinct : Distinct (certificate.instructions.length + 1))
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok (laneValue input))
    (haccept : ∃ words, program.evaluate assignment = .ok words) :
    assigned assignment.publicOutputs (wireName certificate.output)
      ⟨.m31, 4⟩ =
      .ok (laneValue (source.value (fun _ => input))) := by
  obtain ⟨env, henv, houtput⟩ :=
    checked_program_environment_sound source certificate program
      assignment input hNamed hdistinct hprivate hinput
  obtain ⟨words, haccept⟩ := haccept
  have hagree : program.outputsAgree assignment env = .ok () := by
    unfold Program.evaluate at haccept
    rw [henv] at haccept
    change (do
      let claimed ← program.claimedWords assignment
      program.outputsAgree assignment env
      pure claimed) = .ok words at haccept
    cases hclaimed : program.claimedWords assignment with
    | error err =>
        rw [hclaimed] at haccept
        change Except.error err = Except.ok words at haccept
        cases haccept
    | ok claim =>
        cases hout : program.outputsAgree assignment env with
        | error err =>
            rw [hclaimed, hout] at haccept
            change Except.error err = Except.ok words at haccept
            cases haccept
        | ok witness =>
            cases witness
            simpa using hout
  exact outputs_agree_source source certificate program assignment input env
    (checkNamed_canonical source certificate program hNamed) houtput hagree

end S31.Functional.SSANamedPublicClaim
