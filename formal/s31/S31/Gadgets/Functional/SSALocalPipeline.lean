import S31.Gadgets.Functional.SSANamedPublicClaim
import S31.Gadgets.Functional.SSAAirRows

/-!
Composition of the checked four-lane source/SSA/named-Program fragment with
its complete local packed arithmetic-row relation and public-output check.
An AIR row reads values from its addressed prior wires here; authenticating
those reads through the native Gate lookup, and proving native row emission,
remain separate obligations. The source parser and serializer are not modeled.
-/

namespace S31.Functional.SSALocalPipeline

open S31
open S31.Functional.SSACertificate
open S31.Functional.SSANamedProgram
open S31.Functional.SSANamedExecution
open S31.Functional.SSANamedPublicClaim
open S31.Functional.SSAAirRows

/-- Every bounded, checked SSA program admits honest packed arithmetic rows
whose selected output is exactly the source value. This is local row
completeness for an arbitrary accepted certificate, including shared lets. -/
theorem checked_rows_complete (source : Source 1)
    (certificate : Certificate) (program : Program) (input : Lanes)
    (hbounded : checkBounded source certificate program = some ()) :
    ∃ final : List Lanes,
      AcceptsTrace [input] certificate.instructions final ∧
      final[certificate.output]? =
        some (source.value (fun _ => input)) := by
  have hnamed := checkBounded_named source certificate program hbounded
  have hcheck := checkNamed_positional source certificate program hnamed
  have hsource := checked_certificate_sound source certificate input hcheck
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [execute, hrun] at hsource
  | some final =>
      refine ⟨final,
        executing_trace_has_air_rows certificate.instructions [input] final hrun,
        ?_⟩
      simpa [execute, hrun] using hsource

/-- For any accepted bounded certificate and arbitrary accepted local AIR
row witnesses, the selected row output, actual normalized named environment,
and accepted public assignment all agree with source denotation. The row
relation assumes that every operand lookup reads its addressed prior value. -/
theorem checked_rows_named_public_agree (source : Source 1)
    (certificate : Certificate) (program : Program)
    (assignment : Assignment) (input claimed : Lanes)
    (final : List Lanes) (words : List M31)
    (hbounded : checkBounded source certificate program = some ())
    (hprivate : assignment.privateInputs = [])
    (hinput : assigned assignment.publicInputs "x" ⟨.m31, 4⟩ =
      .ok (laneValue input))
    (hrows : AcceptsTrace [input] certificate.instructions final)
    (hselected : final[certificate.output]? = some claimed)
    (haccept : program.evaluate assignment = .ok words) :
    ∃ env : S31.Env,
      program.environment assignment = .ok env ∧
      lookup env (wireName certificate.output) = some (laneValue claimed) ∧
      assigned assignment.publicOutputs (wireName certificate.output)
        ⟨.m31, 4⟩ = .ok (laneValue claimed) ∧
      claimed = source.value (fun _ => input) := by
  have hnamed := checkBounded_named source certificate program hbounded
  have hcheck := checkNamed_positional source certificate program hnamed
  have hrun := accepted_trace_executes hrows
  have hsource := checked_certificate_sound source certificate input hcheck
  have hclaimed : claimed = source.value (fun _ => input) := by
    simpa [execute, hrun, hselected] using hsource
  obtain ⟨env, henv, hlookup⟩ :=
    checked_bounded_environment_sound source certificate program
      assignment input hbounded hprivate hinput
  have hpublic := checked_public_claim_sound source certificate program
    assignment input hnamed
      (checkBounded_distinct source certificate program hbounded)
      hprivate hinput ⟨words, haccept⟩
  rw [← hclaimed] at hlookup hpublic
  exact ⟨env, henv, hlookup, hpublic, hclaimed⟩

end S31.Functional.SSALocalPipeline
