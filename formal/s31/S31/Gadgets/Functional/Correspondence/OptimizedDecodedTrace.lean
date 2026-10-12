import S31.Gadgets.Functional.Correspondence.OptimizedPhysicalRoster
import S31.Gadgets.Functional.Correspondence.SourceDeterminedPhysicalSoundness

/-!
An arbitrary decoded 512-row direct-Gate trace for the checked optimized
four-lane add/pointwise-multiply source fragment. The source, normalized JSON,
and compact canonical IR byte streams choose one certificate and its physical
row partition. Exact fixed-cell matches, installed arithmetic roots, ideal
Gate event balance, and public pins are separate facts about the trace.

This is an ideal decoded-trace theorem. Neither native Zig lowering nor PCS,
FRI, Fiat--Shamir, or proof-opening authentication follows from its premises.
-/

namespace S31.Functional.Correspondence.OptimizedDecodedTrace

open S31.Gadgets.Packed
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes (Token)
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.CanonicalDagOptimization
open S31.Functional.Correspondence.OptimizedTextBytes
open S31.Functional.Correspondence.OptimizedPhysicalRoster
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.SourceDeterminedPhysicalSoundness
open S31.Functional.Correspondence.RawGateSoundness

/-- CSE never removes an already emitted producer. -/
private theorem step_length_ge (state next : State) (raw : Instruction)
    (hstep : step state raw = some next) :
    state.instructions.length ≤ next.instructions.length := by
  unfold step at hstep
  by_cases hid : raw.id = state.sourceToCanonical.length
  · cases hlhs : state.sourceToCanonical[raw.lhs]? with
    | none => simp [hid, hlhs] at hstep
    | some lhs =>
        cases hrhs : state.sourceToCanonical[raw.rhs]? with
        | none => simp [hid, hlhs, hrhs] at hstep
        | some rhs =>
            cases hfind : findKey (raw.multiply, min lhs rhs, max lhs rhs)
                state.keys with
            | none =>
                have hnext : next.instructions = state.instructions ++
                    [{ id := state.instructions.length + 1,
                       lhs := min lhs rhs, rhs := max lhs rhs,
                       multiply := raw.multiply }] := by
                  simpa [step, hid, hlhs, hrhs, hfind] using
                    congrArg (fun item => item.map State.instructions) hstep.symm
                simp [hnext]
            | some existing =>
                have hnext : next.instructions = state.instructions := by
                  simpa [step, hid, hlhs, hrhs, hfind] using
                    congrArg (fun item => item.map State.instructions) hstep.symm
                simp [hnext]
  · simp [hid] at hstep

private theorem fold_length_ge (instructions : List Instruction)
    (state next : State)
    (hfold : instructions.foldlM step state = some next) :
    state.instructions.length ≤ next.instructions.length := by
  induction instructions generalizing state with
  | nil =>
      have hsame : state = next := by simpa using hfold
      subst next
      exact Nat.le_refl _
  | cons instruction rest ih =>
      simp only [List.foldlM_cons] at hfold
      cases hstep : step state instruction with
      | none => simp [hstep] at hfold
      | some middle =>
          exact (step_length_ge state middle instruction hstep).trans
            (ih middle (by simpa [hstep] using hfold))

/-- A successful first optimizer step creates a producer: the initial CSE
key table is empty, so that first key cannot be shared with an earlier node. -/
private theorem first_step_positive (raw : Instruction) (next : State)
    (hstep : step ({} : State) raw = some next) :
    0 < next.instructions.length := by
  unfold step at hstep
  by_cases hid : raw.id = 1
  · cases hlhs : ([0] : List Nat)[raw.lhs]? with
    | none => simp [hid, hlhs] at hstep
    | some lhs =>
        cases hrhs : ([0] : List Nat)[raw.rhs]? with
        | none => simp [hid, hlhs, hrhs] at hstep
        | some rhs =>
            have hnext : next.instructions =
                [{ id := 1, lhs := min lhs rhs,
                   rhs := max lhs rhs, multiply := raw.multiply }] := by
              simpa [step, hid, hlhs, hrhs, findKey] using
                congrArg (fun item => item.map State.instructions) hstep.symm
            simp [hnext]
  · simp [hid] at hstep

private theorem optimizer_preserves_nonempty (raw compact : Certificate)
    (hraw : raw.instructions ≠ [])
    (hopt : optimizeChecked raw = some compact) :
    compact.instructions ≠ [] := by
  unfold optimizeChecked at hopt
  cases hopt0 : optimize raw with
  | none => simp [hopt0] at hopt
  | some produced =>
      have haudit : audit raw produced = true := by
        by_contra hfalse
        simp [hopt0, hfalse] at hopt
      have hcompact : compact = produced := by
        simpa [hopt0, haudit] using hopt.symm
      subst compact
      unfold optimize at hopt0
      by_cases hsmall : raw.instructions.length > 16
      · simp [hsmall] at hopt0
      · cases hfold : raw.instructions.foldlM step
          ({} : State) with
        | none => simp [hsmall, hfold] at hopt0
        | some state =>
            cases hlookup : state.sourceToCanonical[raw.output]? with
            | none => simp [hsmall, hfold, hlookup] at hopt0
            | some output =>
                have hinstructions : produced.instructions =
                    state.instructions := by
                  have heq : produced = Certificate.mk
                      state.instructions output := by
                    simpa [hsmall, hfold, hlookup] using hopt0.symm
                  exact congrArg Certificate.instructions heq
                cases hins : raw.instructions with
                | nil => exact False.elim (hraw hins)
                | cons first rest =>
                    simp only [hins, List.foldlM_cons] at hfold
                    cases hfirst : step ({} : State) first with
                    | none => simp [hfirst] at hfold
                    | some middle =>
                        have hpos := first_step_positive first middle hfirst
                        have htail := fold_length_ge rest middle state
                          (by simpa [hfirst] using hfold)
                        intro hempty
                        have hzero : state.instructions.length = 0 := by
                          rw [hinstructions] at hempty
                          simp [hempty]
                        omega

private theorem parsed_raw_nonempty (bytes : Token)
    (parsed : OptimizedTextBytes.Parsed)
    (hparse : OptimizedTextBytes.parseBytes bytes = some parsed) :
    parsed.raw.instructions ≠ [] := by
  simp [OptimizedTextBytes.parseBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  rcases hparse with ⟨_, _, hnonempty, _, _, htail⟩
  aesop

private theorem checked_optimizer_has_term (raw compact : Certificate)
    (hopt : optimizeChecked raw = some compact) :
    ∃ meaning : Term, SSATextBytes.termFor compact = some meaning := by
  unfold optimizeChecked at hopt
  cases hraw : optimize raw with
  | none => simp [hraw] at hopt
  | some produced =>
      have haudit : audit raw produced = true := by
        by_contra hfalse
        simp [hraw, hfalse] at hopt
      have hcompact : compact = produced := by
        simpa [hraw, haudit] using hopt.symm
      subst compact
      unfold audit at haudit
      cases hsource : SSATextBytes.termFor raw with
      | none => simp [hsource] at haudit
      | some sourceTerm =>
          cases hcompactTerm : SSATextBytes.termFor produced with
          | none => simp [hsource, hcompactTerm] at haudit
          | some compactTerm => exact ⟨compactTerm, by simp⟩

/-- The public-input packing row's multiplicity is positive for every
admitted optimized source. This follows from a nonempty parser result, CSE
never deleting its first producer, and a checked compact term whose first
instruction can read only input wire zero. -/
theorem checked_optimized_source_input_used
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact) :
    0 < sourceInputUses compact := by
  obtain ⟨parsed, hparse, _, _, hcompact, _⟩ :=
    checked_bytes_sound sourceBytes normalizedBytes canonicalBytes
      compact (fun _ => 0) hbytes
  subst compact
  have hnonempty := optimizer_preserves_nonempty parsed.raw parsed.compact
    (parsed_raw_nonempty sourceBytes parsed hparse)
    parsed.checkedOptimization
  obtain ⟨meaning, hterm⟩ := checked_optimizer_has_term
    parsed.raw parsed.compact parsed.checkedOptimization
  exact source_input_used_of_checked_nonempty parsed.compact meaning
    hterm hnonempty

/-- An arbitrary decoded trace satisfying the same fixed, root, exact-Gate,
and public-event facts as the ordinary direct source profile has the meaning
of the checked optimized source. The input-pack producer is proved live from
the optimized parser and CSE transformation above. -/
theorem optimized_balanced_implies_source_claim
    (trace : Trace 9)
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (facts : UnpartitionedTrace trace compact input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    OptimizedTextBytes.denotation sourceBytes input = some claimed := by
  obtain ⟨parsed, hparse, _, _, hcompact, hexecute⟩ :=
    checked_bytes_sound sourceBytes normalizedBytes canonicalBytes
      compact input hbytes
  let output : Lanes := parsed.meaning.eval input
  have hrun : executeNormalized compact input = some output := by
    rw [hexecute]
    simp [OptimizedTextBytes.denotation, hparse, output]
  let physical := UnpartitionedTrace.toPhysical trace compact input claimed
    facts (optimized_bytes_partition sourceBytes normalizedBytes
      canonicalBytes compact hbytes)
  have hinputUsed := checked_optimized_source_input_used sourceBytes
    normalizedBytes canonicalBytes compact hbytes
  have heq : output = claimed :=
    physical_balanced_certificate_claim trace compact
      (compiledAddRows compact) input claimed output physical
      hinputUsed hrun hbalance
  simp [OptimizedTextBytes.denotation, hparse, output, heq]

/-- One theorem exposes the entire modeled source-to-physical path: exact
bytes, CSE's producer budget, the injective bounded row roster, and a public
claim forced by every balanced decoded trace satisfying the explicit local
constraints. A source `let` merged by CSE has no second AIR producer. -/
theorem optimized_source_to_decoded_air
    (trace : Trace 9)
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (facts : UnpartitionedTrace trace compact input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    OptimizedTextBytes.denotation sourceBytes input = some claimed ∧
    compact.instructions.length ≤ 16 ∧
    compiledAddRows compact + 1 + 27 + sourceMulCount compact + 8 =
      2 ^ 9 ∧
    (((expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact))).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells compact (compiledAddRows compact) ++
        (expectedInputCells compact (compiledAddRows compact) ++
          expectedOutputCells compact (compiledAddRows compact)),
      cell.traceRow < 2 ^ 9) := by
  obtain ⟨hbudget, hpartition, _, _, _, hnodup, hbounded⟩ :=
    optimized_bytes_exact_row_roster sourceBytes normalizedBytes
      canonicalBytes compact hbytes
  exact ⟨optimized_balanced_implies_source_claim trace sourceBytes
    normalizedBytes canonicalBytes compact input claimed hbytes facts
    hbalance, hbudget, hpartition, hnodup, hbounded⟩

/-- A false claim is incompatible with ideal exact Gate balance on the
same fixed decoded trace. The statement is universal over adversarial main
columns satisfying the declared fixed-cell and arithmetic-root facts. -/
theorem optimized_forged_claim_unbalanced
    (trace : Trace 9)
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (facts : UnpartitionedTrace trace compact input claimed)
    (hforged : OptimizedTextBytes.denotation sourceBytes input ≠ some claimed) :
    ¬ balanced (nativeRows trace)
      trace.externalUses trace.externalYields := by
  intro hbalance
  exact hforged (optimized_balanced_implies_source_claim trace sourceBytes
    normalizedBytes canonicalBytes compact input claimed hbytes facts
    hbalance)

/-- For a fixed false claim, raw LogUp acceptance is restricted by the
existing algebraic challenge-pair bound. This is the ideal independent-pair
bound; it does not quantify Fiat--Shamir or accepted native proofs. -/
theorem optimized_false_claim_raw_pair_bound
    (trace : Trace 9)
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (compact : Certificate) (input claimed : Lanes)
    (hbytes : checkBytes sourceBytes normalizedBytes canonicalBytes =
      some compact)
    (facts : UnpartitionedTrace trace compact input claimed)
    (hforged : OptimizedTextBytes.denotation sourceBytes input ≠ some claimed)
    (hcanonical : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      event.1 < 2147483647)
    (huses : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allUses (nativeRows trace) trace.externalUses).count event < 2147483647)
    (hyields : ∀ event ∈
      allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields,
      (allYields (nativeRows trace) trace.externalYields).count event < 2147483647) :
    (acceptingChallengePairs trace).card ≤
      (5 * (allUses (nativeRows trace) trace.externalUses ++
        allYields (nativeRows trace) trace.externalYields).toFinset.card ^ 2 +
        2 * (allUses (nativeRows trace) trace.externalUses ++
          allYields (nativeRows trace) trace.externalYields).toFinset.card +
        1536) * Fintype.card GateSecure := by
  exact unbalanced_accepting_pairs_card_le trace
    (optimized_forged_claim_unbalanced trace sourceBytes normalizedBytes
      canonicalBytes compact input claimed hbytes facts hforged)
    hcanonical huses hyields

end S31.Functional.Correspondence.OptimizedDecodedTrace
