import S31.Gadgets.Functional.Correspondence.RawGateSoundness
import S31.Gadgets.Functional.Correspondence.AliasSourceInput
import S31.Gadgets.Functional.SSAAliasTextBytes

/-!
The zero-cost alias and redundant-parentheses source fragment reaches the
same native direct-Gate AIR statement as its producer-only SSA certificate.
Aliases add lexical bindings but no arithmetic rows. The theorem uses the
source bytes accepted by `checkAliasRelation` and the same arbitrary decoded
trace assumptions as `RawGateSoundness`.

This is a source-grammar extension of the conditional algebraic argument.
It does not authenticate committed rows or prove native verifier execution,
PCS/FRI, or Fiat--Shamir challenge sampling.
-/

namespace S31.Functional.Correspondence.AliasRawGateSoundness

open S31
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSACertificate
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.Correspondence.RawGateSoundness

/-- The alias parser may add a lexical binding without a producer. An
arithmetic binding is admitted only while fewer than sixteen producers have
already been emitted. -/
private theorem parseLet_instruction_bound (state next : State)
    (hparse : parseLet state = some next)
    (hbound : state.instructions.length ≤ 16) :
    next.instructions.length ≤ 16 := by
  simp [parseLet, bind, Option.bind_eq_some_iff] at hparse
  aesop (config := { warnOnNonterminal := false })
  all_goals
    simp only [Option.bind_eq_some_iff] at right
    aesop

private theorem parseLetsFuel_instruction_bound (fuel : Nat) (state next : State)
    (hparse : parseLetsFuel fuel state = some next)
    (hbound : state.instructions.length ≤ 16) :
    next.instructions.length ≤ 16 := by
  induction fuel generalizing state with
  | zero =>
      simp [parseLetsFuel] at hparse
      rcases hparse with ⟨_, rfl⟩
      exact hbound
  | succ fuel ih =>
      simp only [parseLetsFuel] at hparse
      split at hparse
      · obtain ⟨middle, hstep, hrest⟩ :=
          Option.bind_eq_some_iff.mp hparse
        exact ih middle hrest
          (parseLet_instruction_bound state middle hstep hbound)
      · simp_all

theorem parseAliasBytes_instruction_bound (bytes : List Nat)
    (parsed : S31.Functional.SSATextBytes.Parsed)
    (hparse : parseAliasBytes bytes = some parsed) :
    parsed.certificate.instructions.length ≤ 16 := by
  simp [parseAliasBytes, Option.bind] at hparse
  repeat (split at hparse <;> simp_all)
  have hbudget := parseLetsFuel_instruction_bound 256 _ _
    (by assumption) (by simp)
  rcases hparse with ⟨_, _, _, _, _, _, _, hparsed⟩
  subst parsed
  simpa using hbudget

/-- Successful alias-source/normalized-byte admission inherits the same
sixteen-arithmetic-instruction cap as the direct source grammar. Alias-only
lets consume parser fuel but add no arithmetic instruction. -/
theorem checked_alias_relation_instruction_bound
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (hrelation : checkAliasRelation sourceBytes normalizedBytes = some certificate) :
    certificate.instructions.length ≤ 16 := by
  unfold checkAliasRelation at hrelation
  cases hsource : parseAliasBytes sourceBytes with
  | none => simp [hsource] at hrelation
  | some parsed =>
      cases hencoded : S31.Functional.SSANormalizedBytes.encodeNormalized parsed with
      | none => simp [hsource, hencoded] at hrelation
      | some expected =>
          by_cases hmatch : expected = normalizedBytes
          · have hcertificate : parsed.certificate = certificate := by
              simpa [hsource, hencoded, hmatch] using hrelation
            subst certificate
            exact parseAliasBytes_instruction_bound sourceBytes parsed hsource
          · simp [hsource, hencoded, hmatch] at hrelation

/-- The alias grammar binds its bytes to the same positional certificate as
the physical row context. Its parser's nonempty checked arithmetic body
proves the source input is used, so the final input pack row yields to Gate. -/
structure AliasFixedTraceContext (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes) : Prop
    extends PhysicalTraceContext trace certificate totalAddRows input claimed where
  relation : checkAliasRelation sourceBytes normalizedBytes = some certificate

/-- Alias-byte admission preserves the source instruction budget, while the
native row partition gives each projected source, pack, mask, inverse and
public copy cell a separate trace position. `fixedMatches` itself supplies
the 512-row bounds because every cell matches a `Fin 512` trace index. -/
theorem alias_projected_cells_distinct (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : AliasFixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed) :
    (((expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows)).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows),
      cell.traceRow < 2 ^ 9) := by
  have hbudget := checked_alias_relation_instruction_bound sourceBytes
    normalizedBytes certificate h.relation
  have ha := source_add_count_bounded certificate
  have hm := source_mul_count_bounded certificate
  have hrows := h.partition
  have hspace : 11 + sourceAddCount certificate ≤ totalAddRows := by
    norm_num at hrows
    omega
  have hgap : 3 + certificate.instructions.length ≤ totalAddRows + 28 := by
    norm_num at hrows
    omega
  have hsource := expected_cells_trace_rows_nodup certificate
    totalAddRows hgap
  have hpublic := expected_public_rows_nodup certificate totalAddRows hspace
  have hdisjoint : List.Disjoint
      ((expectedCells certificate totalAddRows).map ColumnCell.traceRow)
      ((expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows).map ColumnCell.traceRow) := by
    intro row hsourceRow hpublicRow
    obtain ⟨sourceCell, hsourceCell, hsourceEq⟩ :=
      List.mem_map.mp hsourceRow
    obtain ⟨publicCell, hpublicCell, hpublicEq⟩ :=
      List.mem_map.mp hpublicRow
    exact expected_source_public_rows_disjoint certificate totalAddRows hspace
      sourceCell hsourceCell publicCell hpublicCell
      (hsourceEq.trans hpublicEq.symm)
  constructor
  · rw [List.map_append]
    exact hsource.append hpublic hdisjoint
  · intro cell hcell
    have hmember : cell ∈ expectedCells certificate totalAddRows ++
        expectedInputCells certificate totalAddRows ++
        expectedOutputCells certificate totalAddRows := by
      simpa only [List.append_assoc] using hcell
    obtain ⟨i, hi, _, _, _, _, _⟩ := h.fixed cell hmember
    omega

/-- Exact Gate balance forces the public claim for source bytes with aliases
and redundant parentheses. It evaluates the exact alias-parsed bytes, not a
handwritten replacement source. -/
theorem balanced_implies_alias_claim (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : AliasFixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    denotation sourceBytes input = some claimed := by
  have hsource : ∃ parsed, parseAliasBytes sourceBytes = some parsed := by
    have hrelation := h.relation
    unfold checkAliasRelation at hrelation
    cases hp : parseAliasBytes sourceBytes with
    | none => simp [hp] at hrelation
    | some parsed => exact ⟨parsed, rfl⟩
  obtain ⟨parsed, hparse⟩ := hsource
  let output := parsed.meaning.eval input
  have hdenotation : denotation sourceBytes input = some output := by
    simp [denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_alias_relation_sound sourceBytes normalizedBytes
      certificate input h.relation]
    exact hdenotation
  have heq := physical_balanced_certificate_claim trace certificate
    totalAddRows input claimed output h.toPhysicalTraceContext
    (checked_alias_relation_source_input_used sourceBytes normalizedBytes
      certificate h.relation) hexecute hbalance
  simpa only [heq] using hdenotation

/-- A false public claim for an alias source makes the physical Gate event
multiset unequal for any fixed trace satisfying the local row context. -/
theorem forged_alias_claim_unbalanced (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : AliasFixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hforged : denotation sourceBytes input ≠ some claimed) :
    ¬ balanced (nativeRows trace) trace.externalUses trace.externalYields := by
  intro hbalance
  exact hforged (balanced_implies_alias_claim trace sourceBytes
    normalizedBytes certificate totalAddRows input claimed h hbalance)

/-- A fixed false public claim in the alias grammar can satisfy the
source-extracted raw Gate interaction AIR for at most
`(5s² + 2s + 1536) · |QM31|` ideal challenge pairs, under canonical Gate
addresses and bounded event counts. Static aliases add no AIR rows and hence
do not change the denominator term. -/
theorem forged_alias_claim_accepting_pairs_card_le (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : AliasFixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hforged : denotation sourceBytes input ≠ some claimed)
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
    (forged_alias_claim_unbalanced trace sourceBytes normalizedBytes
      certificate totalAddRows input claimed h hforged)
    hcanonical huses hyields

end S31.Functional.Correspondence.AliasRawGateSoundness
