import S31.Gadgets.Functional.Correspondence.SourceDeterminedPhysicalSoundness
import S31.Gadgets.Functional.SSAAirRows

/-!
Constructive, arbitrary-input local AIR witness for every byte-admitted
bounded direct-Gate program. The honest interpreter supplies a single value
for each SSA wire. The modeled source cells then satisfy their selected
native arithmetic polynomial at their exact source-derived addresses.

This construction does not fill source-independent constant, packing, or
padding rows of the physical 512-row trace and does not prove Gate balance.
-/

namespace S31.Functional.Correspondence.HonestSourceCellWitness

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Functional.SSACertificate
open S31.Functional.SSATextBytes
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSAAliasTextBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSAAirRows
open S31.Functional.Correspondence.SourceDeterminedDirectRows
open S31.Functional.Correspondence.AliasCanonicalIrBytes

/-- Every successful local AIR execution extends the preceding wire-value
list by appending outputs; old wire values are never overwritten. -/
private theorem trace_extends {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    ∃ suffix, final = initial ++ suffix := by
  induction h with
  | done values => exact ⟨[], by simp⟩
  | @next values final instruction rest output _ _ ih =>
      obtain ⟨suffix, hfinal⟩ := ih
      exact ⟨output :: suffix, by simpa [List.append_assoc] using hfinal⟩

/-- Read the common final SSA value array at a native direct-Gate address.
The default is never used for accepted source operands or outputs. -/
def wireOfFinal (final : List Lanes) (atAddress : Nat) : Quad :=
  packM31 ((final[atAddress - 22]?).getD (fun _ => 0))

private theorem wire_of_lookup (final : List Lanes) (id : Nat)
    (value : Lanes) (hlookup : final[id]? = some value) :
    wireOfFinal final (address id) = packM31 value := by
  simp [wireOfFinal, address, hlookup]

private theorem final_row_values {values final : List Lanes}
    {instruction : Instruction} {rest : List Instruction}
    (output : Lanes) (hrow : acceptsRow values instruction output)
    (hrest : AcceptsTrace (values ++ [output]) rest final) :
    accepts (encode (s31Op instruction.multiply))
      (wireOfFinal final (address instruction.lhs))
      (wireOfFinal final (address instruction.rhs))
      (wireOfFinal final (address instruction.id)) := by
  obtain ⟨lhs, rhs, hid, hleft, hright, hair⟩ := hrow
  obtain ⟨suffix, hfinal⟩ := trace_extends hrest
  have hleftBound : instruction.lhs < values.length :=
    (List.getElem?_eq_some_iff.mp hleft).1
  have hrightBound : instruction.rhs < values.length :=
    (List.getElem?_eq_some_iff.mp hright).1
  have hleftFinal : final[instruction.lhs]? = some lhs := by
    rw [hfinal, List.append_assoc,
      List.getElem?_append_left hleftBound]
    exact hleft
  have hrightFinal : final[instruction.rhs]? = some rhs := by
    rw [hfinal, List.append_assoc,
      List.getElem?_append_left hrightBound]
    exact hright
  have houtputFinal : final[instruction.id]? = some output := by
    rw [hfinal, hid]
    simp
  simpa [wire_of_lookup final instruction.lhs lhs hleftFinal,
    wire_of_lookup final instruction.rhs rhs hrightFinal,
    wire_of_lookup final instruction.id output houtputFinal] using hair

/-- All source rows in an honest execution satisfy their arithmetic
polynomial simultaneously under one final address-to-value function. -/
theorem honest_trace_source_polynomials {initial final : List Lanes}
    {instructions : List Instruction}
    (h : AcceptsTrace initial instructions final) :
    ∀ instruction ∈ instructions,
      accepts (encode (s31Op instruction.multiply))
        (wireOfFinal final (address instruction.lhs))
        (wireOfFinal final (address instruction.rhs))
        (wireOfFinal final (address instruction.id)) := by
  induction h with
  | done => simp
  | @next values final instruction rest output hrow hrest ih =>
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htail
      · subst item
        exact final_row_values output hrow hrest
      · exact ih item htail

private theorem executed_source_slice (certificate : Certificate)
    (input output : Lanes) (final : List Lanes)
    (htrace : AcceptsTrace [input] certificate.instructions final)
    (hselected : final[certificate.output]? = some output)
    (hplan : SourcePlan certificate
      (expectedCells certificate (compiledAddRows certificate))) :
    sourceCellsEvaluated certificate
        (expectedCells certificate (compiledAddRows certificate))
        (wireOfFinal final) ∧
      wireOfFinal final (address certificate.output) = packM31 output := by
  have hpolynomials : nativePolynomialRows certificate (wireOfFinal final) :=
    honest_trace_source_polynomials htrace
  constructor
  · intro instruction hmember
    obtain ⟨cell, hcell, hadd, hsub, hmul, hpoint,
      hin0, hin1, hout, _⟩ := hplan instruction hmember
    refine ⟨cell, hcell, hadd, hsub, hmul, hpoint,
      hin0, hin1, hout, ?_⟩
    have hflags : cellFlags cell = encode (s31Op instruction.multiply) := by
      cases hkind : instruction.multiply <;>
        simp [cellFlags, s31Op, encode, hkind,
          hadd, hsub, hmul, hpoint]
    simpa [cellAccepts, hflags, hin0, hin1, hout] using
      (hpolynomials instruction hmember)
  · exact wire_of_lookup final certificate.output output hselected

/-- For any accepted source and canonical normalized relation bytes, the
interpreter constructs a final SSA value array and one coherent wire map.
Every source instruction's *projected native cell* has exact checked flags,
addresses, and a vanishing local arithmetic relation. This is a genuine
existence result for the source slice of the modeled physical layout. -/
theorem checked_direct_source_cells_satisfiable
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (input : Lanes)
    (hcheck : checkRelation sourceBytes normalizedBytes = some certificate) :
    ∃ (final : List Lanes) (output : Lanes),
      SSATextBytes.denotation sourceBytes input = some output ∧
      sourceCellsEvaluated certificate
        (expectedCells certificate (compiledAddRows certificate))
        (wireOfFinal final) ∧
      wireOfFinal final (address certificate.output) =
        packM31 output := by
  have hparse : ∃ parsed, parseBytes sourceBytes = some parsed := by
    unfold checkRelation at hcheck
    cases hp : parseBytes sourceBytes with
    | none => simp [hp] at hcheck
    | some parsed => exact ⟨parsed, rfl⟩
  obtain ⟨parsed, hparse⟩ := hparse
  let output := parsed.meaning.eval input
  have hdenotation : SSATextBytes.denotation sourceBytes input =
      some output := by
    simp [SSATextBytes.denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output := by
    rw [checked_relation_sound sourceBytes normalizedBytes certificate input hcheck]
    exact hdenotation
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselected : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have htrace : AcceptsTrace [input] certificate.instructions final :=
        executing_trace_has_air_rows certificate.instructions [input] final hrun
      have hplan : SourcePlan certificate
          (expectedCells certificate (compiledAddRows certificate)) :=
        (direct_bytes_projected_roster sourceBytes normalizedBytes
          certificate hcheck).1
      obtain ⟨hcells, hwire⟩ := executed_source_slice certificate input output
        final htrace hselected hplan
      exact ⟨final, output, hdenotation, hcells, hwire⟩

/-- Canonical alias and redundant-parenthesis programs erase to the same
producer graph. Every accepted byte triple admits the same arbitrary-input
source-cell arithmetic witness with no extra physical producer rows. -/
theorem checked_canonical_alias_source_cells_satisfiable
    (sourceBytes normalizedBytes canonicalBytes : Token)
    (certificate : Certificate) (input : Lanes)
    (hcheck : checkAliasCanonical sourceBytes normalizedBytes canonicalBytes =
      some certificate) :
    ∃ (final : List Lanes) (output : Lanes),
      SSAAliasTextBytes.denotation sourceBytes input = some output ∧
      sourceCellsEvaluated certificate
        (expectedCells certificate (compiledAddRows certificate))
        (wireOfFinal final) ∧
      wireOfFinal final (address certificate.output) =
        packM31 output := by
  obtain ⟨parsed, hparse, _, _, _, _, hsemantics⟩ :=
    checked_alias_canonical_bytes_sound sourceBytes normalizedBytes
      canonicalBytes certificate input hcheck
  let output := parsed.meaning.eval input
  have hdenotation : SSAAliasTextBytes.denotation sourceBytes input =
      some output := by
    simp [SSAAliasTextBytes.denotation, hparse, output]
  have hexecute : executeNormalized certificate input = some output :=
    hsemantics.trans hdenotation
  rw [execute_normalized_eq_execute] at hexecute
  unfold execute at hexecute
  cases hrun : certificate.instructions.foldlM executeStep [input] with
  | none => simp [hrun] at hexecute
  | some final =>
      have hselected : final[certificate.output]? = some output := by
        simpa [hrun] using hexecute
      have htrace : AcceptsTrace [input] certificate.instructions final :=
        executing_trace_has_air_rows certificate.instructions [input] final hrun
      have hplan : SourcePlan certificate
          (expectedCells certificate (compiledAddRows certificate)) :=
        (canonical_alias_projected_rows_distinct sourceBytes normalizedBytes
          canonicalBytes certificate hcheck).1
      obtain ⟨hcells, hwire⟩ := executed_source_slice certificate input output
        final htrace hselected hplan
      exact ⟨final, output, hdenotation, hcells, hwire⟩

end S31.Functional.Correspondence.HonestSourceCellWitness
