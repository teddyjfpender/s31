import S31.Gadgets.Functional.SSAGeneralDecodedTraceBridge
import S31.Gadgets.Air.NativeGateRawSoundness
import S31.Gadgets.Air.DirectGateRowBytecodeBridge

/-!
Challenge soundness for the entire bounded four-lane direct-Gate source
fragment, including source instructions whose output has zero Gate uses.
The context is a fixed, *arbitrary* decoded 512-row trace. It does not assume
that the trace was produced by the honest witness writer. Exact fixed-cell
matches and installed arithmetic roots are premises about that trace.

For a false public claim, exact Gate balance is impossible. The source-
extracted raw Gate interaction AIR can therefore accept this fixed trace only
at its explicit collision/zero-denominator exceptional challenges. The bound
is algebraic for ideal independent challenges. Binding the trace and columns
to native verifier openings, and Fiat--Shamir challenge sampling, are separate
proof-system obligations.
-/

namespace S31.Functional.Correspondence.RawGateSoundness

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateChallenge
open S31.Gadgets.Air.GateAirRawSoundness
open S31.Gadgets.Air.NativeGateRawSoundness
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Gadgets.Air.DirectGateRowBytecodeBridge
open S31.Gadgets.Air.GeneratedDirectGateBytecodeLogUp
open S31.Functional.SSACertificate
open S31.Functional.SSANormalizedBytes
open S31.Functional.SSADirectGateBridge
open S31.Functional.SSAAirColumnCells
open S31.Functional.SSAInputAirCells
open S31.Functional.SSAOutputAirCells
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Functional.SSADeadRowGateJoin
open S31.Functional.SSAInstalledBytecodePublicInput
open S31.Functional.SSAInstalledBytecodePublicOutput
open S31.Functional.SSAGateLookupWireMap

/-- The exact local and public-boundary obligations for a fixed decoded
direct-Gate trace. No field constrains witness values to an honest execution;
the arithmetic roots and ideal producer uniqueness apply to whatever values
the trace contains. The public pins and fixed producers are explicit events.
This physical context is reusable across source grammars that compile to the
same positional certificate and normalized relation. -/
structure PhysicalTraceContext (trace : Trace 9) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes) : Prop where
  partition : totalAddRows + 1 + 27 + sourceMulCount certificate + 8 = 2 ^ 9
  fixed : ∀ cell ∈ expectedCells certificate totalAddRows ++
      expectedInputCells certificate totalAddRows ++
      expectedOutputCells certificate totalAddRows,
    fixedMatches trace cell
  arithmetic : allArithmeticRootsZero trace
  unique : uniqueProduced
    (allYields (nativeRows trace) trace.externalYields)
  zero : (0, base 0) ∈
    allYields (nativeRows trace) trace.externalYields
  basis1 : (15, unit ⟨1, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis2 : (2, unit ⟨2, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  basis3 : (16, unit ⟨3, by decide⟩) ∈
    allYields (nativeRows trace) trace.externalYields
  maskBasis : ∀ i : Fin 4,
    (maskBasisAddress i.val, unit i) ∈
      allYields (nativeRows trace) trace.externalYields
  inverseBasis : ∀ i : Fin 3,
    ((expectedInverseCell certificate totalAddRows i.val).in1,
      unitInverse ⟨i.val + 1, by omega⟩) ∈
        allYields (nativeRows trace) trace.externalYields
  inputPins : ∀ i : Fin 4,
    (3 + i.val, base (Field.toZMod (input i))) ∈ trace.externalYields
  outputPins : ∀ i : Fin 4,
    (7 + i.val, base (Field.toZMod (claimed i))) ∈ trace.externalYields

/-- Original direct-gate source grammar, bound to exact normalized bytes. -/
structure FixedTraceContext (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes) : Prop
    extends PhysicalTraceContext trace certificate totalAddRows input claimed where
  relation : checkRelation sourceBytes normalizedBytes = some certificate

/-- Physical-row and ideal-Gate soundness independent of the source parser.
Any source grammar whose checked denotation equals the positional certificate
can reuse this theorem. The input-use premise is a source-grammar invariant:
the final pack row must yield the packed public input into Gate. -/
theorem physical_balanced_certificate_claim (trace : Trace 9)
    (certificate : Certificate) (totalAddRows : Nat)
    (input claimed output : Lanes)
    (h : PhysicalTraceContext trace certificate totalAddRows input claimed)
    (hinputUsed : 0 < sourceInputUses certificate)
    (hexecute : executeNormalized certificate input = some output)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    output = claimed := by
  have hinputPositive := expected_input_cells_positive certificate
    totalAddRows hinputUsed
  obtain ⟨hsourceRows, hinputRows, houtputRows⟩ :=
    decoded_rows trace certificate
      (expectedCells certificate totalAddRows)
      (expectedInputCells certificate totalAddRows)
      (expectedOutputCells certificate totalAddRows)
      (source_plan_expected certificate totalAddRows)
      hinputPositive
      (expected_output_cells_positive certificate totalAddRows)
      h.fixed h.arithmetic
  have hinputYield := packed_input_yield_of_exact_gate certificate
    totalAddRows (expectedInputCells certificate totalAddRows) input
    (nativeRows trace) trace.externalUses trace.externalYields
    rfl hinputRows hbalance h.unique h.zero h.basis1 h.basis2
    h.basis3 h.inputPins
  let produced := allYields (nativeRows trace) trace.externalYields
  let wire := wireOfProduced produced
  have hinput : wire (address 0) = packM31 input :=
    wire_of_produced_event produced h.unique _ _ hinputYield
  have hsource := exact_gate_implies_used_rows certificate
    (expectedCells certificate totalAddRows) (nativeRows trace)
    trace.externalUses trace.externalYields hsourceRows hbalance h.unique
  have hselected : wire (address certificate.output) = packM31 output :=
    selected_wire_matches_used_rows certificate wire input output hinput
      (usedDependencies_of_sourceUses certificate)
      (sourceUses_selected_pos certificate) hsource hexecute
  have hboundary := output_boundary_of_exact_gate certificate
    totalAddRows (expectedOutputCells certificate totalAddRows) claimed
    (nativeRows trace) trace.externalUses trace.externalYields
    rfl houtputRows hbalance h.unique h.zero h.maskBasis h.inverseBasis
    h.outputPins
  have hclaim : wire (address certificate.output) = packM31 claimed :=
    output_boundary_claim certificate totalAddRows wire claimed hboundary
  have hpacked : packM31 output = packM31 claimed :=
    hselected.symm.trans hclaim
  funext i
  apply Field.toZMod_injective
  simpa only [coord_packM31] using
    congrArg (fun q => coord q i) hpacked

/-- The source byte check and 512-row partition rule make every projected
source and public-boundary fixed cell a separate in-range row. Thus the
`fixed` premise covers all checked operations without row aliasing or an
out-of-bounds cell. -/
theorem context_projected_cells_distinct (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : FixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed) :
    (((expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows)).map
      ColumnCell.traceRow)).Nodup ∧
    (∀ cell ∈ expectedCells certificate totalAddRows ++
        (expectedInputCells certificate totalAddRows ++
          expectedOutputCells certificate totalAddRows),
      cell.traceRow < 2 ^ 9) := by
  exact (checked_relation_modeled_row_roster sourceBytes normalizedBytes
    certificate totalAddRows h.relation h.partition).2

/-- Even for a maliciously chosen trace, exact Gate balance together with
the physical row constraints forces the public statement. -/
theorem balanced_implies_source_claim (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : FixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields) :
    S31.Functional.SSATextBytes.denotation sourceBytes input = some claimed := by
  exact decoded_public_io_sound trace sourceBytes normalizedBytes certificate
    totalAddRows (expectedCells certificate totalAddRows)
    (expectedInputCells certificate totalAddRows)
    (expectedOutputCells certificate totalAddRows) input claimed
    trace.externalUses trace.externalYields h.relation rfl rfl rfl
    h.fixed h.arithmetic hbalance h.unique h.zero h.basis1 h.basis2
    h.basis3 h.maskBasis h.inverseBasis h.inputPins h.outputPins

/-- A fixed false claim makes the decoded trace's ideal Gate event multiset
unbalanced. This is the key arbitrary-witness reduction used by the raw AIR
challenge argument. -/
theorem forged_claim_unbalanced (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : FixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hforged : S31.Functional.SSATextBytes.denotation sourceBytes input ≠
      some claimed) :
    ¬ balanced (nativeRows trace) trace.externalUses trace.externalYields := by
  intro hbalance
  exact hforged (balanced_implies_source_claim trace sourceBytes normalizedBytes
    certificate totalAddRows input claimed h hbalance)

/-- Source-extracted native Gate residuals for this fixed decoded trace. -/
noncomputable def acceptingChallengePairs (trace : Trace 9) :
    Finset (GateSecure × GateSecure) := by
  classical
  exact Finset.univ.filter fun pair =>
    nativeRawInteractionAccepts 9 trace.prev (row trace)
      trace.externalUses trace.externalYields pair.1 pair.2

theorem accepting_pairs_eq_raw (trace : Trace 9) :
    acceptingChallengePairs trace =
      rawAcceptingPairs 9 trace.prev (row trace)
        trace.externalUses trace.externalYields := by
  classical
  ext pair
  simp only [acceptingChallengePairs, rawAcceptingPairs,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact native_raw_accepts_iff 9 trace.prev (row trace)
    trace.externalUses trace.externalYields pair.1 pair.2

/-- Every accepting ideal challenge pair is exceptional even before ruling
out a false claim. The zero-denominator branch includes rows with zero output
multiplicity, whose AIR equation otherwise has a vacuous denominator. -/
theorem accepting_pairs_exceptional (trace : Trace 9) :
    acceptingChallengePairs trace ⊆
      exceptionalPairs (nativeRows trace)
        trace.externalUses trace.externalYields := by
  rw [accepting_pairs_eq_raw]
  exact raw_accepting_pairs_subset_exceptional 9 trace.prev (row trace)
    trace.externalUses trace.externalYields

set_option maxHeartbeats 500000 in
/-- The installed extension bytecode, evaluated at every actual decoded
row, is sufficient to put a challenge in the native raw accepting set.
This uses the proved bytecode-to-Gate evaluator identity for the complete
512-row trace. The zero outputs and public closure are still proof-acceptance
premises; they are not inferred from a Boolean verifier return value. -/
theorem installed_bytecode_pair_accepts (trace : Trace 9)
    (alpha z : GateSecure)
    (hprev : trace.prev =
      S31.Gadgets.Air.DirectGateOodsMask.directPrevious512)
    (hBytecodeOutputs : ∀ index : Fin 512,
      let outputs := bytecodeLogup
        (liftCells
          (S31.Gadgets.Air.DirectGateEvaluatorCells.fromTrace trace index))
        alpha z (trace.claimed / (2 ^ 9 : Nat))
      trace.airPair index = outputs.1 ∧ trace.airLast index = outputs.2)
    (hAuthenticatedRows : ∀ index : Fin 512,
      trace.airPair index = 0 ∧ trace.airLast index = 0)
    (hPublicClosure : trace.claimed +
      S31.Gadgets.Air.GateLogUpBridge.productionReciprocalSum
        trace.externalUses alpha z -
      S31.Gadgets.Air.GateLogUpBridge.productionReciprocalSum
        trace.externalYields alpha z = 0) :
    (alpha, z) ∈ acceptingChallengePairs trace := by
  classical
  have hraw := bytecode_outputs_to_raw_accepts trace alpha z hprev
    hBytecodeOutputs hAuthenticatedRows hPublicClosure
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  apply (native_raw_accepts_iff 9 trace.prev (row trace)
    trace.externalUses trace.externalYields alpha z).mpr
  simpa only [hprev] using hraw

set_option maxRecDepth 4096 in
/-- The raw Gate AIR challenge bound applies to every fixed unbalanced
decoded 512-row trace, independently of which accepted source grammar
produced its positional certificate. -/
theorem unbalanced_accepting_pairs_card_le (trace : Trace 9)
    (hwrong : ¬ balanced (nativeRows trace)
      trace.externalUses trace.externalYields)
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
  have hden : (denominatorEvents (nativeRows trace)).length = 1536 := by
    rw [denominator_events_length]
    simp only [nativeRows, List.length_ofFn]
    norm_num
  rw [accepting_pairs_eq_raw]
  have hbound := raw_false_acceptance_card_le 9 trace.prev (row trace)
    trace.externalUses trace.externalYields hcanonical huses hyields hwrong
  simpa only [hden] using hbound

set_option maxRecDepth 4096 in
/-- With canonical Gate addresses and event counts, an arbitrary fixed trace
for a false public claim passes the modeled source-extracted raw Gate AIR on
at most `(5s² + 2s + 1536) · |QM31|` ideal challenge pairs. Here `s` is the
number of distinct use/yield tuples. The challenge space has `|QM31|²`
pairs. These are *fixed-trace* algebraic odds, not a native STARK theorem. -/
theorem forged_claim_accepting_pairs_card_le (trace : Trace 9)
    (sourceBytes normalizedBytes : List Nat) (certificate : Certificate)
    (totalAddRows : Nat) (input claimed : Lanes)
    (h : FixedTraceContext trace sourceBytes normalizedBytes certificate
      totalAddRows input claimed)
    (hforged : S31.Functional.SSATextBytes.denotation sourceBytes input ≠
      some claimed)
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
  have hwrong := forged_claim_unbalanced trace sourceBytes normalizedBytes
    certificate totalAddRows input claimed h hforged
  exact unbalanced_accepting_pairs_card_le trace hwrong
    hcanonical huses hyields

end S31.Functional.Correspondence.RawGateSoundness
