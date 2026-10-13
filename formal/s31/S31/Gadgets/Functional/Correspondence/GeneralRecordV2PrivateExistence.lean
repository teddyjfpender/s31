import S31.Gadgets.Functional.Correspondence.GeneralRecordV2PhysicalSourceRows
import S31.Gadgets.Functional.SSAGeneralDecodedTraceBridge
import S31.Gadgets.Air.GateWireMap

/-!
Conditional private-witness extraction for the bounded record-v2 scalar Gate
fragment. The private input words are read from one coherent authenticated
address-to-value map; no private assignment is provided to the theorem.

This is an ideal trace statement. Its explicit premises include canonical
scalar input cells, a source-graph totality fact, public input/output pins,
fixed-row identity, local AIR roots and the coherent Gate wire map. Native
PCS/FRI/Fiat–Shamir acceptance does not establish those premises here.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2PrivateExistence

open S31.Functional.Correspondence.GeneralRecordV2SourceCorrespondence
open S31.Functional.Correspondence.GeneralRecordV2ProgramAdmission
open S31.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence
open S31.Functional.Correspondence.GeneralRecordV2ValueCorrespondence
open S31.Functional.Correspondence.GeneralRecordV2PhysicalSourceRows
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAAirColumnCells
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Gadgets.Air.DecodedDirectGateTrace
open S31.Functional.SSAGeneralDecodedTraceBridge
open S31.Gadgets.Air.DirectGateEvaluatorCells
open S31.Gadgets.Air.GeneratedDirectGateBytecodeArithmetic

/-- The canonical M31 word at a Gate address. The other three QM31
coordinates must be zero at source input addresses, checked separately. -/
def wordAt (wire : Nat → Quad) (address : Nat) : Nat :=
  (wire address).a.val

def inputWords (source : Source) (wire : Nat → Quad) : List Nat :=
  (inputWires source).map (wordAt wire ∘ sourceAddress source)

/-- Recover private input fields from the observed Gate values. Public fields
and claimed outputs stay exactly those in the public statement. -/
def recoveredAssignment (source : Source) (wire : Nat → Quad)
    (publicInputs publicOutputs : S31.RawValues) : S31.Assignment :=
  { publicInputs := publicInputs
    privateInputs := ((sourceProgram source).inputs.filter
      (fun i => i.visibility == .private)).map fun i =>
        (i.name, [wordAt wire (sourceAddress source i.name)])
    publicOutputs := publicOutputs }

/-- The trace input slice is scalar, so its canonical coordinate gives the
entire input value at every source input address. -/
def ScalarInputs (source : Source) (wire : Nat → Quad) : Prop :=
  ∀ name ∈ inputWires source,
    wire (sourceAddress source name) =
      scalarCell (wordAt wire (sourceAddress source name))

private theorem input_matches (source : Source) (wire : Nat → Quad)
    (hscalar : ScalarInputs source wire) :
    Matches (sourceAddress source) wire
      (List.zip (inputWires source) (inputWords source wire)) := by
  have lookup_map (names : List String)
      (hscalarNames : ∀ name ∈ names,
        wire (sourceAddress source name) =
          scalarCell (wordAt wire (sourceAddress source name))) :
      Matches (sourceAddress source) wire
        (List.zip names (names.map (wordAt wire ∘ sourceAddress source))) := by
    induction names with
    | nil =>
        intro name word hlookup
        simp [lookupValue] at hlookup
    | cons first rest ih =>
        intro name word hlookup
        by_cases h : first = name
        · subst name
          have hword : word = wordAt wire (sourceAddress source first) := by
            simpa [lookupValue] using hlookup.symm
          rw [hword]
          exact hscalarNames first (by simp)
        · have htail : lookupValue
              (List.zip rest (rest.map (wordAt wire ∘ sourceAddress source)))
              name = some word := by
            simpa [lookupValue, h] using hlookup
          exact ih (by
            intro next hmem
            exact hscalarNames next (by simp [hmem])) name word htail
  intro name word hlookup
  exact lookup_map (inputWires source) hscalar name word
    (by simpa [inputWords] using hlookup)

/-- Exact multiset balance and unique production make one positive-yield
decoded row a circuit gate on the shared address map. -/
theorem trace_cell_accept (trace : Trace 9)
    (cell : ColumnCell)
    (hfixed : fixedMatches trace cell)
    (hpositive : 0 < cell.mults)
    (hroots : allArithmeticRootsZero trace)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields)
    (hunique : uniqueProduced
      (allYields (nativeRows trace) trace.externalYields)) :
    cellAccepts cell
        (producedWire (allYields (nativeRows trace) trace.externalYields)) := by
  obtain ⟨i, hi, hflags, hin0, hin1, hout, hmult⟩ :=
    hfixed
  have hrow : row trace i ∈ nativeRows trace := by
    exact List.mem_ofFn.mpr ⟨i, rfl⟩
  have hzero : accepts (row trace i).flags (row trace i).in0
      (row trace i).in1 (row trace i).output := by
    have hpoly : bytecodeArithmetic (fromTrace trace i) =
        residuals (row trace i).flags (row trace i).in0
          (row trace i).in1 (row trace i).output := by
      rw [bytecode_arithmetic_eq, arithmetic_from_trace]
      exact S31.Gadgets.Air.NativeQm31AirProof.native_residuals_eq
        (row trace i).flags (row trace i).in0
        (row trace i).in1 (row trace i).output
    intro residual hmem
    exact hroots i residual (hpoly ▸ hmem)
  have honWire := row_accepts_on_wire (nativeRows trace)
    trace.externalUses trace.externalYields hbalance hunique
    (row trace i) hrow (by simpa only [hmult] using hpositive)
    hzero
  simpa only [cellAccepts, hflags, hin0, hin1, hout] using honWire

/-- A live source graph has a positive-multiplicity exported cell for each
arithmetic node. Dead nodes require a separate liveness/pruning theorem;
the positive condition is deliberately not imposed on all 512 rows. -/
def LiveSourceCells (source : Source) (cells : List ColumnCell) : Prop :=
  ∀ node ∈ source.nodes, ∃ cell ∈ cells,
    FixedSourceCell source node cell ∧ 0 < cell.mults

theorem trace_live_source_cells (source : Source) (trace : Trace 9)
    (cells : List ColumnCell)
    (hfixed : ∀ cell ∈ cells, fixedMatches trace cell)
    (hlive : LiveSourceCells source cells)
    (hroots : allArithmeticRootsZero trace)
    (hbalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields)
    (hunique : uniqueProduced
      (allYields (nativeRows trace) trace.externalYields)) :
    SourceCells source.nodes (sourceAddress source) cells
      (producedWire (allYields (nativeRows trace) trace.externalYields)) := by
  intro node hnode
  obtain ⟨cell, hcell, hshape, hpositive⟩ := hlive node hnode
  obtain ⟨hadd, hsub, hmul, hpoint, horient, hout⟩ := hshape
  exact ⟨cell, hcell, hadd, hsub, hmul, hpoint, horient, hout,
    trace_cell_accept trace cell (hfixed cell hcell) hpositive
      hroots hbalance hunique⟩

/-- Operational totality of the independently parsed source graph. The
source parser resolves operands before use; a separate parser invariant must
establish this predicate for every admitted source. It says nothing about the
values of any public output. -/
def SourceTotal (source : Source) : Prop :=
  ∀ words : List Nat,
    words.length = (inputWires source).length →
    (∀ word ∈ words, word < S31.modulus) →
    ∃ values,
      source.nodes.foldlM evalNode (List.zip (inputWires source) words) =
        some values ∧
      ∀ name ∈ (resultWires source).eraseDups,
        ∃ word, lookupValue values name = some word

private def Covered (names : List String)
    (values : List (String × Nat)) : Prop :=
  ∀ name ∈ names, ∃ word, lookupValue values name = some word

private theorem initial_covered (names : List String) (words : List Nat)
    (hlen : names.length = words.length) :
    Covered names (List.zip names words) := by
  induction names generalizing words with
  | nil => simp [Covered]
  | cons first rest ih =>
      cases words with
      | nil => simp at hlen
      | cons word remaining =>
          have htail : rest.length = remaining.length := by
            simpa using hlen
          intro name hmem
          rcases List.mem_cons.mp hmem with h | h
          · subst name
            exact ⟨word, by simp [lookupValue]⟩
          · obtain ⟨found, hfound⟩ := ih remaining htail name h
            by_cases heq : first = name
            · subst name
              exact ⟨word, by simp [lookupValue]⟩
            · exact ⟨found, by simpa [lookupValue, heq] using hfound⟩

private theorem checked_nodes_run (nodes : List Arithmetic)
    (names : List String) (values : List (String × Nat))
    (finalNames : List String)
    (hcovered : Covered names values)
    (hcheck : checkNodes nodes names = some finalNames) :
    ∃ finalValues,
      nodes.foldlM evalNode values = some finalValues ∧
      Covered finalNames finalValues := by
  induction nodes generalizing names values with
  | nil =>
      have hnames : names = finalNames := by simpa [checkNodes] using hcheck
      subst finalNames
      exact ⟨values, by simp, hcovered⟩
  | cons node rest ih =>
      simp [checkNodes] at hcheck
      have hoperands : names.contains node.lhs.wire = true ∧
          names.contains node.rhs.wire = true := by
        simpa only [List.contains_iff_mem] using hcheck.1
      obtain ⟨lhs, hleft⟩ := hcovered node.lhs.wire
        (List.contains_iff_mem.mp hoperands.1)
      obtain ⟨rhs, hright⟩ := hcovered node.rhs.wire
        (List.contains_iff_mem.mp hoperands.2)
      let output := if node.op == "+" then (lhs + rhs) % S31.modulus
        else (lhs * rhs) % S31.modulus
      have hstep : evalNode values node =
          some ((node.name, output) :: values) := by
        simp [evalNode, hleft, hright, output]
      have hnextCovered : Covered (node.name :: names)
          ((node.name, output) :: values) := by
        intro name hmem
        by_cases heq : name = node.name
        · subst name
          exact ⟨output, by simp [lookupValue]⟩
        · have hold : name ∈ names := by
            simpa [heq] using hmem
          obtain ⟨word, hword⟩ := hcovered name hold
          have hne : node.name ≠ name := Ne.symm heq
          exact ⟨word, by simpa [lookupValue, hne] using hword⟩
      have hrest : checkNodes rest (node.name :: names) =
          some finalNames := hcheck.2
      obtain ⟨finalValues, hrun, hfinal⟩ :=
        ih (node.name :: names) ((node.name, output) :: values)
          hnextCovered hrest
      exact ⟨finalValues,
        by simpa [List.foldlM_cons, hstep] using hrun, hfinal⟩

/-- The executable name pass discharges source-run totality for every
canonical input vector. The proof is independent of the typed evaluator and
does not inspect public output values. -/
theorem checked_topology_total (source : Source)
    (hcheck : checkSourceTopology source = true) :
    SourceTotal source := by
  unfold checkSourceTopology at hcheck
  cases hnames : checkNodes source.nodes (inputWires source) with
  | none => simp [hnames] at hcheck
  | some finalNames =>
      intro words hlen _
      obtain ⟨finalValues, hrun, hcovered⟩ :=
        checked_nodes_run source.nodes (inputWires source)
          (List.zip (inputWires source) words) finalNames
          (initial_covered _ _ hlen.symm) hnames
      refine ⟨finalValues, hrun, ?_⟩
      intro name hmem
      have hmember : name ∈ resultWires source := by
        simpa only [List.mem_eraseDups] using hmem
      have hin : name ∈ finalNames := by
        have hh : ∀ x ∈ resultWires source, x ∈ finalNames := by
          simpa [hnames] using hcheck
        exact hh name hmember
      exact hcovered name hin

/-- The public record result must be the value of the authenticated Gate
address. Aliased fields share the same address and appear only once in the
normalized public-output claim. -/
def PublicOutputPins (source : Source) (wire : Nat → Quad)
    (publicOutputs : S31.RawValues) : Prop :=
  ∀ name ∈ (resultWires source).eraseDups, ∀ word,
    wire (sourceAddress source name) = scalarCell word →
    S31.assigned publicOutputs name ⟨.m31, 1⟩ = .ok (singleton word)

private theorem canonical_wire_words (source : Source)
    (wire : Nat → Quad) :
    (inputWords source wire).length = (inputWires source).length ∧
    ∀ word ∈ inputWords source wire, word < S31.modulus := by
  constructor
  · simp [inputWords]
  · intro word hmem
    obtain ⟨name, _, rfl⟩ := List.mem_map.mp hmem
    exact (wire (sourceAddress source name)).a.val_lt

private theorem output_claims_from_pins (source : Source)
    (cells : List ColumnCell) (wire : Nat → Quad)
    (values : List (String × Nat)) (publicOutputs : S31.RawValues)
    (hinput : Matches (sourceAddress source) wire
      (List.zip (inputWires source) (inputWords source wire)))
    (hfold : source.nodes.foldlM evalNode
      (List.zip (inputWires source) (inputWords source wire)) = some values)
    (hcells : SourceCells source.nodes (sourceAddress source) cells wire)
    (hresults : ∀ name ∈ (resultWires source).eraseDups,
      ∃ word, lookupValue values name = some word)
    (hpins : PublicOutputPins source wire publicOutputs) :
    checkOutputClaims source values
      { publicInputs := [], privateInputs := [],
        publicOutputs := publicOutputs } = true := by
  have hmatch := source_fold_physical_cells source.nodes
    (sourceAddress source) cells wire _ values hinput hcells hfold
  apply List.all_eq_true.mpr
  intro name hmem
  obtain ⟨word, hlookup⟩ := hresults name hmem
  simpa [checkOutputClaims, hlookup] using
    hpins name hmem word (hmatch name word hlookup)

/-- From an arbitrary decoded Gate trace meeting the explicit fixed-cell,
AIR, lookup and public-IO premises, recover a private source assignment whose
actual normalized `Program.evaluate` accepts the public claim. The checked
fixed-cell layout is supplied; its commitment/root binding remains external.
`LiveSourceCells` requires every arithmetic node to produce a positive Gate
event, so a dead-node/liveness theorem is still needed for all parsed sources.
No private assignment or successful source run is supplied by the caller. -/
theorem private_assignment_exists
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : Static sourceBytes treeBytes relationBytes abiBytes)
    (trace : Trace 9) (cells : List ColumnCell)
    (publicInputs publicOutputs : S31.RawValues)
    (claimed : List S31.M31)
    (hcheckedFixedCellLayout :
      checkFixedSourceCells accepted.checked.source cells = true)
    (hfixedTrace : ∀ cell ∈ cells, fixedMatches trace cell)
    (hlive : LiveSourceCells accepted.checked.source cells)
    (hlocalAir : allArithmeticRootsZero trace)
    (hlookupBalance : balanced (nativeRows trace)
      trace.externalUses trace.externalYields)
    (hunique : uniqueProduced
      (allYields (nativeRows trace) trace.externalYields))
    (hscalarInputs : ScalarInputs accepted.checked.source
      (producedWire (allYields (nativeRows trace) trace.externalYields)))
    (hpublicInputs : checkInputAlignment accepted.checked.source
      (recoveredAssignment accepted.checked.source
        (producedWire (allYields (nativeRows trace) trace.externalYields))
        publicInputs publicOutputs)
      (inputWords accepted.checked.source
        (producedWire (allYields (nativeRows trace) trace.externalYields))) = true)
    (hpublicOutputs : PublicOutputPins accepted.checked.source
      (producedWire (allYields (nativeRows trace) trace.externalYields))
      publicOutputs)
    (hclaimed : accepted.program.claimedWords
      (recoveredAssignment accepted.checked.source
        (producedWire (allYields (nativeRows trace) trace.externalYields))
        publicInputs publicOutputs) = .ok claimed) :
    cells.length = 512 ∧
    ∃ assignment : S31.Assignment,
      assignment.publicInputs = publicInputs ∧
      assignment.publicOutputs = publicOutputs ∧
      accepted.program.evaluate assignment = .ok claimed := by
  let source := accepted.checked.source
  let wire := producedWire (allYields (nativeRows trace) trace.externalYields)
  let assignment := recoveredAssignment source wire publicInputs publicOutputs
  have hcanonical := canonical_wire_words source wire
  obtain ⟨values, hfold, hresults⟩ :=
    checked_topology_total source accepted.topology
      (inputWords source wire) hcanonical.1 hcanonical.2
  have hcells : SourceCells source.nodes (sourceAddress source) cells wire :=
    trace_live_source_cells source trace cells hfixedTrace hlive hlocalAir
      hlookupBalance hunique
  have hpin : Matches (sourceAddress source) wire
      (List.zip (inputWires source) (inputWords source wire)) :=
    input_matches source wire hscalarInputs
  have houtput : checkOutputClaims source values assignment = true := by
    exact output_claims_from_pins source cells wire values publicOutputs
      hpin hfold hcells hresults hpublicOutputs
  refine ⟨(checked_fixed_source_cells source cells hcheckedFixedCellLayout).1,
    assignment, rfl, rfl, ?_⟩
  exact source_fold_program_evaluate accepted assignment
    (inputWords source wire) values claimed hpublicInputs hfold houtput hclaimed

theorem worked_topology_check :
    checkSourceTopology
      GeneralRecordV2ValueCorrespondence.workedSource = true := by
  decide

private def missingOperandSource : Source :=
  { GeneralRecordV2ValueCorrespondence.workedSource with
    nodes := [⟨"sum", ⟨"unavailable", Lean.Json.null⟩,
      ⟨"_s31_abi_input_2", Lean.Json.null⟩, "+"⟩] }

private def missingResultSource : Source :=
  { GeneralRecordV2ValueCorrespondence.workedSource with
    result := [⟨"left", ⟨"unavailable", Lean.Json.null⟩⟩,
      ⟨"right", ⟨"sum", Lean.Json.null⟩⟩] }

theorem unavailable_operand_rejected :
    checkSourceTopology missingOperandSource = false := by
  decide

theorem unavailable_result_rejected :
    checkSourceTopology missingResultSource = false := by
  decide

end S31.Functional.Correspondence.GeneralRecordV2PrivateExistence
