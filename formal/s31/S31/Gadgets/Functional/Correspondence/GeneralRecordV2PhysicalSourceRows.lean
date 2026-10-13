import S31.Gadgets.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence
import S31.Gadgets.Functional.SSANativePolynomialRows

/-!
The source-owned arithmetic slice of a bounded record-v2 direct-Gate trace.
The exact-byte source checker supplies the arithmetic list. An independent
fixed-column check must identify its cells in the native 512-row layout, and
the Gate lookup/commitment protocol must supply one coherent address-to-value
map. These obligations remain explicit hypotheses, not conclusions of this
value-level theorem.
-/

namespace S31.Functional.Correspondence.GeneralRecordV2PhysicalSourceRows

open S31.Functional.Correspondence.GeneralRecordV2SourceCorrespondence
open S31.Functional.Correspondence.GeneralRecordV2EvaluateCorrespondence
open S31.Functional.SSANativePolynomialRows
open S31.Functional.SSAAirColumnCells
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Packed

set_option maxRecDepth 4096

def scalarCell (word : Nat) : Quad := base (word : F)

def Matches (address : String → Nat) (wire : Nat → Quad)
    (values : List (String × Nat)) : Prop :=
  ∀ name word, lookupValue values name = some word →
    wire (address name) = scalarCell word

/-- A checked source instruction has a native fixed cell with the exact
selector and operand addresses. `cellAccepts` is the nine production-style
local polynomial residuals evaluated on one coherent Gate wire map. -/
def SourceCells (nodes : List Arithmetic) (address : String → Nat)
    (cells : List ColumnCell) (wire : Nat → Quad) : Prop :=
  ∀ node ∈ nodes, ∃ cell ∈ cells,
    cell.addFlag = (if node.op == "+" then 1 else 0) ∧
    cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
    cell.pointwiseMulFlag = (if node.op == "+" then 0 else 1) ∧
    cell.in0 = address node.lhs.wire ∧
    cell.in1 = address node.rhs.wire ∧
    cell.out = address node.name ∧
    cellAccepts cell wire

/-- Candidate one-lane direct-Gate addresses, independently reconstructed
from the record source. The first input uses address 11; the first pack also
reserves addresses 12 and 13; later inputs and arithmetic producers are
allocated consecutively. An emitted fixed-column export must pass
`checkFixedSourceCells` before these addresses can be used as a native join. -/
def sourceAddress (source : Source) (name : String) : Nat :=
  match (inputWires source).idxOf? name with
  | some 0 => 11
  | some index => 13 + index
  | none =>
      match (source.nodes.map Arithmetic.name).idxOf? name with
      | some index => 13 + (inputWires source).length + index
      | none => 0

def FixedSourceCell (source : Source) (node : Arithmetic)
    (cell : ColumnCell) : Prop :=
  cell.addFlag = (if node.op == "+" then 1 else 0) ∧
  cell.subFlag = 0 ∧ cell.mulFlag = 0 ∧
  cell.pointwiseMulFlag = (if node.op == "+" then 0 else 1) ∧
  cell.in0 = sourceAddress source node.lhs.wire ∧
  cell.in1 = sourceAddress source node.rhs.wire ∧
  cell.out = sourceAddress source node.name

instance (source : Source) (node : Arithmetic) (cell : ColumnCell) :
    Decidable (FixedSourceCell source node cell) := by
  unfold FixedSourceCell
  infer_instance

/-- Read only the exported fixed columns. The complete row range and unique
physical positions are checked alongside each source-owned opcode/address
cell. Native fixed-root binding remains a separate assumption. -/
def checkFixedSourceCells (source : Source) (cells : List ColumnCell) : Bool :=
  decide (cells.length = 512 ∧
    (cells.map ColumnCell.traceRow).Nodup ∧
    ∀ cell ∈ cells, cell.traceRow < 512) &&
  source.nodes.all (fun node =>
    cells.any (fun cell => decide (FixedSourceCell source node cell)))

theorem checked_fixed_source_cells (source : Source)
    (cells : List ColumnCell)
    (h : checkFixedSourceCells source cells = true) :
    cells.length = 512 ∧
    (cells.map ColumnCell.traceRow).Nodup ∧
    (∀ cell ∈ cells, cell.traceRow < 512) ∧
    (∀ node ∈ source.nodes,
      ∃ cell ∈ cells, FixedSourceCell source node cell) := by
  unfold checkFixedSourceCells at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  refine ⟨h.1.1, h.1.2.1, h.1.2.2, ?_⟩
  intro node hnode
  have hfound := (List.all_eq_true.mp h.2) node hnode
  obtain ⟨cell, hcell, hmatch⟩ := List.any_eq_true.mp hfound
  exact ⟨cell, hcell, of_decide_eq_true hmatch⟩

theorem checked_cells_with_roots (source : Source)
    (cells : List ColumnCell) (wire : Nat → Quad)
    (hfixed : checkFixedSourceCells source cells = true)
    (hroots : ∀ cell ∈ cells, cellAccepts cell wire) :
    SourceCells source.nodes (sourceAddress source) cells wire := by
  intro node hnode
  obtain ⟨cell, hcell, hflags0, hflags1, hflags2, hflags3,
    hin0, hin1, hout⟩ :=
    (checked_fixed_source_cells source cells hfixed).2.2.2
      node hnode
  exact ⟨cell, hcell, hflags0, hflags1, hflags2, hflags3,
    hin0, hin1, hout, hroots cell hcell⟩

private theorem scalar_operation (node : Arithmetic) (lhs rhs : Nat) :
    S31.Gadgets.Air.Qm31Ops.evaluate (s31Op (node.op != "+"))
      (scalarCell lhs) (scalarCell rhs) =
      scalarCell (if node.op == "+" then (lhs + rhs) % S31.modulus
        else (lhs * rhs) % S31.modulus) := by
  by_cases heq : node.op = "+"
  · simp [scalarCell, s31Op, heq, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.add, base, S31.modulus]
    simpa only [S31.modulus, RiscvRefinement.M31.modulus,
      Nat.cast_add] using
      (ZMod.natCast_mod (lhs + rhs) 2147483647).symm
  · simp [scalarCell, s31Op, heq, S31.Gadgets.Air.Qm31Ops.evaluate,
      S31.Gadgets.Packed.pointwise, base, S31.modulus]
    simpa only [S31.modulus, RiscvRefinement.M31.modulus,
      Nat.cast_mul] using
      (ZMod.natCast_mod (lhs * rhs) 2147483647).symm

private theorem checked_cell_output (node : Arithmetic)
    (address : String → Nat) (wire : Nat → Quad) (cell : ColumnCell)
    (lhs rhs : Nat)
    (hflags0 : cell.addFlag = if node.op == "+" then 1 else 0)
    (hflags1 : cell.subFlag = 0) (hflags2 : cell.mulFlag = 0)
    (hflags3 : cell.pointwiseMulFlag = if node.op == "+" then 0 else 1)
    (hin0 : cell.in0 = address node.lhs.wire)
    (hin1 : cell.in1 = address node.rhs.wire)
    (hout : cell.out = address node.name)
    (hair : cellAccepts cell wire)
    (hleft : wire (address node.lhs.wire) = scalarCell lhs)
    (hright : wire (address node.rhs.wire) = scalarCell rhs) :
    wire (address node.name) =
      scalarCell (if node.op == "+" then (lhs + rhs) % S31.modulus
        else (lhs * rhs) % S31.modulus) := by
  have hflags : cellFlags cell = encode (s31Op (node.op != "+")) := by
    by_cases heq : node.op = "+"
    · simp [cellFlags, s31Op, heq, encode, hflags0, hflags1,
        hflags2, hflags3]
    · simp [cellFlags, s31Op, heq, encode, hflags0, hflags1,
        hflags2, hflags3]
  have hrow : accepts (encode (s31Op (node.op != "+")))
      (scalarCell lhs) (scalarCell rhs)
      (wire (address node.name)) := by
    simpa only [cellAccepts, hflags, hin0, hin1, hout,
      hleft, hright] using hair
  exact ((accepts_encoded _ _ _ _).mp hrow).trans
    (scalar_operation node lhs rhs)

/-- Every successful independent source fold is reflected in all of its
source-owned physical Gate cells. The cells can be any observed 512-row slice;
the theorem does not assume the honest witness writer produced their values.
Native fixed-column and lookup authentication are the `SourceCells` and
coherent `wire` premises. -/
theorem source_fold_physical_cells (nodes : List Arithmetic)
    (address : String → Nat) (cells : List ColumnCell)
    (wire : Nat → Quad) (initial final : List (String × Nat))
    (hinput : Matches address wire initial)
    (hcells : SourceCells nodes address cells wire)
    (hrun : nodes.foldlM evalNode initial = some final) :
    Matches address wire final := by
  induction nodes generalizing initial with
  | nil =>
      have heq : initial = final := by
        simpa [List.foldlM_nil] using hrun
      cases heq
      exact hinput
  | cons node rest ih =>
      cases hleft : lookupValue initial node.lhs.wire with
      | none => simp [List.foldlM_cons, evalNode, hleft] at hrun
      | some lhs =>
          cases hright : lookupValue initial node.rhs.wire with
          | none => simp [List.foldlM_cons, evalNode, hleft, hright] at hrun
          | some rhs =>
              let output := if node.op == "+" then (lhs + rhs) % S31.modulus
                else (lhs * rhs) % S31.modulus
              obtain ⟨cell, _, hflags0, hflags1, hflags2, hflags3,
                hin0, hin1, hout, hair⟩ := hcells node (by simp)
              have houtput : wire (address node.name) = scalarCell output :=
                checked_cell_output node address wire cell lhs rhs hflags0
                  hflags1 hflags2 hflags3 hin0 hin1 hout hair
                  (hinput _ _ hleft) (hinput _ _ hright)
              have hnext : Matches address wire ((node.name, output) :: initial) := by
                intro name word hlookup
                by_cases hname : name = node.name
                · subst name
                  have hword : word = output := by
                    simpa [lookupValue] using hlookup.symm
                  subst word
                  exact houtput
                · have hold : lookupValue initial name = some word := by
                    have hne : node.name ≠ name := Ne.symm hname
                    simpa [lookupValue, hne] using hlookup
                  exact hinput name word hold
              have htailCells : SourceCells rest address cells wire := by
                intro later hmem
                exact hcells later (by simp [hmem])
              have htail : rest.foldlM evalNode
                  ((node.name, output) :: initial) = some final := by
                simpa [List.foldlM_cons, evalNode, hleft, hright,
                  output] using hrun
              exact ih _ hnext htailCells htail

private theorem result_words_match (address : String → Nat)
    (wire : Nat → Quad) (values : List (String × Nat))
    (names : List String) (words : List Nat)
    (hmatch : Matches address wire values)
    (hresult : names.mapM (lookupValue values) = some words) :
    List.Forall₂ (fun name word => wire (address name) = scalarCell word)
      names words := by
  induction names generalizing words with
  | nil =>
      have hnil : words = [] := by simpa using hresult.symm
      subst words
      exact .nil
  | cons name rest ih =>
      cases hword : lookupValue values name with
      | none => simp [List.mapM_cons, hword] at hresult
      | some word =>
          cases htail : rest.mapM (lookupValue values) with
          | none => simp [List.mapM_cons, hword, htail] at hresult
          | some tail =>
              have heq : word :: tail = words := by
                simpa [List.mapM_cons, hword, htail] using hresult
              cases heq
              exact .cons (hmatch name word hword) (ih _ htail)

/-- A full source run plus verified source-owned native cells fixes every
ordered record result, including repeated aliases. The input pin is an
explicit private/public Gate-join premise; the fixed-root and main-trace PCS
binding are not inferred from a Boolean native verifier result. -/
theorem source_run_physical_results (source : Source)
    (inputWords results : List Nat) (cells : List ColumnCell)
    (wire : Nat → Quad)
    (hsource : GeneralRecordV2SourceCorrespondence.evaluate
      source inputWords = some results)
    (hpin : Matches (sourceAddress source) wire
      (List.zip (inputWires source) inputWords))
    (hfixed : checkFixedSourceCells source cells = true)
    (hroots : ∀ cell ∈ cells, cellAccepts cell wire) :
    List.Forall₂ (fun name word =>
      wire (sourceAddress source name) = scalarCell word)
      (resultWires source) results := by
  unfold GeneralRecordV2SourceCorrespondence.evaluate at hsource
  by_cases hcanonical :
      inputWords.length = (inputWires source).length ∧
      ∀ word ∈ inputWords, word < S31.modulus
  · cases hfold : source.nodes.foldlM evalNode
        (List.zip (inputWires source) inputWords) with
    | none => simp [hcanonical, hfold] at hsource
    | some values =>
        have hresult : (resultWires source).mapM
            (lookupValue values) = some results := by
          simp [hcanonical, hfold] at hsource
          exact hsource.2
        have hmatch := source_fold_physical_cells source.nodes
          (sourceAddress source) cells wire _ values hpin
          (checked_cells_with_roots source cells wire hfixed hroots) hfold
        exact result_words_match _ _ _ _ _ hmatch hresult
  · simp [hcanonical] at hsource

/-- Compose exact-source static admission, independent scalar execution,
the actual typed public-word evaluator, and the modeled source-owned native
Gate cells. The input pin, local roots, fixed-column export, and address
coherence are explicit obligations for an emitted proof. In particular this
theorem does not turn `Program.evaluate` into an authenticated proof trace. -/
theorem checked_assignment_physical_results
    {sourceBytes : List Nat} {treeBytes relationBytes abiBytes : String}
    (accepted : GeneralRecordV2ProgramAdmission.Static
      sourceBytes treeBytes relationBytes abiBytes)
    (assignment : S31.Assignment) (run : CheckedRun)
    (cells : List ColumnCell) (wire : Nat → Quad)
    (hchecked : checkSourceAssignment accepted assignment = some run)
    (hpin : ∀ inputWords,
      inputWordsFromAssignment accepted.checked.source assignment =
        some inputWords →
      Matches (sourceAddress accepted.checked.source) wire
        (List.zip (inputWires accepted.checked.source) inputWords))
    (hfixed : checkFixedSourceCells accepted.checked.source cells = true)
    (hroots : ∀ cell ∈ cells, cellAccepts cell wire) :
    accepted.program.evaluate assignment = .ok run.claimed ∧
    List.Forall₂ (fun name word =>
      wire (sourceAddress accepted.checked.source name) = scalarCell word)
      (resultWires accepted.checked.source) run.sourceResults := by
  obtain ⟨inputWords, hwords, hsource, htyped⟩ :=
    checked_source_assignment_evaluate accepted assignment run hchecked
  exact ⟨htyped,
    source_run_physical_results accepted.checked.source inputWords
      run.sourceResults cells wire hsource (hpin inputWords hwords)
      hfixed hroots⟩

/-- The illustrative public/private two-field program allocates one scalar
Gate wire for each field and one fresh wire per source arithmetic node. -/
theorem worked_source_addresses :
    let source := GeneralRecordV2ValueCorrespondence.workedSource
    (inputWires source).map (sourceAddress source) = [11, 14, 15, 16] ∧
    (source.nodes.map Arithmetic.name).map (sourceAddress source) =
      [17, 18] := by
  decide

end S31.Functional.Correspondence.GeneralRecordV2PhysicalSourceRows
