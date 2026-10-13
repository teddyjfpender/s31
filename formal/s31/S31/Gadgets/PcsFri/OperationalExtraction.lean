import S31.Gadgets.PcsFri.RawLayerRefinement

/-!
The S31 native capture admission check replays raw query positions, queried
values, reconstructed subsets, folds, and the terminal polynomial. This module
separates those operational obligations from the Merkle oracle-equality
obligation and proves their composition for any finite layer schedule.

The source-pinned Zig admission check is not compiled into Lean. In particular,
the implication from a successful Zig call to `operationalAccepts` remains an
explicit semantic extraction obligation. Merkle binding remains separate.
-/

namespace S31.Gadgets.PcsFri.OperationalExtraction

open S31.Gadgets.PcsFri.QueryAndTranscript
open S31.Gadgets.PcsFri.LayerAcceptance
open S31.Gadgets.PcsFri.RawLayerRefinement

variable {F : Type*}

/-- Current-value placement and next-value fold for each raw slot, exactly the
noncryptographic layer properties checked by capture admission. -/
def operationalLayer (raw : List Nat) (current : Nat → F)
    (layer : Layer F) : Prop :=
  (∀ q ∈ raw,
    current q = layer.opened (foldPosition layer.step q) (q % width layer)) ∧
  (∀ q ∈ raw,
    layer.next (foldPosition layer.step q) =
      layer.fold (fun r => layer.opened (foldPosition layer.step q) r))

/-- Every opened subset entry corresponds to the fixed putative oracle.
Deriving this from accepted Merkle roots needs a separate binding argument. -/
def oracleBoundLayer (raw : List Nat) (layer : Layer F) : Prop :=
  ∀ q ∈ raw, ∀ r < width layer,
    layer.opened (foldPosition layer.step q) r =
      layer.oracle (foldPosition layer.step q * width layer + r)

/-- Operational replay, including the native terminal degree/evaluation gate.
It intentionally contains no Merkle oracle-equality premise. -/
def operationalAccepts (raw : List Nat) (current : Nat → F) :
    List (Layer F) → Terminal F → Prop
  | [], terminal =>
      terminalDegreeOk terminal ∧
      ∀ q ∈ raw, current q = terminalEval terminal q
  | layer :: rest, terminal =>
      operationalLayer raw current layer ∧
      operationalAccepts (raw.map (foldPosition layer.step)) layer.next rest terminal

/-- Merkle binding obligations across the same raw query schedule. -/
def oracleBoundSchedule (raw : List Nat) : List (Layer F) → Prop
  | [] => True
  | layer :: rest =>
      oracleBoundLayer raw layer ∧
      oracleBoundSchedule (raw.map (foldPosition layer.step)) rest

/-- Operational admission plus the explicit oracle-binding premise yields the
raw-slot relation. Neither premise is inferred from native success in Lean. -/
theorem operational_and_binding_implies_rawAccepts
    (raw : List Nat) (current : Nat → F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (hoperational : operationalAccepts raw current layers terminal)
    (hbinding : oracleBoundSchedule raw layers) :
    rawAccepts raw current layers terminal := by
  induction layers generalizing raw current with
  | nil => exact hoperational
  | cons layer rest ih =>
      refine ⟨?_, ih _ _ hoperational.2 hbinding.2⟩
      exact rawLayerChecks_of_components raw current layer
        hoperational.1.1 hbinding.1 hoperational.1.2

/-- Consequently, a successful operational replay and committed-oracle
binding imply the modeled arbitrary-layer acceptance relation. -/
theorem operational_and_binding_implies_accepts
    (raw : List Nat) (current : Nat → F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (hoperational : operationalAccepts raw current layers terminal)
    (hbinding : oracleBoundSchedule raw layers) :
    accepts (normalized raw) current layers terminal := by
  exact rawAccepts_implies_accepts raw current layers terminal
    (operational_and_binding_implies_rawAccepts raw current layers terminal
      hoperational hbinding)

end S31.Gadgets.PcsFri.OperationalExtraction
