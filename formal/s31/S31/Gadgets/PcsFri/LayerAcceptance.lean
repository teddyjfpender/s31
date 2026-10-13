import S31.Gadgets.PcsFri.QueryAndTranscript
import S31.Gadgets.PcsFri.QuerySampling
import Mathlib.Data.Finset.Image

/-!
An explicit native-verifier-to-FRI-IOP proof obligation for any finite layer
schedule. `Layer` represents one putative committed oracle, reconstructed full
subsets, the field fold, and the values passed to the next layer. `accepts`
lists local checks sufficient to build IOP query paths by induction.

The native source and adversarial checks bind the selected verifier path, but
they do not prove that Zig implements this relation. In particular, the
oracle-equality clause of `layerChecks` is a commitment-binding premise, and
`fold` is abstract: the one-butterfly field theorem alone does not prove
arbitrary native folds. The local acceptance relation does not encode native
position bounds; checking those bounds is part of the outstanding
Zig-success-to-`accepts` obligation.

The counting theorem's hypotheses are explicit: `current`, all layer oracles,
openings and transitions, and the terminal polynomial are fixed independently
of the ideal raw query vector; `hproximity` supplies a fixed good set;
`h_native_refines` supplies the still-unproved native semantic bridge outside
Merkle and sampling failure events; `h_merkle` and `h_sampling` bound those
events. The theorem does not establish native proximity soundness or a bit
security claim for the Blake2sM31 channel.
-/

namespace S31.Gadgets.PcsFri.LayerAcceptance

open S31.Gadgets.PcsFri.QueryAndTranscript

variable {F : Type*}

/-- One FRI layer's fold width, putative oracle, reconstructed subsets,
and value passed to the next query set. The field fold remains abstract. -/
structure Layer (F : Type*) where
  step : Nat
  oracle : Nat → F
  opened : Nat → Nat → F
  fold : (Fin (2 ^ step) → F) → F
  next : Nat → F

/-- The terminal degree gate is explicit. `evalAt` is an abstract evaluator;
identifying it with native `LinePoly.evalAtPoint` is a separate obligation. -/
structure Terminal (F : Type*) where
  coefficients : List F
  logDegreeBound : Nat
  evalAt : List F → Nat → F

def terminalDegreeOk (terminal : Terminal F) : Prop :=
  terminal.coefficients.length ≤ 2 ^ terminal.logDegreeBound

def terminalEval (terminal : Terminal F) (q : Nat) : F :=
  terminal.evalAt terminal.coefficients q

def width (layer : Layer F) : Nat := 2 ^ layer.step

def nextQueries (queries : Finset Nat) (layer : Layer F) : Finset Nat :=
  queries.image (foldPosition layer.step)

/-- Local transition for one queried value. The oracle equality is an explicit
premise; no Merkle property is inferred from hash equality. -/
def localTransition (q : Nat) (value : F) (layer : Layer F) : Prop :=
  let p := foldPosition layer.step q
  value = layer.opened p (q % width layer) ∧
  (∀ r < width layer,
    layer.opened p r = layer.oracle (p * width layer + r)) ∧
  layer.next p = layer.fold (fun r => layer.opened p r)

/-- Per-layer checks over the current query set. The second clause needs a
separate Merkle binding argument; it is not inferred from a hash equality. -/
def layerChecks (queries : Finset Nat) (current : Nat → F)
    (layer : Layer F) : Prop :=
  (∀ q ∈ queries,
    current q = layer.opened (foldPosition layer.step q) (q % width layer)) ∧
  (∀ p ∈ nextQueries queries layer, ∀ r < width layer,
    layer.opened p r = layer.oracle (p * width layer + r)) ∧
  (∀ p ∈ nextQueries queries layer,
    layer.next p = layer.fold (fun r => layer.opened p r))

/-- General modeled acceptance relation for all layer counts, including zero
inner layers. The final clause models the last-layer polynomial query check. -/
def accepts (queries : Finset Nat) (current : Nat → F) :
    List (Layer F) → Terminal F → Prop
  | [], terminal =>
      terminalDegreeOk terminal ∧
      ∀ q ∈ queries, current q = terminalEval terminal q
  | layer :: rest, terminal =>
      layerChecks queries current layer ∧
      accepts (nextQueries queries layer) layer.next rest terminal

/-- One raw query's IOP path through all reconstructed subsets. -/
def queryPath (q : Nat) (value : F) :
    List (Layer F) → Terminal F → Prop
  | [], terminal => value = terminalEval terminal q
  | layer :: rest, terminal =>
      let p := foldPosition layer.step q
      localTransition q value layer ∧
      queryPath p (layer.next p) rest terminal

/-- The index reached by following the actual layer schedule. -/
def terminalPosition : List (Layer F) → Nat → Nat
  | [], q => q
  | layer :: rest, q =>
      terminalPosition rest (foldPosition layer.step q)

/-- The value passed along the same sequence of per-layer next-value maps. -/
def terminalValue : List (Layer F) → Nat → F → F
  | [], _, value => value
  | layer :: rest, q, _ =>
      terminalValue rest (foldPosition layer.step q)
        (layer.next (foldPosition layer.step q))

def totalSteps (layers : List (Layer F)) : Nat :=
  (layers.map Layer.step).sum

/-- A one-layer success supplies a local transition at each queried value. -/
theorem layerChecks_localTransition (queries : Finset Nat) (current : Nat → F)
    (layer : Layer F) (hchecks : layerChecks queries current layer)
    (q : Nat) (hq : q ∈ queries) :
    localTransition q (current q) layer := by
  rcases hchecks with ⟨hcurrent, horacle, hfold⟩
  have hp : foldPosition layer.step q ∈ nextQueries queries layer :=
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  exact ⟨hcurrent q hq, horacle _ hp, hfold _ hp⟩

/-- Each accepted next value is a fold of the putative oracle itself. `Fin`
restricts the fold to exactly the subset entries covered by `layerChecks`. -/
theorem layerChecks_next_eq_oracleFold (queries : Finset Nat)
    (current : Nat → F) (layer : Layer F)
    (hchecks : layerChecks queries current layer)
    (p : Nat) (hp : p ∈ nextQueries queries layer) :
    layer.next p = layer.fold (fun r =>
      layer.oracle (p * width layer + r)) := by
  calc
    layer.next p = layer.fold (fun r => layer.opened p r) := hchecks.2.2 p hp
    _ = layer.fold (fun r => layer.oracle (p * width layer + r)) := by
      congr 1
      funext r
      exact hchecks.2.1 p hp r r.isLt

/-- Induction propagates each local transition through arbitrary many layers,
including folds that merge distinct raw queries. -/
theorem accepts_implies_queryPath (queries : Finset Nat) (current : Nat → F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (haccept : accepts queries current layers terminal) :
    ∀ q ∈ queries, queryPath q (current q) layers terminal := by
  induction layers generalizing queries current with
  | nil =>
      intro q hq
      exact haccept.2 q hq
  | cons layer rest ih =>
      rcases haccept with ⟨hchecks, hrest⟩
      intro q hq
      have hp : foldPosition layer.step q ∈ nextQueries queries layer := by
        exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
      exact ⟨layerChecks_localTransition queries current layer hchecks q hq,
        ih _ _ hrest _ hp⟩

theorem accepts_terminal_degree (queries : Finset Nat) (current : Nat → F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (haccept : accepts queries current layers terminal) :
    terminalDegreeOk terminal := by
  induction layers generalizing queries current with
  | nil => exact haccept.1
  | cons layer rest ih => exact ih _ _ haccept.2

/-- A successful query path reaches the polynomial value at its final query
index; this does not assert that the polynomial has low degree. -/
theorem queryPath_terminal (q : Nat) (value : F)
    (layers : List (Layer F)) (terminal : Terminal F)
    (hpath : queryPath q value layers terminal) :
    terminalValue layers q value = terminalEval terminal (terminalPosition layers q) := by
  induction layers generalizing q value with
  | nil => exact hpath
  | cons layer rest ih =>
      exact ih _ _ hpath.2

/-- Repeated native right shifts have the same index as one shift by the
sum of the layer step counts, for any schedule. -/
theorem terminalPosition_eq_totalFold (layers : List (Layer F)) (q : Nat) :
    terminalPosition layers q = foldPosition (totalSteps layers) q := by
  induction layers generalizing q with
  | nil => simp [terminalPosition, totalSteps, foldPosition]
  | cons layer rest ih =>
      simp [terminalPosition, totalSteps, ih,
        fold_position_composes, Nat.add_comm]

/-- General modeled-acceptance-to-IOP bridge. Every raw transcript draw,
including duplicates and draws merging under folds, has an oracle-consistent
layer path and reaches the terminal polynomial evaluation. -/
theorem modeled_acceptance_has_iop_path (raw : List Nat)
    (current : Nat → F) (layers : List (Layer F))
    (terminal : Terminal F)
    (haccept : accepts (normalized raw) current layers terminal)
    (q : Nat) (hq : q ∈ raw) :
    terminalDegreeOk terminal ∧
    queryPath q (current q) layers terminal ∧
      terminalValue layers q (current q) =
        terminalEval terminal (foldPosition (totalSteps layers) q) := by
  have hnormalized : q ∈ normalized raw := by
    simpa [normalized] using hq
  have hpath := accepts_implies_queryPath
    (normalized raw) current layers terminal haccept q hnormalized
  exact ⟨accepts_terminal_degree _ _ _ _ haccept, hpath, by
    rw [← terminalPosition_eq_totalFold]
    exact queryPath_terminal q (current q) layers terminal hpath⟩

/-- A raw query with no IOP path rules out modeled acceptance. -/
theorem missing_raw_iop_path_rejects (raw : List Nat)
    (current : Nat → F) (layers : List (Layer F))
    (terminal : Terminal F) (q : Nat) (hq : q ∈ raw)
    (hbad : ¬ queryPath q (current q) layers terminal) :
    ¬ accepts (normalized raw) current layers terminal := by
  intro haccept
  exact hbad (modeled_acceptance_has_iop_path raw current layers terminal
    haccept q hq).2.1

/-- A concrete failed fold transition: the reconstructed pair sums to three,
but the value forwarded to the next layer is four. -/
private def wrongFoldLayer : Layer Nat where
  step := 1
  oracle := fun q => if q % 2 = 0 then 1 else 2
  opened := fun _ r => if r = 0 then 1 else 2
  fold := fun values => values 0 + values 1
  next := fun _ => 4

private def wrongFoldTerminal : Terminal Nat where
  coefficients := [4]
  logDegreeBound := 0
  evalAt := fun coefficients _ => coefficients.head!

/-- The local relation rejects a bad value even when the terminal evaluator
would accept the forwarded four. -/
example : ¬ localTransition 0 1 wrongFoldLayer := by
  intro h
  have hfold := h.2.2
  change (4 : Nat) = 3 at hfold
  omega

example : ¬ accepts {0} (fun _ => 1) [wrongFoldLayer] wrongFoldTerminal := by
  intro h
  have hlocal := layerChecks_localTransition {0} (fun _ => 1)
    wrongFoldLayer h.1 0 (by simp)
  have hbad : ¬ localTransition 0 1 wrongFoldLayer := by
    intro htransition
    have hfold := htransition.2.2
    change (4 : Nat) = 3 at hfold
    omega
  exact hbad hlocal

section Counting

variable {D : Type*} [Fintype D]

/-- Raw transcript positions preserve multiplicity before normalization. -/
def rawPositions {s : Nat} (index : D → Nat) (draws : Fin s → D) : List Nat :=
  (List.ofFn draws).map index

/-- All ideal query vectors accepted by the abstract arbitrary-layer relation.
The layer records and oracle are fixed before the queries are drawn. -/
noncomputable def modeledAccepted (s : Nat) (index : D → Nat)
    (current : Nat → F) (layers : List (Layer F)) (terminal : Terminal F) :
    Finset (Fin s → D) := by
  classical
  exact Finset.univ.filter (fun draws =>
    accepts (normalized (rawPositions index draws)) current layers terminal)

/-- One explicit proximity premise suffices: every domain position admitting
an IOP path must lie in the fixed good set. The arbitrary-layer path theorem
then puts every accepted ideal query vector in `goodSequences`. -/
theorem modeledAccepted_subset_goodSequences (s : Nat) (index : D → Nat)
    (current : Nat → F) (layers : List (Layer F)) (terminal : Terminal F)
    (good : Finset D)
    (hproximity : ∀ d : D,
      queryPath (index d) (current (index d)) layers terminal → d ∈ good) :
    modeledAccepted s index current layers terminal ⊆
      QuerySampling.goodSequences s good := by
  classical
  intro draws hdraws
  rw [QuerySampling.good_sequences_member]
  intro i
  apply hproximity
  change draws ∈ Finset.univ.filter (fun draws =>
    accepts (normalized (rawPositions index draws)) current layers terminal) at hdraws
  have haccept : accepts (normalized (rawPositions index draws))
      current layers terminal := (Finset.mem_filter.mp hdraws).2
  have hmem : index (draws i) ∈ rawPositions index draws := by
    simp [rawPositions]
  exact (modeled_acceptance_has_iop_path (rawPositions index draws)
    current layers terminal haccept (index (draws i)) hmem).2.1

/-- Exact ideal-uniform counting composition for any finite fold schedule.
This does not model the native Blake2sM31 query distribution. -/
theorem modeled_ideal_accept_fraction [Nonempty D] (s : Nat) (index : D → Nat)
    (current : Nat → F) (layers : List (Layer F)) (terminal : Terminal F)
    (good : Finset D)
    (hproximity : ∀ d : D,
      queryPath (index d) (current (index d)) layers terminal → d ∈ good) :
    ((modeledAccepted s index current layers terminal).card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) ≤
      ((good.card : ℚ) / (Fintype.card D : ℚ)) ^ s := by
  have hcard := Finset.card_le_card
    (modeledAccepted_subset_goodSequences s index current layers terminal
      good hproximity)
  have hcast : ((modeledAccepted s index current layers terminal).card : ℚ) ≤
      ((QuerySampling.goodSequences s good).card : ℚ) := by
    exact_mod_cast hcard
  calc
    _ ≤ ((QuerySampling.goodSequences s good).card : ℚ) /
          (Fintype.card (Fin s → D) : ℚ) :=
        div_le_div_of_nonneg_right hcast (by positivity)
    _ = _ := QuerySampling.ideal_all_good_fraction s good

/-- End-to-end *conditional* counting composition for arbitrary layer counts.
`h_native_refines` is the outstanding Zig-success-to-`accepts` semantic
refinement, outside explicit Merkle and sampling failure sets. This theorem
does not prove that refinement or either failure budget. `hproximity` is the
separate IOP proximity claim for the fixed putative oracles. -/
theorem conditional_native_general_layers_bound [Nonempty D] [DecidableEq D]
    (s : Nat) (index : D → Nat)
    (current : Nat → F) (layers : List (Layer F)) (terminal : Terminal F)
    (good : Finset D)
    (nativeAccepted merkleFailure samplingFailure : Finset (Fin s → D))
    (merkleBudget samplingBudget : ℚ)
    (hproximity : ∀ d : D,
      queryPath (index d) (current (index d)) layers terminal → d ∈ good)
    (h_native_refines : nativeAccepted ⊆
      merkleFailure ∪ samplingFailure ∪
        modeledAccepted s index current layers terminal)
    (h_merkle : (merkleFailure.card : ℚ) /
      (Fintype.card (Fin s → D) : ℚ) ≤ merkleBudget)
    (h_sampling : (samplingFailure.card : ℚ) /
      (Fintype.card (Fin s → D) : ℚ) ≤ samplingBudget) :
    (nativeAccepted.card : ℚ) /
        (Fintype.card (Fin s → D) : ℚ) ≤
      merkleBudget + samplingBudget +
        ((good.card : ℚ) / (Fintype.card D : ℚ)) ^ s := by
  exact QuerySampling.conditional_native_bad_accept_bound s good
    nativeAccepted merkleFailure samplingFailure
    (modeledAccepted s index current layers terminal)
    merkleBudget samplingBudget h_native_refines
    (modeledAccepted_subset_goodSequences s index current layers terminal
      good hproximity) h_merkle h_sampling

end Counting

end S31.Gadgets.PcsFri.LayerAcceptance
