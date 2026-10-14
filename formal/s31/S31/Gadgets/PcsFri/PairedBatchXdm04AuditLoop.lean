import S31.Gadgets.PcsFri.PairedBatchXdm04Framing

/-!
An executable model of the audit-only XDM04 `Capture.auditAt` parent walk.
For each native level it checks the current node, the sibling and inserted
row selected by `openingAt`, then recomputes the ordered parent. The recursive
checker consumes exactly one step per level. Its soundness theorem supplies
the path-local recurrence needed by `auditedOpening_checks` for arbitrary
modeled profile dimensions.

This is a Lean theorem about the executable checker. Source pins and native
mutation tests guard the corresponding Zig code separately; they do not prove
that Zig execution refines this Lean definition. In particular, bare
`verifyAndCollect` success does not imply this check succeeded.
-/

namespace S31.Gadgets.PcsFri.PairedBatchXdm04AuditLoop

open S31.Gadgets.PcsFri.PairedBatchSourceCustody
open S31.Gadgets.PcsFri.PairedBatchXdm04Topology
open S31.Gadgets.PcsFri.PairedBatchXdm04Certificate
open S31.Gadgets.PcsFri.PairedBatchXdm04Framing

variable {H : Type*} [DecidableEq H]

/-- The node-map checks made by the audit walk, including the step fields
selected by `openingAt`. The starting digest is supplied separately so that
the caller must prove it is the tagged hash of the opened row. -/
def auditEdges (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (nodes : Nat → Nat → H) (siblingIndex : Nat → Nat → Nat)
    (rows : Nat → Nat → List Base) (k heightCount : Nat) :
    Nat → Nat → H → List (MixedStep H) → Bool
  | 0, index, current, [] => decide (current = nodes 0 index)
  | 0, _, _, _ :: _ => false
  | _ + 1, _, _, [] => false
  | level + 1, index, current, step :: rest =>
      decide (current = nodes (level + 1) index) &&
      decide (step.1 = nodes (level + 1) (siblingIndex (level + 1) index)) &&
      decide (step.2 = edgeRow rows k heightCount (level + 1) index) &&
      auditEdges upperHash insertedHash nodes siblingIndex rows k heightCount
        level (nativeParent (level + 1) index)
        (mixedHash upperHash insertedHash
          (nativeChildren (level + 1) index current step.1, step.2)) rest

/-- A successful complete audit fixes the current node, every selected
sibling and inserted row, and every parent recurrence on the opened path.
It places no condition on off-path nodes. -/
theorem auditEdges_sound (upperHash : H × H → H)
    (insertedHash : H × H → List Base → H)
    (nodes : Nat → Nat → H) (siblingIndex : Nat → Nat → Nat)
    (rows : Nat → Nat → List Base) (k heightCount level index : Nat)
    (current : H) (steps : List (MixedStep H))
    (accepted : auditEdges upperHash insertedHash nodes siblingIndex rows
      k heightCount level index current steps = true) :
    current = nodes level index ∧
    steps = committedSteps nodes siblingIndex rows k heightCount level index ∧
    pathNodeRecurrences upperHash insertedHash nodes siblingIndex rows
      k heightCount level index := by
  induction level generalizing index current steps with
  | zero =>
      cases steps with
      | nil =>
          have hcurrent : current = nodes 0 index := by
            simpa [auditEdges] using (of_decide_eq_true accepted)
          exact ⟨hcurrent, rfl, trivial⟩
      | cons _ _ => simp [auditEdges] at accepted
  | succ level ih =>
      cases steps with
      | nil => simp [auditEdges] at accepted
      | cons step rest =>
          have hparts :
              ((current = nodes (level + 1) index ∧
                step.1 = nodes (level + 1) (siblingIndex (level + 1) index)) ∧
                step.2 = edgeRow rows k heightCount (level + 1) index) ∧
              auditEdges upperHash insertedHash nodes siblingIndex rows
                k heightCount level (nativeParent (level + 1) index)
                (mixedHash upperHash insertedHash
                  (nativeChildren (level + 1) index current step.1, step.2))
                rest = true := by
            simpa [auditEdges, Bool.and_eq_true, decide_eq_true_eq] using accepted
          rcases hparts with ⟨⟨⟨hcurrent, hsibling⟩, hrow⟩, htail⟩
          obtain ⟨hparent, hsteps, hpath⟩ := ih _ _ _ htail
          refine ⟨hcurrent, ?_, ?_⟩
          · have hstep : step =
                (nodes (level + 1) (siblingIndex (level + 1) index),
                  edgeRow rows k heightCount (level + 1) index) :=
              Prod.ext hsibling hrow
            simp [committedSteps, hstep, hsteps]
          · constructor
            · rw [← hparent, ← hcurrent, ← hsibling, ← hrow]
            · exact hpath

/-- Local verifier-success implication after the audited native-to-model
premise has been supplied. The starting-node equation comes from the audit
itself; only the admitted index and public root remain external. The digest
implementation is still abstract, and instantiating it with the Zig BLAKE2s
routine requires its own refinement. -/
theorem auditedPath_checks (d : Digest32)
    (nodes : Nat → Nat → Bytes) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) (input : NodeInput Bytes)
    (root : Bytes) (steps : List (MixedStep Bytes))
    (hindex : index < 2 ^ level)
    (hroot : nodes 0 0 = root)
    (accepted : auditEdges (framedUpper d) (framedInserted d)
      nodes nativeSibling rows k heightCount level index
      (taggedNodeHash (framedLeaf d) (framedInserted d) input)
      steps = true) :
    checkFramedOpening d
      (auditedOpening nodes rows k heightCount level index input root) = true := by
  obtain ⟨hstart, _, hpath⟩ := auditEdges_sound (framedUpper d) (framedInserted d)
    nodes nativeSibling rows k heightCount level index
    (taggedNodeHash (framedLeaf d) (framedInserted d) input) steps accepted
  exact auditedOpening_checks d nodes rows k heightCount level index input root
    hindex hstart hroot hpath

/-- The exact captured step list, rather than a separately reconstructed
list, passes the framed checker when the audit walk accepts. This is the
model-side success theorem corresponding to the Zig `openingAt` fields. -/
theorem auditedNativeOpening_checks (d : Digest32)
    (nodes : Nat → Nat → Bytes) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) (input : NodeInput Bytes)
    (root : Bytes) (steps : List (MixedStep Bytes))
    (hindex : index < 2 ^ level)
    (hroot : nodes 0 0 = root)
    (accepted : auditEdges (framedUpper d) (framedInserted d)
      nodes nativeSibling rows k heightCount level index
      (taggedNodeHash (framedLeaf d) (framedInserted d) input)
      steps = true) :
    checkFramedOpening d
      { level := level, nativeIndex := index
        binaryPosition := pathPosition level index, input := input
        steps := steps, root := root } = true := by
  obtain ⟨_, hsteps, _⟩ := auditEdges_sound (framedUpper d) (framedInserted d)
    nodes nativeSibling rows k heightCount level index
    (taggedNodeHash (framedLeaf d) (framedInserted d) input) steps accepted
  have hderived := auditedPath_checks d nodes rows k heightCount level index
    input root steps hindex hroot accepted
  simpa [auditedOpening, hsteps] using hderived

/-- Complete modeled audit acceptance. The index and root checks are part of
the executable predicate, so its success theorem needs no external geometry
or root premise. The native-to-model execution relation is still separate. -/
def auditModeledOpening (d : Digest32)
    (nodes : Nat → Nat → Bytes) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) (input : NodeInput Bytes)
    (root : Bytes) (steps : List (MixedStep Bytes)) : Bool :=
  decide (index < 2 ^ level) && decide (nodes 0 0 = root) &&
    auditEdges (framedUpper d) (framedInserted d) nodes nativeSibling rows
      k heightCount level index
      (taggedNodeHash (framedLeaf d) (framedInserted d) input) steps

theorem auditModeledOpening_sound (d : Digest32)
    (nodes : Nat → Nat → Bytes) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) (input : NodeInput Bytes)
    (root : Bytes) (steps : List (MixedStep Bytes))
    (accepted : auditModeledOpening d nodes rows k heightCount level index
      input root steps = true) :
    checkFramedOpening d
      { level := level, nativeIndex := index
        binaryPosition := pathPosition level index, input := input
        steps := steps, root := root } = true := by
  have hparts : (index < 2 ^ level ∧ nodes 0 0 = root) ∧
      auditEdges (framedUpper d) (framedInserted d) nodes nativeSibling rows
        k heightCount level index
        (taggedNodeHash (framedLeaf d) (framedInserted d) input) steps = true := by
    simpa [auditModeledOpening, Bool.and_eq_true, decide_eq_true_eq] using accepted
  rcases hparts with ⟨⟨hindex, hroot⟩, hedges⟩
  exact auditedNativeOpening_checks d nodes rows k heightCount level index
    input root steps hindex hroot hedges

theorem auditModeledOpening_accepted (d : Digest32)
    (nodes : Nat → Nat → Bytes) (rows : Nat → Nat → List Base)
    (k heightCount level index : Nat) (input : NodeInput Bytes)
    (root : Bytes) (steps : List (MixedStep Bytes))
    (accepted : auditModeledOpening d nodes rows k heightCount level index
      input root steps = true) :
    acceptedMixedOpening (framedLeaf d) (framedInserted d) (framedUpper d)
      root level (pathPosition level index) input steps := by
  exact checkFramedOpening_sound d _
    (auditModeledOpening_sound d nodes rows k heightCount level index
      input root steps accepted)

/-- A one-edge witness shows the checker accepts a genuine parent equation;
changing the sibling is rejected. The general theorem above is independent
of this small executable control. -/
private def toyNodes (level index : Nat) : Nat :=
  if level = 0 then 7 else if level = 1 then
    (if index = 0 then 3 else 4) else 0

example : auditEdges (fun pair : Nat × Nat => pair.1 + pair.2)
    (fun _ _ => 0) toyNodes nativeSibling (fun _ _ => []) 1 1
    1 0 3 [(4, none)] = true := by decide

example : auditEdges (fun pair : Nat × Nat => pair.1 + pair.2)
    (fun _ _ => 0) toyNodes nativeSibling (fun _ _ => []) 1 1
    1 0 3 [(5, none)] = false := by decide

end S31.Gadgets.PcsFri.PairedBatchXdm04AuditLoop
