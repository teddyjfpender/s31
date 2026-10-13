import S31.Gadgets.PcsFri.MultiproofDecoder
import Mathlib.Tactic

/-!
Compose the compressed Merkle decoder across an arbitrary number of levels.
The sorted-frontier check makes the invariant needed by `buildLayer_structure`
explicit. Native Zig obtains it from initial sorting and parent construction;
proving that correspondence remains a separate implementation obligation.
-/

namespace S31.Gadgets.PcsFri.MultiproofAllHeights

open S31.Gadgets.PcsFri.MultiproofCapture
open S31.Gadgets.PcsFri.MultiproofDecoder
open S31.Gadgets.PcsFri.MerkleOpening

variable {H : Type*}

/-- A full compressed witness walk with an explicit sorted-frontier invariant
at every level. An unsuccessful layer or insufficient witness fails closed. -/
def decodeLayers (parentHash : H × H → H) :
    Nat → List (Node H) → List H →
      Option (List (List (Chunk H)) × List (Node H) × List H)
  | 0, nodes, witnesses => some ([], nodes, witnesses)
  | depth + 1, nodes, witnesses => do
      if ¬ List.Pairwise (fun a b => a.index < b.index) nodes then none
      else
        let (chunks, parents, remaining) ← buildLayer parentHash nodes witnesses
        let (layers, finalNodes, finalWitnesses) ←
          decodeLayers parentHash depth parents remaining
        some (chunks :: layers, finalNodes, finalWitnesses)

/-- Every accepted level consumed a valid chunk partition; there are exactly
`depth` layers. This is a statement about the executable model. -/
theorem decodeLayers_valid (parentHash : H × H → H) :
    ∀ depth nodes witnesses layers finalNodes remaining,
      decodeLayers parentHash depth nodes witnesses =
        some (layers, finalNodes, remaining) →
      layers.length = depth ∧
      ∀ layer ∈ layers, ∀ chunk ∈ layer, validChunk chunk := by
  intro depth
  induction depth with
  | zero =>
      intro nodes witnesses layers finalNodes remaining accepted
      simp [decodeLayers] at accepted
      rcases accepted with ⟨rfl, rfl, rfl⟩
      simp
  | succ depth ih =>
      intro nodes witnesses layers finalNodes remaining accepted
      by_cases sorted : List.Pairwise (fun a b => a.index < b.index) nodes
      · cases built : buildLayer parentHash nodes witnesses with
        | none => simp [decodeLayers, sorted, built] at accepted
        | some result =>
            rcases result with ⟨chunks, parents, rest⟩
            cases tail : decodeLayers parentHash depth parents rest with
            | none => simp [decodeLayers, sorted, built, tail] at accepted
            | some output =>
                rcases output with ⟨nextLayers, lastNodes, lastWitnesses⟩
                have shape : layers = chunks :: nextLayers ∧
                    finalNodes = lastNodes ∧ remaining = lastWitnesses := by
                  simpa [decodeLayers, sorted, built, tail] using accepted.symm
                rcases shape with ⟨rfl, rfl, rfl⟩
                obtain ⟨_, _, _, validHead⟩ :=
                  buildLayer_structure parentHash nodes witnesses chunks parents rest
                    sorted built
                obtain ⟨lengthTail, validTail⟩ :=
                  ih parents rest nextLayers finalNodes remaining tail
                constructor
                · simp [lengthTail]
                · intro layer member chunk inChunk
                  rcases List.mem_cons.mp member with rfl | inTail
                  · exact validHead chunk inChunk
                  · exact validTail layer inTail chunk inChunk
      · simp [decodeLayers, sorted] at accepted

/-- Compression consumes each witness hash exactly once in frontier order.
The caller's empty-suffix check rules out surplus words. -/
theorem decodeLayers_witness_accounting (parentHash : H × H → H) :
    ∀ depth nodes witnesses layers finalNodes remaining,
      decodeLayers parentHash depth nodes witnesses =
        some (layers, finalNodes, remaining) →
      layers.flatMap (fun layer => layer.flatMap chunkWitness) ++ remaining =
        witnesses := by
  intro depth
  induction depth with
  | zero =>
      intro nodes witnesses layers finalNodes remaining accepted
      simp [decodeLayers] at accepted
      rcases accepted with ⟨rfl, rfl, rfl⟩
      simp
  | succ depth ih =>
      intro nodes witnesses layers finalNodes remaining accepted
      by_cases sorted : List.Pairwise (fun a b => a.index < b.index) nodes
      · cases built : buildLayer parentHash nodes witnesses with
        | none => simp [decodeLayers, sorted, built] at accepted
        | some result =>
            rcases result with ⟨chunks, parents, rest⟩
            cases tail : decodeLayers parentHash depth parents rest with
            | none => simp [decodeLayers, sorted, built, tail] at accepted
            | some output =>
                rcases output with ⟨nextLayers, lastNodes, lastWitnesses⟩
                have shape : layers = chunks :: nextLayers ∧
                    finalNodes = lastNodes ∧ remaining = lastWitnesses := by
                  simpa [decodeLayers, sorted, built, tail] using accepted.symm
                rcases shape with ⟨rfl, rfl, rfl⟩
                obtain ⟨_, _, used, _⟩ :=
                  buildLayer_structure parentHash nodes witnesses chunks parents rest
                    sorted built
                have tailUsed := ih parents rest nextLayers finalNodes remaining tail
                simp only [List.flatMap_cons, List.append_assoc]
                rw [tailUsed]
                exact used
      · simp [decodeLayers, sorted] at accepted

/-- Every initial query in an accepted full decode follows one path to a node
in the final frontier. The assertion is uniform in witness length and height. -/
theorem decodeLayers_follows [DecidableEq H] (parentHash : H × H → H) :
    ∀ depth nodes witnesses layers finalNodes remaining,
      decodeLayers parentHash depth nodes witnesses =
        some (layers, finalNodes, remaining) →
      ∀ node ∈ nodes, ∃ path target,
        target ∈ finalNodes ∧
        follow parentHash node layers = some (path, target) := by
  intro depth
  induction depth with
  | zero =>
      intro nodes witnesses layers finalNodes remaining accepted node member
      simp [decodeLayers] at accepted
      rcases accepted with ⟨rfl, rfl, rfl⟩
      exact ⟨[], node, member, rfl⟩
  | succ depth ih =>
      intro nodes witnesses layers finalNodes remaining accepted node member
      by_cases sorted : List.Pairwise (fun a b => a.index < b.index) nodes
      · cases built : buildLayer parentHash nodes witnesses with
        | none => simp [decodeLayers, sorted, built] at accepted
        | some result =>
            rcases result with ⟨chunks, parents, rest⟩
            cases tail : decodeLayers parentHash depth parents rest with
            | none => simp [decodeLayers, sorted, built, tail] at accepted
            | some output =>
                rcases output with ⟨nextLayers, lastNodes, lastWitnesses⟩
                have shape : layers = chunks :: nextLayers ∧
                    finalNodes = lastNodes ∧ remaining = lastWitnesses := by
                  simpa [decodeLayers, sorted, built, tail] using accepted.symm
                rcases shape with ⟨rfl, rfl, rfl⟩
                obtain ⟨sibling, parent, oneStep, _, inParents⟩ :=
                  decoded_layer_follows parentHash nodes witnesses rest chunks
                    parents node sorted built member
                obtain ⟨path, target, inFinal, moreSteps⟩ :=
                  ih parents rest nextLayers finalNodes remaining tail parent inParents
                refine ⟨sibling :: path, target, inFinal, ?_⟩
                cases found : findEdge parentHash chunks node with
                | none => simp [follow, found] at oneStep
                | some edge =>
                    have edgeShape : edge.sibling = sibling ∧
                        edge.output = parent := by
                      simpa [follow, found] using oneStep
                    rcases edgeShape with ⟨siblingEq, parentEq⟩
                    simp [follow, found, parentEq, moreSteps, siblingEq]
      · simp [decodeLayers, sorted] at accepted

/-- If the accepted final frontier is exactly the checked root and no witness
hashes remain, every initial node has a full-height path to that root. -/
theorem decodeLayers_single_root [DecidableEq H] (parentHash : H × H → H)
    (depth : Nat) (nodes : List (Node H)) (witnesses : List H)
    (layers : List (List (Chunk H))) (root : Node H)
    (accepted : decodeLayers parentHash depth nodes witnesses =
      some (layers, [root], [])) (node : Node H) (member : node ∈ nodes) :
    ∃ path, path.length = depth ∧
      pathRoot parentHash node.hash node.index path = root.hash := by
  obtain ⟨length, valid⟩ := decodeLayers_valid parentHash depth nodes
    witnesses layers [root] [] accepted
  obtain ⟨path, target, targetMember, followed⟩ :=
    decodeLayers_follows parentHash depth nodes witnesses layers [root] []
      accepted node member
  have targetEq : target = root := by simpa using targetMember
  subst target
  obtain ⟨replay, pathDepth, _⟩ :=
    follow_replays parentHash layers valid node root path followed
  exact ⟨path, pathDepth.trans length, replay⟩

/-- The complete model-level acceptance condition expected by the Merkle
collision reduction. The native sorted frontier and root comparison still
need to be shown to instantiate this exact decoder. -/
theorem decodeLayers_accepted_opening [DecidableEq H]
    {V : Type*} (leafHash : List V → H) (parentHash : H × H → H)
    (rootHash : H) (height position : Nat) (row : List V)
    (nodes : List (Node H)) (witnesses : List H)
    (layers : List (List (Chunk H))) (root : Node H)
    (accepted : decodeLayers parentHash height nodes witnesses =
      some (layers, [root], []))
    (rootChecked : root.hash = rootHash)
    (inDomain : position < 2 ^ height)
    (queried : (⟨position, leafHash row⟩ : Node H) ∈ nodes) :
    ∃ path, acceptedOpening leafHash parentHash rootHash height position row path := by
  obtain ⟨path, pathDepth, pathRootEq⟩ :=
    decodeLayers_single_root parentHash height nodes witnesses layers root
      accepted ⟨position, leafHash row⟩ queried
  exact ⟨path, inDomain, pathDepth, pathRootEq.trans rootChecked⟩

end S31.Gadgets.PcsFri.MultiproofAllHeights
