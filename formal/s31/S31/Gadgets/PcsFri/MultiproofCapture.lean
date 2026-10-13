import S31.Gadgets.PcsFri.MerkleOpening
import Mathlib.Tactic

/-!
A functional layer-event model for `vcs_lifted/verifier.zig::verifyImpl`.
Each native layer consumes either two adjacent sibling nodes or one node plus
one supplied hash witness. The verifier records the opposite child as the
captured sibling for every original query, including deduplicated queries.

The theorem below proves that following these exact layer events yields a
full bottom-up path to the checked root. The remaining implementation bridge
is that Zig's sorting, witness cursor, and path-copy loops produce these
modeled events; this file does not assume global hash injectivity or establish
that bridge merely from a source-text match.
-/

namespace S31.Gadgets.PcsFri.MultiproofCapture

open S31.Gadgets.PcsFri.MerkleOpening

variable {H V : Type*}

structure Node (H : Type*) where
  index : Nat
  hash : H
  deriving DecidableEq

/-- One native compressed multiproof chunk. `paired` represents the adjacent
even/odd sibling branch; `witnessed` consumes one hash from the proof. -/
inductive Chunk (H : Type*) where
  | paired (evenIndex : Nat) (left right : H)
  | witnessed (index : Nat) (current sibling : H)

/-- The sorted-adjacent pair branch in native code has an even first index. -/
def validChunk : Chunk H → Prop
  | .paired evenIndex _ _ => evenIndex % 2 = 0
  | .witnessed _ _ _ => True

structure Edge (H : Type*) where
  input : Node H
  sibling : H
  output : Node H
  deriving DecidableEq

/-- The two captured sibling assignments made by a paired native chunk, or
the one assignment made by a witness-consuming chunk. -/
def chunkEdges (parentHash : H × H → H) : Chunk H → List (Edge H)
  | .paired evenIndex left right =>
      let parent := ⟨evenIndex / 2, parentHash (left, right)⟩
      [⟨⟨evenIndex, left⟩, right, parent⟩,
       ⟨⟨evenIndex + 1, right⟩, left, parent⟩]
  | .witnessed index current sibling =>
      [⟨⟨index, current⟩, sibling,
        ⟨index / 2, parentHash (orderedChildren index current sibling)⟩⟩]

def layerEdges (parentHash : H × H → H) (chunks : List (Chunk H)) : List (Edge H) :=
  chunks.flatMap (chunkEdges parentHash)

/-- The native bottom-up hash/index relation for one captured edge. -/
def edgeSound (parentHash : H × H → H) (edge : Edge H) : Prop :=
  edge.output.index = edge.input.index / 2 ∧
    edge.output.hash = parentHash
      (orderedChildren edge.input.index edge.input.hash edge.sibling)

theorem chunk_edges_sound (parentHash : H × H → H) (chunk : Chunk H)
    (valid : validChunk chunk) (edge : Edge H)
    (member : edge ∈ chunkEdges parentHash chunk) :
    edgeSound parentHash edge := by
  cases chunk with
  | paired evenIndex left right =>
      simp only [validChunk] at valid
      simp [chunkEdges] at member
      rcases member with first | second
      · subst edge
        simp [edgeSound, orderedChildren, valid]
      · subst edge
        have odd : (evenIndex + 1) % 2 ≠ 0 := by omega
        have half : (evenIndex + 1) / 2 = evenIndex / 2 := by omega
        simp [edgeSound, orderedChildren, odd, half]
  | witnessed index current sibling =>
      simp only [chunkEdges, List.mem_singleton] at member
      subst edge
      simp [edgeSound]

theorem layer_edges_sound (parentHash : H × H → H) (chunks : List (Chunk H))
    (valid : ∀ chunk ∈ chunks, validChunk chunk) (edge : Edge H)
    (member : edge ∈ layerEdges parentHash chunks) :
    edgeSound parentHash edge := by
  simp only [layerEdges, List.mem_flatMap] at member
  rcases member with ⟨chunk, inChunks, inChunk⟩
  exact chunk_edges_sound parentHash chunk (valid chunk inChunks) edge inChunk

/-- Locate the native assignment for a current node. If no assignment exists,
decoding fails rather than silently fabricating a path. -/
def findEdge [DecidableEq H] (parentHash : H × H → H)
    (chunks : List (Chunk H)) (node : Node H) : Option (Edge H) :=
  (layerEdges parentHash chunks).find? fun edge => decide (edge.input = node)

/-- Follow compressed native-style layer events for one original query and
return its captured siblings in bottom-up order and final node. -/
def follow [DecidableEq H] (parentHash : H × H → H) (node : Node H) :
    List (List (Chunk H)) → Option (List H × Node H)
  | [] => some ([], node)
  | layer :: rest => do
      let edge ← findEdge parentHash layer node
      let (path, finalNode) ← follow parentHash edge.output rest
      some (edge.sibling :: path, finalNode)

theorem findEdge_sound [DecidableEq H] (parentHash : H × H → H)
    (chunks : List (Chunk H)) (node : Node H) (edge : Edge H)
    (valid : ∀ chunk ∈ chunks, validChunk chunk)
    (found : findEdge parentHash chunks node = some edge) :
    edge.input = node ∧ edgeSound parentHash edge := by
  have raw : (layerEdges parentHash chunks).find?
      (fun candidate => decide (candidate.input = node)) = some edge := by
    simpa [findEdge] using found
  have member := List.mem_of_find?_eq_some raw
  have selected := List.find?_some raw
  exact ⟨of_decide_eq_true selected,
    layer_edges_sound parentHash chunks valid edge member⟩

/-- Every successful modeled compressed multiproof capture independently
replays to its final node. This connects the one- or two-child native layer
chunks to the full path used by `MerkleOpening.pathRoot`. -/
theorem follow_replays [DecidableEq H] (parentHash : H × H → H)
    (layers : List (List (Chunk H)))
    (valid : ∀ layer ∈ layers, ∀ chunk ∈ layer, validChunk chunk)
    (node finalNode : Node H) (path : List H)
    (accepted : follow parentHash node layers = some (path, finalNode)) :
    pathRoot parentHash node.hash node.index path = finalNode.hash ∧
      path.length = layers.length ∧
      finalNode.index = node.index / 2 ^ layers.length := by
  induction layers generalizing node path finalNode with
  | nil =>
      simp [follow] at accepted
      rcases accepted with ⟨rfl, rfl⟩
      simp [pathRoot]
  | cons layer rest ih =>
      have layerValid : ∀ chunk ∈ layer, validChunk chunk :=
        valid layer (by simp)
      have restValid : ∀ next ∈ rest, ∀ chunk ∈ next, validChunk chunk := by
        intro next hnext
        exact valid next (by simp [hnext])
      cases found : findEdge parentHash layer node with
      | none => simp [follow, found] at accepted
      | some edge =>
          cases next : follow parentHash edge.output rest with
          | none => simp [follow, found, next] at accepted
          | some result =>
              rcases result with ⟨tailPath, reached⟩
              have shape : path = edge.sibling :: tailPath ∧ finalNode = reached := by
                have h : edge.sibling :: tailPath = path ∧ reached = finalNode := by
                  simpa [follow, found, next] using accepted
                exact ⟨h.1.symm, h.2.symm⟩
              rcases shape with ⟨rfl, rfl⟩
              obtain ⟨inputEq, edgeStep⟩ :=
                findEdge_sound parentHash layer node edge layerValid found
              rcases edgeStep with ⟨indexStep, hashStep⟩
              have tail := ih restValid edge.output finalNode tailPath next
              rcases tail with ⟨tailRoot, tailLength, tailIndex⟩
              constructor
              · simpa [pathRoot, ← inputEq, indexStep, hashStep] using tailRoot
              constructor
              · simp [tailLength]
              · simp only [List.length_cons, pow_succ]
                rw [tailIndex, indexStep]
                simp only [Nat.div_div_eq_div_mul, Nat.mul_comm, inputEq]

/-- A successful event-chain capture under the checked root satisfies the
full-path acceptance predicate used by the Merkle binding reduction. The
bounded-position premise is enforced by the native verifier's range guard. -/
theorem successful_capture_is_accepted [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (root : H) (height position : Nat) (row : List V)
    (layers : List (List (Chunk H))) (path : List H) (finalNode : Node H)
    (valid : ∀ layer ∈ layers, ∀ chunk ∈ layer, validChunk chunk)
    (depth : layers.length = height) (inDomain : position < 2 ^ height)
    (capture : follow parentHash ⟨position, leafHash row⟩ layers =
      some (path, finalNode))
    (rootChecked : finalNode.hash = root) :
    acceptedOpening leafHash parentHash root height position row path := by
  obtain ⟨replay, pathDepth, _⟩ := follow_replays parentHash layers valid
    ⟨position, leafHash row⟩ finalNode path capture
  exact ⟨inDomain, pathDepth.trans depth, replay.trans rootChecked⟩

/-- With the new native range guard, `height` right shifts necessarily put
the final captured node at the root index zero. -/
theorem successful_capture_root_index_zero [DecidableEq H]
    (parentHash : H × H → H) (height position : Nat)
    (leaf finalNode : Node H) (layers : List (List (Chunk H)))
    (path : List H)
    (valid : ∀ layer ∈ layers, ∀ chunk ∈ layer, validChunk chunk)
    (depth : layers.length = height) (inDomain : position < 2 ^ height)
    (leafPosition : leaf.index = position)
    (capture : follow parentHash leaf layers = some (path, finalNode)) :
    finalNode.index = 0 := by
  obtain ⟨_, _, finalIndex⟩ := follow_replays parentHash layers valid
    leaf finalNode path capture
  rw [depth, leafPosition] at finalIndex
  exact finalIndex.trans (Nat.div_eq_of_lt inDomain)

/-- The complete symbolic join for one native captured query: the executable
compressed event walk gives a full path, then Merkle binding identifies the
opened row with the projected committed columns unless these exact openings
witness a hash collision. The Zig-event correspondence and committed-column
origin remain explicit premises. -/
theorem successful_capture_refines_projected_row [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (root : H) (height position : Nat) (columns : List (Column V))
    (nativeRow : List V) (layers : List (List (Chunk H)))
    (nativePath committedPath : List H) (finalNode : Node H)
    (valid : ∀ layer ∈ layers, ∀ chunk ∈ layer, validChunk chunk)
    (depth : layers.length = height) (inDomain : position < 2 ^ height)
    (capture : follow parentHash ⟨position, leafHash nativeRow⟩ layers =
      some (nativePath, finalNode))
    (rootChecked : finalNode.hash = root)
    (committed : acceptedOpening leafHash parentHash root height position
      (projectedRow height position columns) committedPath)
    (noCollision : ¬collisionOnOpenings leafHash parentHash position nativeRow
      (projectedRow height position columns) nativePath committedPath) :
    nativeRow = projectedRow height position columns := by
  have native := successful_capture_is_accepted leafHash parentHash root
    height position nativeRow layers nativePath finalNode valid depth inDomain
    capture rootChecked
  exact accepted_row_refines_projected_commitment leafHash parentHash root
    height position columns nativeRow committedPath nativePath committed native
    noCollision

/-- Tiny executable two-query, two-layer example. This arithmetic hash is
illustrative only; no security property is assigned to it. -/
private def toyParent (children : Nat × Nat) : Nat :=
  children.1 * 100 + children.2

private def toyLayers : List (List (Chunk Nat)) :=
  [[.witnessed 1 11 10, .witnessed 3 13 12],
   [.paired 0 (toyParent (10, 11)) (toyParent (12, 13))]]

example : follow toyParent ⟨1, 11⟩ toyLayers =
    some ([10, toyParent (12, 13)],
      ⟨0, toyParent (toyParent (10, 11), toyParent (12, 13))⟩) := by
  decide

example : follow toyParent ⟨3, 13⟩ toyLayers =
    some ([12, toyParent (10, 11)],
      ⟨0, toyParent (toyParent (10, 11), toyParent (12, 13))⟩) := by
  decide

end S31.Gadgets.PcsFri.MultiproofCapture
