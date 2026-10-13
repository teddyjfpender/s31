import S31.Gadgets.PcsFri.MultiproofCapture
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic

/-!
The deterministic inner loop of `vcs_lifted/verifier.zig::verifyImpl`.
The frontier is strictly ordered by index. A neighboring pair is consumed
together exactly when `first.idx ^ 1 == second.idx`; otherwise the verifier
consumes one hash from the proof witness. This executable model exposes the
same chunk, parent frontier, and remaining witness at each step.
-/

namespace S31.Gadgets.PcsFri.MultiproofDecoder

open S31.Gadgets.PcsFri.MultiproofCapture
open S31.Gadgets.PcsFri.MerkleOpening

variable {H : Type*}

def chunkInputs : Chunk H → List (Node H)
  | .paired index left right => [⟨index, left⟩, ⟨index + 1, right⟩]
  | .witnessed index current _ => [⟨index, current⟩]

def chunkParent (parentHash : H × H → H) : Chunk H → Node H
  | .paired index left right => ⟨index / 2, parentHash (left, right)⟩
  | .witnessed index current sibling =>
      ⟨index / 2, parentHash (orderedChildren index current sibling)⟩

def chunkWitness : Chunk H → List H
  | .paired _ _ _ => []
  | .witnessed _ _ sibling => [sibling]

/-- An exact functional transcription of the native one-layer decoder loop.
`none` is its `WitnessTooShort` branch. -/
def buildLayer (parentHash : H × H → H) :
    List (Node H) → List H → Option (List (Chunk H) × List (Node H) × List H)
  | [], witnesses => some ([], [], witnesses)
  | [_], [] => none
  | [first], sibling :: witnesses =>
      some ([.witnessed first.index first.hash sibling],
        [⟨first.index / 2,
          parentHash (orderedChildren first.index first.hash sibling)⟩],
        witnesses)
  | first :: second :: rest, witnesses =>
      if first.index ^^^ 1 = second.index then
        do
          let (chunks, parents, remaining) ← buildLayer parentHash rest witnesses
          some (.paired first.index first.hash second.hash :: chunks,
            ⟨first.index / 2, parentHash (first.hash, second.hash)⟩ :: parents,
            remaining)
      else
        match witnesses with
        | [] => none
        | sibling :: tail => do
            let (chunks, parents, remaining) ←
              buildLayer parentHash (second :: rest) tail
            some (.witnessed first.index first.hash sibling :: chunks,
              ⟨first.index / 2,
                parentHash (orderedChildren first.index first.hash sibling)⟩ :: parents,
              remaining)

/-- Ordered frontier indices make the native XOR test an even/odd sibling test. -/
theorem ordered_xor_one_iff_even_successor (first second : Nat)
    (ordered : first < second) :
    (first ^^^ 1 = second) ↔ first % 2 = 0 ∧ second = first + 1 := by
  constructor
  · intro h
    rcases Nat.even_or_odd first with even | odd
    · have hmod : first % 2 = 0 := Nat.even_iff.mp even
      rw [Nat.xor_one_of_even even] at h
      exact ⟨hmod, h.symm⟩
    · rw [Nat.xor_one_of_odd odd] at h
      omega
  · rintro ⟨hmod, rfl⟩
    exact Nat.xor_one_of_even (Nat.even_iff.mpr hmod)

/-- The event model exposes exactly the input nodes represented by a chunk. -/
theorem chunkEdges_inputs (parentHash : H × H → H) (chunk : Chunk H) :
    (chunkEdges parentHash chunk).map Edge.input = chunkInputs chunk := by
  cases chunk <;> rfl

theorem layerEdges_inputs (parentHash : H × H → H)
    (chunks : List (Chunk H)) :
    (layerEdges parentHash chunks).map Edge.input =
      chunks.flatMap chunkInputs := by
  simp [layerEdges, List.map_flatMap, chunkEdges_inputs]

theorem chunkEdges_output (parentHash : H × H → H) (chunk : Chunk H)
    (edge : Edge H) (member : edge ∈ chunkEdges parentHash chunk) :
    edge.output = chunkParent parentHash chunk := by
  cases chunk with
  | paired index left right =>
      simp [chunkEdges] at member
      rcases member with rfl | rfl <;> rfl
  | witnessed index current sibling =>
      simp only [chunkEdges, List.mem_singleton] at member
      subst edge
      rfl

theorem layerEdges_output_mem (parentHash : H × H → H)
    (chunks : List (Chunk H)) (edge : Edge H)
    (member : edge ∈ layerEdges parentHash chunks) :
    edge.output ∈ chunks.map (chunkParent parentHash) := by
  simp only [layerEdges, List.mem_flatMap] at member
  obtain ⟨chunk, inChunks, inChunk⟩ := member
  apply List.mem_map.mpr
  exact ⟨chunk, inChunks, (chunkEdges_output parentHash chunk edge inChunk).symm⟩

/-- A successful decode partitions the input frontier into valid chunks,
emits their parents in order, and consumes precisely their witness hashes. -/
theorem buildLayer_structure (parentHash : H × H → H) :
    ∀ (nodes : List (Node H)) (witnesses : List H)
      (chunks : List (Chunk H)) (parents : List (Node H))
      (remaining : List H),
      List.Pairwise (fun a b => a.index < b.index) nodes →
      buildLayer parentHash nodes witnesses = some (chunks, parents, remaining) →
      chunks.flatMap chunkInputs = nodes ∧
      chunks.map (chunkParent parentHash) = parents ∧
      chunks.flatMap chunkWitness ++ remaining = witnesses ∧
      (∀ chunk ∈ chunks, validChunk chunk) := by
  intro nodes witnesses chunks parents remaining sorted accepted
  suffices aux : ∀ (n : Nat) (xs : List (Node H)) (ws : List H)
      (cs : List (Chunk H)) (ps : List (Node H)) (rem : List H),
      xs.length = n → List.Pairwise (fun a b => a.index < b.index) xs →
      buildLayer parentHash xs ws = some (cs, ps, rem) →
      cs.flatMap chunkInputs = xs ∧
      cs.map (chunkParent parentHash) = ps ∧
      cs.flatMap chunkWitness ++ rem = ws ∧
      (∀ chunk ∈ cs, validChunk chunk) from
    aux nodes.length nodes witnesses chunks parents remaining rfl sorted accepted
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs witnesses chunks parents remaining hlen sorted accepted
    cases xs with
    | nil =>
        simp [buildLayer] at accepted
        rcases accepted with ⟨rfl, rfl, rfl⟩
        simp
    | cons first tail =>
        cases tail with
        | nil =>
            cases witnesses with
            | nil => simp [buildLayer] at accepted
            | cons sibling rest =>
                simp [buildLayer] at accepted
                rcases accepted with ⟨rfl, rfl, rfl⟩
                simp [chunkInputs, chunkParent, chunkWitness, validChunk]
        | cons second rest =>
            by_cases pair : first.index ^^^ 1 = second.index
            · simp only [buildLayer, pair, ↓reduceIte] at accepted
              cases recursive : buildLayer parentHash rest witnesses with
              | none => simp [recursive] at accepted
              | some result =>
                  rcases result with ⟨cs, ps, rem⟩
                  have shape : chunks = .paired first.index first.hash second.hash :: cs ∧
                      parents = ⟨first.index / 2, parentHash (first.hash, second.hash)⟩ :: ps ∧
                      remaining = rem := by
                    simpa [recursive] using accepted.symm
                  rcases shape with ⟨rfl, rfl, rfl⟩
                  have firstSecond : first.index < second.index := by
                    exact (List.pairwise_cons.mp sorted).1 second (by simp)
                  have nextIndex : second.index = first.index + 1 :=
                    (ordered_xor_one_iff_even_successor _ _ firstSecond).mp pair |>.2
                  obtain ⟨inputs, outputs, consumed, valid⟩ :=
                    ih rest.length (by simp at hlen; omega) rest witnesses cs ps remaining
                      rfl
                      ((List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).2)
                      recursive
                  constructor
                  · simp only [List.flatMap_cons, chunkInputs, inputs]
                    cases second with
                    | mk index hash => simpa using nextIndex.symm
                  · refine ⟨?_, ?_, ?_⟩
                    · simp [chunkParent, outputs]
                    · simp [chunkWitness, consumed]
                    · intro chunk member
                      simp only [List.mem_cons] at member
                      rcases member with rfl | member
                      · exact (ordered_xor_one_iff_even_successor _ _ firstSecond).mp pair |>.1
                      · exact valid chunk member
            · simp only [buildLayer, pair, ↓reduceIte] at accepted
              cases witnesses with
              | nil => simp at accepted
              | cons sibling ws =>
                  cases recursive : buildLayer parentHash (second :: rest) ws with
                  | none => simp [recursive] at accepted
                  | some result =>
                      rcases result with ⟨cs, ps, rem⟩
                      have shape : chunks = .witnessed first.index first.hash sibling :: cs ∧
                          parents = ⟨first.index / 2,
                            parentHash (orderedChildren first.index first.hash sibling)⟩ :: ps ∧
                          remaining = rem := by
                        simpa [buildLayer, pair, recursive] using accepted.symm
                      rcases shape with ⟨rfl, rfl, rfl⟩
                      obtain ⟨inputs, outputs, consumed, valid⟩ :=
                        ih (second :: rest).length (by
                          simp only [List.length_cons] at hlen ⊢
                          omega)
                          (second :: rest) ws cs ps remaining rfl
                          (List.pairwise_cons.mp sorted).2 recursive
                      constructor
                      · simp [chunkInputs, inputs]
                      · refine ⟨?_, ?_, ?_⟩
                        · simp [chunkParent, outputs]
                        · simp [chunkWitness, consumed]
                        · intro chunk member
                          simp only [List.mem_cons] at member
                          rcases member with rfl | member
                          · trivial
                          · exact valid chunk member

/-- Every decoded input node is present in the modeled event list, so the
event walk can select its recorded sibling and parent. -/
theorem decoded_layer_has_edge [DecidableEq H]
    (parentHash : H × H → H) (nodes : List (Node H))
    (witnesses remaining : List H) (chunks : List (Chunk H))
    (parents : List (Node H)) (node : Node H)
    (sorted : List.Pairwise (fun a b => a.index < b.index) nodes)
    (decoded : buildLayer parentHash nodes witnesses =
      some (chunks, parents, remaining)) (member : node ∈ nodes) :
    ∃ edge, findEdge parentHash chunks node = some edge ∧
      edge.input = node ∧ edgeSound parentHash edge ∧ edge.output ∈ parents := by
  obtain ⟨covered, emitted, _, valid⟩ :=
    buildLayer_structure parentHash nodes witnesses chunks parents remaining
      sorted decoded
  have inInputs : node ∈ (layerEdges parentHash chunks).map Edge.input := by
    rw [layerEdges_inputs, covered]
    exact member
  obtain ⟨candidate, inEdges, inputEq⟩ := List.mem_map.mp inInputs
  cases found : findEdge parentHash chunks node with
  | none =>
      have impossible := (List.find?_eq_none.mp
        (show (layerEdges parentHash chunks).find?
          (fun edge => decide (edge.input = node)) = none from found))
        candidate inEdges
      simp [inputEq] at impossible
  | some edge =>
      obtain ⟨same, sound⟩ :=
        findEdge_sound parentHash chunks node edge valid found
      have raw : edge ∈ layerEdges parentHash chunks :=
        List.mem_of_find?_eq_some (by simpa [findEdge] using found)
      exact ⟨edge, rfl, same, sound,
        emitted ▸ layerEdges_output_mem parentHash chunks edge raw⟩

theorem decoded_layer_follows [DecidableEq H]
    (parentHash : H × H → H) (nodes : List (Node H))
    (witnesses remaining : List H) (chunks : List (Chunk H))
    (parents : List (Node H)) (node : Node H)
    (sorted : List.Pairwise (fun a b => a.index < b.index) nodes)
    (decoded : buildLayer parentHash nodes witnesses =
      some (chunks, parents, remaining)) (member : node ∈ nodes) :
    ∃ sibling parent, follow parentHash node [chunks] =
      some ([sibling], parent) ∧
      parent.hash = parentHash (orderedChildren node.index node.hash sibling) ∧
      parent ∈ parents := by
  obtain ⟨edge, found, same, sound, inParents⟩ :=
    decoded_layer_has_edge parentHash nodes witnesses remaining chunks parents
      node sorted decoded member
  refine ⟨edge.sibling, edge.output, ?_, ?_, inParents⟩
  · simp [follow, found]
  · rw [← same]
    exact sound.2

private def toyParent (children : Nat × Nat) : Nat :=
  children.1 * 100 + children.2

-- Adjacent even/odd indices share a parent without consuming a witness.
example : buildLayer toyParent [⟨0, 10⟩, ⟨1, 11⟩] [] =
    some ([.paired 0 10 11], [⟨0, toyParent (10, 11)⟩], []) := by
  rfl

-- Sparse indices consume witnesses in ascending frontier order.
example : buildLayer toyParent [⟨1, 11⟩, ⟨3, 13⟩] [10, 12] =
    some ([.witnessed 1 11 10, .witnessed 3 13 12],
      [⟨0, toyParent (10, 11)⟩, ⟨1, toyParent (12, 13)⟩], []) := by
  rfl

example : buildLayer toyParent [⟨1, 11⟩, ⟨3, 13⟩] [10] = none := by
  decide

-- The layer decoder itself leaves surplus witnesses for the final verifier
-- check, which rejects any nonempty suffix after the last layer.
example : buildLayer toyParent [⟨0, 10⟩, ⟨1, 11⟩] [99] =
    some ([.paired 0 10 11], [⟨0, toyParent (10, 11)⟩], [99]) := by
  rfl

end S31.Gadgets.PcsFri.MultiproofDecoder
