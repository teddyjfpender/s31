import S31.Gadgets.PcsFri.MultiproofDecoder
import S31.Gadgets.PcsFri.MultiproofAllHeights
import Mathlib.Tactic

/-!
The compressed Merkle decoder sorts and deduplicates initial positions, then
iterates without sorting intermediate frontiers. This file proves that its
modeled pair-or-witness layer preserves strictly increasing parent indices.
The finite-width Zig `usize` and actual sort implementation are still an
explicit native-to-model obligation.
-/

namespace S31.Gadgets.PcsFri.MultiproofSortedFrontier

open S31.Gadgets.PcsFri.MultiproofCapture
open S31.Gadgets.PcsFri.MultiproofDecoder
open S31.Gadgets.PcsFri.MultiproofAllHeights
open S31.Gadgets.PcsFri.MerkleOpening

variable {H : Type*}

private theorem chunk_parent_has_input (parentHash : H × H → H)
    (chunk : Chunk H) :
    ∃ input ∈ chunkInputs chunk,
      (chunkParent parentHash chunk).index = input.index / 2 := by
  cases chunk with
  | paired index left right =>
      exact ⟨⟨index, left⟩, by simp [chunkInputs], rfl⟩
  | witnessed index current sibling =>
      exact ⟨⟨index, current⟩, by simp [chunkInputs], rfl⟩

/-- Every emitted parent takes its index from an input node and shifts it one
bit. This follows from the complete chunk/input partition, not a hash
collision assumption. -/
theorem buildLayer_parent_has_input (parentHash : H × H → H)
    (nodes : List (Node H)) (witnesses : List H)
    (chunks : List (Chunk H)) (parents : List (Node H)) (remaining : List H)
    (sorted : List.Pairwise (fun a b => a.index < b.index) nodes)
    (accepted : buildLayer parentHash nodes witnesses =
      some (chunks, parents, remaining))
    (parent : Node H) (member : parent ∈ parents) :
    ∃ input ∈ nodes, parent.index = input.index / 2 := by
  obtain ⟨covered, emitted, _, _⟩ :=
    buildLayer_structure parentHash nodes witnesses chunks parents remaining
      sorted accepted
  rw [← emitted] at member
  obtain ⟨chunk, inChunks, parentEq⟩ := List.mem_map.mp member
  obtain ⟨input, inChunk, indexEq⟩ :=
    chunk_parent_has_input parentHash chunk
  refine ⟨input, ?_, ?_⟩
  · rw [← covered]
    exact List.mem_flatMap.mpr ⟨chunk, inChunks, inChunk⟩
  · rw [← parentEq]
    exact indexEq

/-- A sorted input frontier yields a strictly sorted parent frontier. The
nonpaired even-index branch cannot hide the adjacent sibling: it would have
been taken by the XOR-one test. -/
theorem buildLayer_preserves_sorted (parentHash : H × H → H) :
    ∀ (nodes : List (Node H)) (witnesses : List H)
      (chunks : List (Chunk H)) (parents : List (Node H))
      (remaining : List H),
      List.Pairwise (fun a b => a.index < b.index) nodes →
      buildLayer parentHash nodes witnesses = some (chunks, parents, remaining) →
      List.Pairwise (fun a b => a.index < b.index) parents := by
  intro nodes witnesses chunks parents remaining sorted accepted
  suffices aux : ∀ (n : Nat) (xs : List (Node H)) (ws : List H)
      (cs : List (Chunk H)) (ps : List (Node H)) (rem : List H),
      xs.length = n →
      List.Pairwise (fun a b => a.index < b.index) xs →
      buildLayer parentHash xs ws = some (cs, ps, rem) →
      List.Pairwise (fun a b => a.index < b.index) ps from
    aux nodes.length nodes witnesses chunks parents remaining rfl sorted accepted
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs witnesses chunks parents remaining length sorted accepted
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
                simp
        | cons second rest =>
            have firstSecond : first.index < second.index :=
              (List.pairwise_cons.mp sorted).1 second (by simp)
            by_cases pair : first.index ^^^ 1 = second.index
            · simp only [buildLayer, pair, ↓reduceIte] at accepted
              cases recursive : buildLayer parentHash rest witnesses with
              | none => simp [recursive] at accepted
              | some result =>
                  rcases result with ⟨cs, ps, rem⟩
                  have shape : chunks = .paired first.index first.hash second.hash :: cs ∧
                      parents = ⟨first.index / 2,
                        parentHash (first.hash, second.hash)⟩ :: ps ∧
                      remaining = rem := by
                    simpa [recursive] using accepted.symm
                  rcases shape with ⟨rfl, rfl, rfl⟩
                  have restSorted : List.Pairwise
                      (fun a b => a.index < b.index) rest :=
                    (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).2
                  have psSorted := ih rest.length (by
                      simp at length
                      omega) rest witnesses cs ps remaining rfl restSorted recursive
                  apply List.pairwise_cons.mpr
                  constructor
                  · intro parent inPs
                    obtain ⟨input, inRest, parentIndex⟩ :=
                      buildLayer_parent_has_input parentHash rest witnesses cs ps remaining
                        restSorted recursive parent inPs
                    have secondBeforeInput : second.index < input.index :=
                      (List.pairwise_cons.mp (List.pairwise_cons.mp sorted).2).1
                        input inRest
                    have sibling : second.index = first.index + 1 :=
                      (ordered_xor_one_iff_even_successor _ _ firstSecond).mp pair |>.2
                    dsimp
                    omega
                  · exact psSorted
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
                      have tailSorted : List.Pairwise
                          (fun a b => a.index < b.index) (second :: rest) :=
                        (List.pairwise_cons.mp sorted).2
                      have psSorted := ih (second :: rest).length (by
                          simp at length ⊢
                          omega) (second :: rest) ws cs ps remaining rfl
                            tailSorted recursive
                      have noEvenAdjacent :
                          ¬ (first.index % 2 = 0 ∧
                            second.index = first.index + 1) := by
                        intro h
                        exact pair ((ordered_xor_one_iff_even_successor _ _
                          firstSecond).mpr h)
                      apply List.pairwise_cons.mpr
                      constructor
                      · intro parent inPs
                        obtain ⟨input, inTail, parentIndex⟩ :=
                          buildLayer_parent_has_input parentHash (second :: rest)
                            ws cs ps remaining tailSorted recursive parent inPs
                        have secondAtMostInput : second.index ≤ input.index := by
                          rcases List.mem_cons.mp inTail with rfl | inRest
                          · omega
                          · exact Nat.le_of_lt
                              ((List.pairwise_cons.mp tailSorted).1 input inRest)
                        dsimp
                        omega
                      · exact psSorted

/-- The native loop sorts only the initial frontier. The model below mirrors
that choice: later layers run directly on the emitted parent list. -/
def decodeNativeShape (parentHash : H × H → H) :
    Nat → List (Node H) → List H →
      Option (List (List (Chunk H)) × List (Node H) × List H)
  | 0, nodes, witnesses => some ([], nodes, witnesses)
  | depth + 1, nodes, witnesses => do
      let (chunks, parents, remaining) ← buildLayer parentHash nodes witnesses
      let (layers, finalNodes, finalWitnesses) ←
        decodeNativeShape parentHash depth parents remaining
      some (chunks :: layers, finalNodes, finalWitnesses)

/-- Initial sorting suffices for every later frontier. Thus the unguarded
native-shaped loop and the guarded all-height decoder have identical results
on strictly sorted initial nodes, including failure and witness suffixes. -/
theorem decodeNativeShape_eq_checked (parentHash : H × H → H) :
    ∀ depth nodes witnesses,
      List.Pairwise (fun a b => a.index < b.index) nodes →
      decodeNativeShape parentHash depth nodes witnesses =
        decodeLayers parentHash depth nodes witnesses := by
  intro depth
  induction depth with
  | zero =>
      intro nodes witnesses _
      rfl
  | succ depth ih =>
      intro nodes witnesses sorted
      cases built : buildLayer parentHash nodes witnesses with
      | none => simp [decodeNativeShape, decodeLayers, sorted, built]
      | some result =>
          rcases result with ⟨chunks, parents, remaining⟩
          have parentsSorted : List.Pairwise
              (fun a b => a.index < b.index) parents :=
            buildLayer_preserves_sorted parentHash nodes witnesses chunks
              parents remaining sorted built
          simp [decodeNativeShape, decodeLayers, sorted, built,
            ih parents remaining parentsSorted]

/-- On the model of the native one-sort loop, an accepted single-root decode
gives every original query a checked path of the declared height. -/
theorem decodeNativeShape_single_root [DecidableEq H]
    (parentHash : H × H → H) (depth : Nat)
    (nodes : List (Node H)) (witnesses : List H)
    (layers : List (List (Chunk H))) (root : Node H)
    (sorted : List.Pairwise (fun a b => a.index < b.index) nodes)
    (accepted : decodeNativeShape parentHash depth nodes witnesses =
      some (layers, [root], [])) (node : Node H) (member : node ∈ nodes) :
    ∃ path, path.length = depth ∧
      pathRoot parentHash node.hash node.index path = root.hash := by
  have checked : decodeLayers parentHash depth nodes witnesses =
      some (layers, [root], []) := by
    rw [← decodeNativeShape_eq_checked parentHash depth nodes witnesses sorted]
    exact accepted
  exact decodeLayers_single_root parentHash depth nodes witnesses layers root
    checked node member

end S31.Gadgets.PcsFri.MultiproofSortedFrontier
