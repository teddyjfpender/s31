import S31.Gadgets.PcsFri.MultiproofSortedFrontier
import Mathlib.Tactic

/-!
The native lifted Merkle verifier first decodes a sorted, deduplicated
frontier and then copies each unique path into the original query order.
This file models that last copy as a map over caller requests. Duplicate
requests therefore receive the same path, while every request retains its
own position in the result list. The theorem is about the executable Lean
decoder; proving that the Zig sort/dedup and copy loops implement the model
is still a separate native refinement obligation.
-/

namespace S31.Gadgets.PcsFri.MultiproofCallerOrder

open S31.Gadgets.PcsFri.MultiproofCapture
open S31.Gadgets.PcsFri.MultiproofSortedFrontier
open S31.Gadgets.PcsFri.MultiproofAllHeights
open S31.Gadgets.PcsFri.MerkleOpening

variable {H : Type*} [DecidableEq H]

/-- Each result slot is computed from the request in the same caller slot.
The native implementation uses a sorted unique temporary array and an
indexed copy loop to realize this observable map. -/
def captureInCallerOrder (parentHash : H × H → H)
    (layers : List (List (Chunk H))) (requests : List (Node H)) :
    List (Option (List H)) :=
  requests.map fun node => (follow parentHash node layers).map Prod.fst

theorem captureInCallerOrder_length (parentHash : H × H → H)
    (layers : List (List (Chunk H))) (requests : List (Node H)) :
    (captureInCallerOrder parentHash layers requests).length = requests.length := by
  simp [captureInCallerOrder]

/-- The modeled copy returns a checked full path for every caller slot, at
arbitrary height and with arbitrary repetition or ordering of requests. -/
theorem captureInCallerOrder_getElem (parentHash : H × H → H)
    (depth : Nat) (nodes requests : List (Node H)) (witnesses : List H)
    (layers : List (List (Chunk H))) (root : Node H)
    (sorted : List.Pairwise (fun a b => a.index < b.index) nodes)
    (accepted : decodeNativeShape parentHash depth nodes witnesses =
      some (layers, [root], []))
    (requested : ∀ node ∈ requests, node ∈ nodes)
    (i : Nat) (inRange : i < requests.length) :
    ∃ path, (captureInCallerOrder parentHash layers requests)[i]'(by
      simpa [captureInCallerOrder] using inRange) = some path ∧
      path.length = depth ∧
      pathRoot parentHash requests[i].hash requests[i].index path = root.hash := by
  let node := requests[i]
  have inNodes : node ∈ nodes := requested node (List.getElem_mem inRange)
  obtain ⟨path, target, targetMember, followed⟩ :=
    decodeNativeShape_follows parentHash depth nodes witnesses layers [root] []
      sorted accepted node inNodes
  have targetEq : target = root := by simpa using targetMember
  subst target
  have checked : decodeLayers parentHash depth nodes witnesses =
      some (layers, [root], []) := by
    rw [← decodeNativeShape_eq_checked parentHash depth nodes witnesses sorted]
    exact accepted
  obtain ⟨layerCount, valid⟩ :=
    decodeLayers_valid parentHash depth nodes witnesses layers [root] [] checked
  obtain ⟨replay, pathLength, _⟩ :=
    follow_replays parentHash layers valid node root path followed
  refine ⟨path, ?_, pathLength.trans layerCount, replay⟩
  simp [captureInCallerOrder, node, followed]

/-- Equal original requests, including a duplicate query after deduplication,
receive byte-for-byte identical modeled paths. -/
theorem captureInCallerOrder_duplicate (parentHash : H × H → H)
    (layers : List (List (Chunk H))) (requests : List (Node H))
    (i j : Nat) (hi : i < requests.length) (hj : j < requests.length)
    (same : requests[i] = requests[j]) :
    (captureInCallerOrder parentHash layers requests)[i]'(by
      simpa [captureInCallerOrder] using hi) =
      (captureInCallerOrder parentHash layers requests)[j]'(by
        simpa [captureInCallerOrder] using hj) := by
  simp [captureInCallerOrder, same]

end S31.Gadgets.PcsFri.MultiproofCallerOrder
