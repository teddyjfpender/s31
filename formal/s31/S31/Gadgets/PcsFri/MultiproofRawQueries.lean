import S31.Gadgets.PcsFri.MultiproofCallerOrder
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-!
An executable raw-query front end for the compressed Merkle model. Its inputs
are the rows already assembled in native column-log-size order. It rejects an
out-of-domain position and any two rows at the same position that differ,
then deduplicates and sorts the surviving leaves before running the one-sort
decoder. The final capture maps paths back to the caller's original order.

This closes the sorted-frontier and request-membership *model premises* used
by `MultiproofCallerOrder`. It is not a proof that Zig's heap sort, finite-
width arithmetic, row assembly, or byte hashing execute this Lean function.
-/

namespace S31.Gadgets.PcsFri.MultiproofRawQueries

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.MultiproofCapture
open S31.Gadgets.PcsFri.MultiproofSortedFrontier
open S31.Gadgets.PcsFri.MultiproofCallerOrder

variable {V H : Type*}

structure RawQuery (V : Type*) where
  position : Nat
  row : List V
  deriving DecidableEq

def positionLE (a b : RawQuery V) : Prop := a.position ≤ b.position

private instance : DecidableRel (positionLE (V := V)) :=
  fun a b => inferInstanceAs (Decidable (a.position ≤ b.position))

private instance : Std.Total (positionLE (V := V)) where
  total a b := Nat.le_total a.position b.position

private instance : IsTrans (RawQuery V) (positionLE (V := V)) where
  trans _ _ _ := Nat.le_trans

/-- Native duplicate acceptance compares canonical field rows, before leaf
hashing. Equality of leaf hashes alone is deliberately insufficient. -/
def consistentRows (queries : List (RawQuery V)) : Prop :=
  ∀ a ∈ queries, ∀ b ∈ queries, a.position = b.position → a.row = b.row

def shapeOK [DecidableEq V] (height : Nat)
    (queries : List (RawQuery V)) : Bool :=
  queries.all (fun q => decide (q.position < 2 ^ height)) &&
    queries.all (fun a => queries.all (fun b =>
      decide (a.position = b.position → a.row = b.row)))

theorem shapeOK_iff [DecidableEq V] (height : Nat)
    (queries : List (RawQuery V)) :
    shapeOK height queries = true ↔
      (∀ q ∈ queries, q.position < 2 ^ height) ∧ consistentRows queries := by
  simp only [shapeOK, Bool.and_eq_true, List.all_eq_true,
    decide_eq_true_iff, consistentRows]

def leafNode (leafHash : List V → H) (query : RawQuery V) : Node H :=
  ⟨query.position, leafHash query.row⟩

/-- With consistent rows, identical requests can be removed before sorting
without changing which row is selected for a position. Exact equivalence to
the native `(position, original_index)` heap sort is an open Zig bridge. The
input order is retained separately for capture output. -/
def initialNodes [DecidableEq V] (leafHash : List V → H)
    (queries : List (RawQuery V)) : List (Node H) :=
  (queries.dedup.insertionSort positionLE).map (leafNode leafHash)

/-- Executable shape checks of the native nonempty-tree decoder, expressed
over mathematical indices. The native `usize` representation is a separate
refinement premise. -/
def parseQueries [DecidableEq V] (leafHash : List V → H) (height : Nat)
    (queries : List (RawQuery V)) : Option (List (Node H)) :=
  if shapeOK height queries then
    some (initialNodes leafHash queries)
  else none

theorem parseQueries_accepts [DecidableEq V] (leafHash : List V → H)
    (height : Nat) (queries : List (RawQuery V)) (nodes : List (Node H))
    (accepted : parseQueries leafHash height queries = some nodes) :
    nodes = initialNodes leafHash queries ∧
      (∀ q ∈ queries, q.position < 2 ^ height) ∧ consistentRows queries := by
  unfold parseQueries at accepted
  split_ifs at accepted with shape
  · obtain ⟨rfl⟩ := Option.some.inj accepted.symm
    exact ⟨rfl, (shapeOK_iff height queries).mp shape⟩

theorem initialNodes_member [DecidableEq V] (leafHash : List V → H)
    (queries : List (RawQuery V)) (q : RawQuery V) (member : q ∈ queries) :
    leafNode leafHash q ∈ initialNodes leafHash queries := by
  unfold initialNodes
  exact List.mem_map.mpr ⟨q,
    (List.mem_insertionSort positionLE).2 ((List.mem_dedup).2 member), rfl⟩

/-- Every successful native-shaped preprocessing result is strictly sorted by
position. The duplicate-row check is what upgrades a nondecreasing sort and
query deduplication to *strict* order, without assuming hash injectivity. -/
theorem initialNodes_sorted [DecidableEq V] (leafHash : List V → H)
    (queries : List (RawQuery V)) (consistent : consistentRows queries) :
    List.Pairwise (fun a b => a.index < b.index)
      (initialNodes leafHash queries) := by
  let ordered := queries.dedup.insertionSort positionLE
  have sortedLE : ordered.Pairwise positionLE :=
    List.pairwise_insertionSort positionLE queries.dedup
  have unique : ordered.Nodup :=
    (List.perm_insertionSort positionLE queries.dedup).nodup_iff.mpr
      (List.nodup_dedup queries)
  have distinct : ordered.Pairwise (fun a b => a ≠ b) :=
    List.nodup_iff_pairwise_ne.mp unique
  have inOriginal : ∀ q ∈ ordered, q ∈ queries := by
    intro q member
    exact (List.mem_dedup).1 ((List.mem_insertionSort positionLE).1 member)
  have strict : ordered.Pairwise (fun a b => a.position < b.position) := by
    apply (sortedLE.and distinct).imp_of_mem
    intro a b ha hb relation
    rcases relation with ⟨le, ne⟩
    by_contra notLt
    have samePosition : a.position = b.position := by
      exact Nat.le_antisymm le (Nat.le_of_not_gt notLt)
    have sameRow := consistent a (inOriginal a ha) b (inOriginal b hb)
      samePosition
    have equal : a = b := by
      cases a with
      | mk apos arow =>
        cases b with
        | mk bpos brow =>
          simp only [RawQuery.mk.injEq]
          exact ⟨samePosition, sameRow⟩
    exact ne equal
  change List.Pairwise (fun a b => a.index < b.index)
    (ordered.map (leafNode leafHash))
  exact strict.map (leafNode leafHash) (by intro a b h; exact h)

theorem parseQueries_sorted [DecidableEq V] (leafHash : List V → H)
    (height : Nat) (queries : List (RawQuery V)) (nodes : List (Node H))
    (accepted : parseQueries leafHash height queries = some nodes) :
    List.Pairwise (fun a b => a.index < b.index) nodes := by
  obtain ⟨rfl, _, consistent⟩ :=
    parseQueries_accepts leafHash height queries nodes accepted
  exact initialNodes_sorted leafHash queries consistent

theorem parseQueries_member [DecidableEq V] (leafHash : List V → H)
    (height : Nat) (queries : List (RawQuery V)) (nodes : List (Node H))
    (accepted : parseQueries leafHash height queries = some nodes)
    (q : RawQuery V) (member : q ∈ queries) : leafNode leafHash q ∈ nodes := by
  obtain ⟨rfl, _, _⟩ :=
    parseQueries_accepts leafHash height queries nodes accepted
  exact initialNodes_member leafHash queries q member

theorem parseQueries_rejects_out_of_domain [DecidableEq V]
    (leafHash : List V → H) (height : Nat)
    (queries : List (RawQuery V)) (q : RawQuery V)
    (member : q ∈ queries) (outOfDomain : 2 ^ height ≤ q.position) :
    parseQueries leafHash height queries = none := by
  cases parsed : parseQueries leafHash height queries with
  | none => rfl
  | some nodes =>
      obtain ⟨_, domain, _⟩ :=
        parseQueries_accepts leafHash height queries nodes parsed
      have inDomain := domain q member
      omega

theorem parseQueries_rejects_conflicting_rows [DecidableEq V]
    (leafHash : List V → H) (height : Nat)
    (queries : List (RawQuery V)) (a b : RawQuery V)
    (aMember : a ∈ queries) (bMember : b ∈ queries)
    (samePosition : a.position = b.position) (differentRows : a.row ≠ b.row) :
    parseQueries leafHash height queries = none := by
  cases parsed : parseQueries leafHash height queries with
  | none => rfl
  | some nodes =>
      obtain ⟨_, _, consistent⟩ :=
        parseQueries_accepts leafHash height queries nodes parsed
      exact False.elim (differentRows (consistent a aMember b bMember samePosition))

/-- The extra root-index-zero check in `verifyRaw` does not strengthen native
acceptance for a nonempty accepted query set: bounded raw positions and a
complete height-level decode already force the only final node to index zero.
Native Zig checks the root hash and frontier length, not this index explicitly. -/
theorem parsedDecode_root_index_zero [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (queries : List (RawQuery V)) (witnesses : List H)
    (nodes : List (Node H)) (layers : List (List (Chunk H)))
    (last : Node H) (q : RawQuery V)
    (parsed : parseQueries leafHash height queries = some nodes)
    (decoded : decodeNativeShape parentHash height nodes witnesses =
      some (layers, [last], [])) (member : q ∈ queries) : last.index = 0 := by
  have sorted := parseQueries_sorted leafHash height queries nodes parsed
  have inNodes := parseQueries_member leafHash height queries nodes parsed q member
  obtain ⟨path, target, targetMember, followed⟩ :=
    decodeNativeShape_follows parentHash height nodes witnesses layers [last] []
      sorted decoded (leafNode leafHash q) inNodes
  have targetEq : target = last := by simpa using targetMember
  subst target
  have checked : S31.Gadgets.PcsFri.MultiproofAllHeights.decodeLayers
      parentHash height nodes witnesses = some (layers, [last], []) := by
    rw [← decodeNativeShape_eq_checked parentHash height nodes witnesses sorted]
    exact decoded
  obtain ⟨layerCount, valid⟩ :=
    S31.Gadgets.PcsFri.MultiproofAllHeights.decodeLayers_valid
      parentHash height nodes witnesses layers [last] [] checked
  obtain ⟨_, domain, _⟩ :=
    parseQueries_accepts leafHash height queries nodes parsed
  exact successful_capture_root_index_zero parentHash height q.position
    (leafNode leafHash q) last layers path valid layerCount
    (domain q member) rfl followed

/-- The full executable model of the nonempty-tree native multiproof path:
parse caller rows, consume the compressed witness, check one root and an
empty witness suffix, then return one optional full path per original slot.
The option at each slot is proved present for every successful result below. -/
def verifyRaw [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (root : H) (queries : List (RawQuery V))
    (witnesses : List H) : Option (List (Option (List H))) := do
  let nodes ← parseQueries leafHash height queries
  let (layers, finalNodes, remaining) ←
    decodeNativeShape parentHash height nodes witnesses
  if finalNodes = [⟨0, root⟩] ∧ remaining = [] then
    some (captureInCallerOrder parentHash layers
      (queries.map (leafNode leafHash)))
  else none

theorem verifyRaw_decomposes [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (root : H) (queries : List (RawQuery V))
    (witnesses : List H) (captures : List (Option (List H)))
    (accepted : verifyRaw leafHash parentHash height root queries witnesses =
      some captures) :
    ∃ nodes layers,
      parseQueries leafHash height queries = some nodes ∧
      decodeNativeShape parentHash height nodes witnesses =
        some (layers, [⟨0, root⟩], []) ∧
      captures = captureInCallerOrder parentHash layers
        (queries.map (leafNode leafHash)) := by
  unfold verifyRaw at accepted
  cases parsed : parseQueries leafHash height queries with
  | none => simp [parsed] at accepted
  | some nodes =>
      cases decoded : decodeNativeShape parentHash height nodes witnesses with
      | none => simp [parsed, decoded] at accepted
      | some result =>
          rcases result with ⟨layers, finalNodes, remaining⟩
          by_cases checked : finalNodes = [⟨0, root⟩] ∧ remaining = []
          · rcases checked with ⟨rfl, rfl⟩
            simp [parsed, decoded] at accepted
            exact ⟨nodes, layers, rfl, decoded, accepted.symm⟩
          · simp [parsed, decoded, checked] at accepted

/-- Every slot in a successful executable decode is an accepted full Merkle
opening under the checked root. This uses exact row duplicate equality and
does not assume that the leaf or parent hash is injective. -/
theorem verifyRaw_each_opening [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (root : H) (queries : List (RawQuery V))
    (witnesses : List H) (captures : List (Option (List H)))
    (accepted : verifyRaw leafHash parentHash height root queries witnesses =
      some captures) (i : Nat) (inRange : i < queries.length) :
    ∃ path, captures[i]'(by
      obtain ⟨_, layers, _, _, rfl⟩ :=
        verifyRaw_decomposes leafHash parentHash height root queries witnesses
          captures accepted
      simpa [captureInCallerOrder] using inRange) = some path ∧
      acceptedOpening leafHash parentHash root height
        queries[i].position queries[i].row path := by
  obtain ⟨nodes, layers, parsed, decoded, rfl⟩ :=
    verifyRaw_decomposes leafHash parentHash height root queries witnesses
      captures accepted
  have sorted := parseQueries_sorted leafHash height queries nodes parsed
  have requested : ∀ node ∈ queries.map (leafNode leafHash), node ∈ nodes := by
    intro node member
    obtain ⟨q, inQueries, rfl⟩ := List.mem_map.mp member
    exact parseQueries_member leafHash height queries nodes parsed q inQueries
  obtain ⟨path, captured, pathLength, replay⟩ :=
    captureInCallerOrder_getElem parentHash height nodes
      (queries.map (leafNode leafHash)) witnesses layers ⟨0, root⟩
      sorted decoded requested i (by simpa using inRange)
  refine ⟨path, captured, ?_⟩
  obtain ⟨_, domain, _⟩ :=
    parseQueries_accepts leafHash height queries nodes parsed
  exact ⟨domain queries[i] (List.getElem_mem inRange), pathLength,
    by simpa [leafNode] using replay⟩

/-- Conditional committed-column origin for one caller slot. The committed
opening premise must be justified by the actual prover tree construction;
the local no-collision premise is not discharged by this decoder theorem. -/
theorem verifyRaw_refines_committed_row [DecidableEq V] [DecidableEq H]
    (leafHash : List V → H) (parentHash : H × H → H)
    (height : Nat) (root : H) (queries : List (RawQuery V))
    (witnesses : List H) (captures : List (Option (List H)))
    (accepted : verifyRaw leafHash parentHash height root queries witnesses =
      some captures) (i : Nat) (inRange : i < queries.length)
    (columns : List (Column V)) (nativePath committedPath : List H)
    (captured : captures[i]'(by
      obtain ⟨_, layers, _, _, rfl⟩ :=
        verifyRaw_decomposes leafHash parentHash height root queries witnesses
          captures accepted
      simpa [captureInCallerOrder] using inRange) = some nativePath)
    (committed : acceptedOpening leafHash parentHash root height
      queries[i].position
      (projectedRow height queries[i].position columns) committedPath)
    (noCollision : ¬collisionOnOpenings leafHash parentHash
      queries[i].position queries[i].row
      (projectedRow height queries[i].position columns)
      nativePath committedPath) :
    queries[i].row = projectedRow height queries[i].position columns := by
  obtain ⟨path, observed, native⟩ :=
    verifyRaw_each_opening leafHash parentHash height root queries witnesses
      captures accepted i inRange
  have samePath : path = nativePath := Option.some.inj (observed.symm.trans captured)
  subst path
  exact accepted_row_refines_projected_commitment leafHash parentHash root
    height queries[i].position columns queries[i].row committedPath nativePath
    committed native noCollision

private def toyLeaf (row : List Nat) : Nat := row.sum
private def toyParent (children : Nat × Nat) : Nat :=
  100 * children.1 + children.2
private def toyQueries : List (RawQuery Nat) :=
  [⟨1, [11]⟩, ⟨0, [10]⟩, ⟨1, [11]⟩]

example : verifyRaw toyLeaf toyParent 1 1011 toyQueries [] =
    some [some [10], some [11], some [10]] := by decide

example : verifyRaw toyLeaf toyParent 1 1011
    [⟨1, [11]⟩, ⟨1, [12]⟩] [10] = none := by decide

example : verifyRaw toyLeaf toyParent 1 1011
    [⟨3, [11]⟩] [10] = none := by decide

example : verifyRaw toyLeaf toyParent 1 1011
    [⟨1, [11]⟩] [] = none := by decide

end S31.Gadgets.PcsFri.MultiproofRawQueries
