import S31.Gadgets.PcsFri.MerkleOpening
import S31.Gadgets.PcsFri.RawDeepCustody

/-!
This module discharges the `oracleBoundSchedule` premise from concrete Merkle
opening obligations, for an arbitrary FRI layer schedule. A packed FRI leaf
contains `2^leafLog` adjacent extension-field evaluations. `nativeRow` is the
row reconstructed by the verifier and `oracleLeaf` is the same row in a fixed
putative committed oracle. One unequal row at the same root and leaf index
would give the explicit leaf/parent collision from `MerkleOpening`.

The obligations are deliberately local and separate: Zig success must imply
the modeled accepted native paths and row-slot placement; a committed tree
must have the `oracleLeaf` rows; and the two compared openings must have no
hash collision. Source guards and native tests are evidence for the first
obligation, not a Lean proof of Zig execution or BLAKE2s collision resistance.
-/

namespace S31.Gadgets.PcsFri.FriMerkleBinding

open S31.Gadgets.PcsFri.MerkleOpening
open S31.Gadgets.PcsFri.LayerAcceptance
open S31.Gadgets.PcsFri.OperationalExtraction
open S31.Gadgets.PcsFri.QueryAndTranscript

variable {F H : Type*}

/-- One leaf index in a tree of packed consecutive FRI evaluations. -/
def leafPosition (leafLog absolutePosition : Nat) : Nat :=
  absolutePosition / 2 ^ leafLog

/-- The evaluation's offset inside its packed leaf. -/
def leafOffset (leafLog absolutePosition : Nat) : Nat :=
  absolutePosition % 2 ^ leafLog

/-- The canonical packed row of a fixed putative FRI oracle. -/
def oracleLeaf (layer : Layer F) (leafLog position : Nat) : List F :=
  (List.range (2 ^ leafLog)).map fun offset =>
    layer.oracle (position * 2 ^ leafLog + offset)

/-- Merkle evidence for all FRI positions, indexed by the actual packed-leaf
position rather than by raw query slot. Sharing a leaf across queries is safe. -/
structure LayerOpening (F H : Type*) where
  root : H
  height : Nat
  leafLog : Nat
  nativeRow : Nat → List F
  nativePath : Nat → List H
  committedPath : Nat → List H

/-- The native and fixed-oracle openings and their one accessed row slot.
Acceptance includes the exact root, height and leaf position. No equality of
the two rows, or of `opened` and `oracle`, is assumed. -/
def authenticatedSlot (leafHash : List F → H) (parentHash : H × H → H)
    (layer : Layer F) (opening : LayerOpening F H) (p r : Nat) : Prop :=
  let absolute := p * width layer + r
  let position := leafPosition opening.leafLog absolute
  let offset := leafOffset opening.leafLog absolute
  acceptedOpening leafHash parentHash opening.root opening.height position
    (opening.nativeRow position) (opening.nativePath position) ∧
  acceptedOpening leafHash parentHash opening.root opening.height position
    (oracleLeaf layer opening.leafLog position) (opening.committedPath position) ∧
  getElem? (opening.nativeRow position) offset = some (layer.opened p r) ∧
  ¬collisionOnOpenings leafHash parentHash position
    (opening.nativeRow position) (oracleLeaf layer opening.leafLog position)
    (opening.nativePath position) (opening.committedPath position)

private theorem oracleLeaf_slot (layer : Layer F) (leafLog absolute : Nat) :
    getElem? (oracleLeaf layer leafLog (leafPosition leafLog absolute))
      (leafOffset leafLog absolute) = some (layer.oracle absolute) := by
  have positive : 0 < 2 ^ leafLog := by positivity
  have offsetLt : leafOffset leafLog absolute < 2 ^ leafLog := by
    exact Nat.mod_lt _ positive
  have split : leafPosition leafLog absolute * 2 ^ leafLog +
      leafOffset leafLog absolute = absolute := by
    simpa [leafPosition, leafOffset, Nat.add_comm, Nat.mul_comm] using
      (Nat.mod_add_div absolute (2 ^ leafLog))
  simp [oracleLeaf, offsetLt, split]

/-- Collision freedom identifies the opened FRI value with the fixed oracle's
value at the same absolute evaluation index, including packed-leaf offsets. -/
theorem authenticatedSlot_eq_oracle
    (leafHash : List F → H) (parentHash : H × H → H)
    (layer : Layer F) (opening : LayerOpening F H) (p r : Nat)
    (hslot : authenticatedSlot leafHash parentHash layer opening p r) :
    layer.opened p r = layer.oracle (p * width layer + r) := by
  dsimp [authenticatedSlot] at hslot
  rcases hslot with ⟨native, committed, nativeValue, noCollision⟩
  have sameRows : opening.nativeRow
      (leafPosition opening.leafLog (p * width layer + r)) =
      oracleLeaf layer opening.leafLog
        (leafPosition opening.leafLog (p * width layer + r)) := by
    by_contra different
    exact noCollision (conflicting_openings_produce_collision leafHash parentHash
      opening.root opening.height
      (leafPosition opening.leafLog (p * width layer + r))
      (opening.nativeRow (leafPosition opening.leafLog (p * width layer + r)))
      (oracleLeaf layer opening.leafLog
        (leafPosition opening.leafLog (p * width layer + r)))
      (opening.nativePath (leafPosition opening.leafLog (p * width layer + r)))
      (opening.committedPath (leafPosition opening.leafLog (p * width layer + r)))
      native committed different)
  have committedValue := oracleLeaf_slot layer opening.leafLog
    (p * width layer + r)
  rw [sameRows] at nativeValue
  exact Option.some.inj (nativeValue.symm.trans committedValue)

/-- An opening with an inconsistent accessed value cannot satisfy the
authentication certificate unless one of its explicit collision premises is
removed. This rejects a bad slot for any layer width or packing size. -/
theorem inconsistentSlot_rejected
    (leafHash : List F → H) (parentHash : H × H → H)
    (layer : Layer F) (opening : LayerOpening F H) (p r : Nat)
    (hbad : layer.opened p r ≠ layer.oracle (p * width layer + r)) :
    ¬authenticatedSlot leafHash parentHash layer opening p r := by
  intro hslot
  exact hbad (authenticatedSlot_eq_oracle leafHash parentHash layer opening
    p r hslot)

/-- Local authenticated slots suffice for the existing layer oracle premise. -/
def authenticatedLayer (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) (layer : Layer F) (opening : LayerOpening F H) : Prop :=
  ∀ q ∈ raw, ∀ r < width layer,
    authenticatedSlot leafHash parentHash layer opening
      (foldPosition layer.step q) r

theorem authenticatedLayer_oracleBound
    (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) (layer : Layer F) (opening : LayerOpening F H)
    (hauth : authenticatedLayer leafHash parentHash raw layer opening) :
    oracleBoundLayer raw layer := by
  intro q hq r hr
  exact authenticatedSlot_eq_oracle leafHash parentHash layer opening
    (foldPosition layer.step q) r (hauth q hq r hr)

/-- Per-layer Merkle certificates follow the same arbitrary query-fold
schedule as operational FRI admission. A missing certificate fails closed. -/
def authenticatedSchedule (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) : List (Layer F) → List (LayerOpening F H) → Prop
  | [], [] => True
  | layer :: rest, opening :: openings =>
      authenticatedLayer leafHash parentHash raw layer opening ∧
        authenticatedSchedule leafHash parentHash
          (raw.map (foldPosition layer.step)) rest openings
  | _, _ => False

theorem authenticatedSchedule_oracleBound
    (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) (layers : List (Layer F))
    (openings : List (LayerOpening F H))
    (hauth : authenticatedSchedule leafHash parentHash raw layers openings) :
    oracleBoundSchedule raw layers := by
  induction layers generalizing raw openings with
  | nil => simp [oracleBoundSchedule]
  | cons layer rest ih =>
      cases openings with
      | nil => simp [authenticatedSchedule] at hauth
      | cons opening openings =>
          exact ⟨authenticatedLayer_oracleBound leafHash parentHash raw layer opening
            hauth.1, ih _ _ hauth.2⟩

/-- A certificate list must contain exactly one opening record per FRI layer;
the recursive relation cannot silently drop a final partial-fold layer. -/
theorem authenticatedSchedule_length
    (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) (layers : List (Layer F))
    (openings : List (LayerOpening F H))
    (hauth : authenticatedSchedule leafHash parentHash raw layers openings) :
    openings.length = layers.length := by
  induction layers generalizing raw openings with
  | nil =>
      cases openings with
      | nil => rfl
      | cons opening rest => simp [authenticatedSchedule] at hauth
  | cons layer rest ih =>
      cases openings with
      | nil => simp [authenticatedSchedule] at hauth
      | cons opening more =>
          simp [ih _ _ hauth.2]

/-- End-to-end **conditional** join: raw DEEP custody, operational FRI replay,
and authenticated Merkle openings yield the modeled query-path relation. This
does not derive any of its native or cryptographic premises from Zig success. -/
theorem authenticated_raw_deep_implies_accepts
    (leafHash : List F → H) (parentHash : H × H → H)
    (raw : List Nat) (answers : List F) (captured quotient : Nat → F)
    (layers : List (Layer F)) (openings : List (LayerOpening F H))
    (terminal : Terminal F)
    (hcaptured : RawDeepCustody.rawAnswers raw answers captured)
    (hquotient : RawDeepCustody.rawAnswers raw answers quotient)
    (hoperational : operationalAccepts raw captured layers terminal)
    (hauth : authenticatedSchedule leafHash parentHash raw layers openings) :
    accepts (normalized raw) quotient layers terminal := by
  exact RawDeepCustody.raw_deep_and_operational_implies_accepts
    raw answers captured quotient layers terminal hcaptured hquotient
    hoperational (authenticatedSchedule_oracleBound leafHash parentHash
      raw layers openings hauth)

end S31.Gadgets.PcsFri.FriMerkleBinding
