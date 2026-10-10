import S31.Gadgets.Functional.TextSquare4NativeBoundary
import S31.Gadgets.Air.GateWireMap

/-!
Conditional composition of the source-generated fourth-power circuit path
with an exact Gate address join. This removes the shared-wire-map premise of
`TextSquare4NativeBoundary`: it is constructed from balanced Gate events and
unique producers. Establishing that a native STARK proof supplies the stated
events, rows, pins, and nonexceptional challenge remains a separate obligation.
-/

namespace S31.Functional.TextSquare4GateJoin

open S31
open S31.Gadgets.Packed
open S31.Gadgets.Air.Qm31Ops
open S31.Gadgets.Air.GateLookup
open S31.Gadgets.Air.GateWireMap
open S31.Functional.TextSquare4NativeBoundary
open S31.Functional.TextSquare4NativeProof

def hasGate (rows : List Row) (gate : TextSquare4Native.Gate)
    (op : S31.Gadgets.Air.Qm31Ops.Op) : Prop :=
  ∃ row ∈ rows,
    row.in0Address = gate.input0 ∧
    row.in1Address = gate.input1 ∧
    row.outAddress = gate.output ∧
    row.flags = encode op ∧
    0 < row.multiplicity ∧
    accepts row.flags row.in0 row.in1 row.output

theorem hasGate_on_wire (rows : List Row) (externalUses externalYields : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (gate : TextSquare4Native.Gate) (op : S31.Gadgets.Air.Qm31Ops.Op)
    (hgate : hasGate rows gate op) :
    accepts (encode op)
      (producedWire (allYields rows externalYields) gate.input0)
      (producedWire (allYields rows externalYields) gate.input1)
      (producedWire (allYields rows externalYields) gate.output) := by
  obtain ⟨row, hrow, h0, h1, hout, hflags, hm, hair⟩ := hgate
  have h := row_accepts_on_wire rows externalUses externalYields
    hbalance hunique row hrow hm hair
  simpa only [h0, h1, hout, hflags] using h

/-- The 23 arithmetic gates on the source-generated input-to-output path.
Other native range and representation rows may also occur in `rows`. -/
def nativePathRows (rows : List Row) : Prop :=
  (∀ i : Fin 4, hasGate rows (inputCopy i.val) .add) ∧
  (∀ i : Fin 3, hasGate rows (packMul i.val) .mul) ∧
  (∀ i : Fin 3, hasGate rows (packAdd i.val) .add) ∧
  hasGate rows TextSquare4Native.first (s31Op true) ∧
  hasGate rows TextSquare4Native.second (s31Op true) ∧
  (∀ i : Fin 4, hasGate rows (outputPoint i.val) .pointwiseMul) ∧
  (∀ i : Fin 4, if i.val = 0 then True else
    hasGate rows (outputInverse (i.val - 1)) .mul) ∧
  (∀ i : Fin 4, hasGate rows (outputCopy i.val) .add)

/-- Constants and public words are supplied as produced Gate events. Their
values are forced by uniqueness, rather than assigned to an assumed map. -/
def pinnedEvents (produced : List Event) (input claimed : Fin 4 → M31) : Prop :=
  (TextSquare4Native.zeroWire, base 0) ∈ produced ∧
  (∀ i : Fin 4, (publicInputWire i.val,
      base (Field.toZMod (input i))) ∈ produced) ∧
  (basisWire 0, unit ⟨1, by decide⟩) ∈ produced ∧
  (basisWire 1, unit ⟨2, by decide⟩) ∈ produced ∧
  (basisWire 2, unit ⟨3, by decide⟩) ∈ produced ∧
  (∀ i : Fin 4,
    ((outputPoint i.val).input1, unit i) ∈ produced) ∧
  (∀ i : Fin 4, if i.val = 0 then True else
    ((outputInverse (i.val - 1)).input1, unitInverse i) ∈ produced) ∧
  (∀ i : Fin 4, (publicOutputWire i.val,
      base (Field.toZMod (claimed i))) ∈ produced)

/-- Exact Gate balance, unique producers, local AIR acceptance of each
source-generated path gate, and pinned public/constant events force the full
public fourth-power statement. -/
theorem native_public_claim_of_gate_balance
    (rows : List Row) (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  let produced := allYields rows externalYields
  let wire := producedWire produced
  have hgate (gate : TextSquare4Native.Gate)
      (op : S31.Gadgets.Air.Qm31Ops.Op)
      (h : hasGate rows gate op) :
      accepts (encode op) (wire gate.input0) (wire gate.input1)
        (wire gate.output) :=
    hasGate_on_wire rows externalUses externalYields hbalance hunique gate op h
  have hpin (address : Nat) (value : Quad)
      (h : (address, value) ∈ produced) : wire address = value :=
    producedWire_eq produced hunique address value h
  rcases hpins with ⟨hzero, hinput, hb1, hb2, hb3, hunit, hinverse, houtput⟩
  rcases hpath with ⟨hcopyIn, hpackMul, hpackAdd, hfirst, hsecond,
    hpoint, hmulOut, hcopyOut⟩
  have hinput' : inputBoundary wire input :=
    ⟨hpin _ _ hzero, fun i => ⟨hgate _ .add (hcopyIn i),
      hpin _ _ (hinput i)⟩⟩
  have harithmetic : arithmeticGateRows wire :=
    ⟨hpin _ _ hb1, hpin _ _ hb2, hpin _ _ hb3,
      (fun i => hgate _ .mul (hpackMul i)),
      (fun i => hgate _ .add (hpackAdd i)),
      hgate _ (s31Op true) hfirst,
      hgate _ (s31Op true) hsecond⟩
  have houtput' : nativeOutputRows wire claimed :=
    ⟨(fun i => ⟨hpin _ _ (hunit i), hgate _ .pointwiseMul (hpoint i)⟩),
      (fun i => by
        by_cases hi : i.val = 0
        · simp [hi]
        · simp only [hi, ↓reduceIte]
          have hm := hmulOut i
          simp only [hi, ↓reduceIte] at hm
          have hu := hinverse i
          simp only [hi, ↓reduceIte] at hu
          exact ⟨hpin _ _ hu, hgate _ .mul hm⟩),
      (fun i => ⟨hgate _ .add (hcopyOut i), hpin _ _ (houtput i)⟩)⟩
  exact native_public_claim_sound wire input claimed
    hinput' harithmetic houtput'

end S31.Functional.TextSquare4GateJoin
