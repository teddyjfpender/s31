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

def below35 (gate : TextSquare4Native.Gate) : Prop :=
  gate.input0 < 35 ∧ gate.input1 < 35 ∧ gate.output < 35

theorem hasGate_on_wire_below (rows : List Row)
    (externalUses externalYields : List Event)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProducedBelow (allYields rows externalYields) 35)
    (gate : TextSquare4Native.Gate) (op : S31.Gadgets.Air.Qm31Ops.Op)
    (hbound : below35 gate) (hgate : hasGate rows gate op) :
    accepts (encode op)
      (producedWire (allYields rows externalYields) gate.input0)
      (producedWire (allYields rows externalYields) gate.input1)
      (producedWire (allYields rows externalYields) gate.output) := by
  obtain ⟨row, hrow, h0, h1, hout, hflags, hm, hair⟩ := hgate
  have hr0 : row.in0Address < 35 := by rw [h0]; exact hbound.1
  have hr1 : row.in1Address < 35 := by rw [h1]; exact hbound.2.1
  have hrout : row.outAddress < 35 := by rw [hout]; exact hbound.2.2
  have h := row_accepts_on_wire_below rows externalUses externalYields 35
    hbalance hunique row hrow hm hr0 hr1 hrout hair
  simpa only [h0, h1, hout, hflags] using h

theorem inputCopy_below (i : Fin 4) : below35 (inputCopy i.val) := by
  fin_cases i <;> (unfold below35; decide)
theorem packMul_below (i : Fin 3) : below35 (packMul i.val) := by
  fin_cases i <;> (unfold below35; decide)
theorem packAdd_below (i : Fin 3) : below35 (packAdd i.val) := by
  fin_cases i <;> (unfold below35; decide)
theorem outputPoint_below (i : Fin 4) : below35 (outputPoint i.val) := by
  fin_cases i <;> (unfold below35; decide)
theorem outputInverse_below (i : Fin 4) :
    below35 (outputInverse (i.val - 1)) := by
  fin_cases i <;> (unfold below35; decide)
theorem outputCopy_below (i : Fin 4) : below35 (outputCopy i.val) := by
  fin_cases i <;> (unfold below35; decide)

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

/-- The native exporter checks every declared wire has exactly one producer
and that this concrete circuit has no permutation scratch rows. Lean checks
the reported geometry and the selected path's declared-address bound. -/
theorem native_compiler_declared_facts :
    35 ≤ TextSquare4Native.declaredVarCount ∧
    TextSquare4Native.declaredVarCount < 2147483647 ∧
    TextSquare4Native.arithmeticRowCount =
      TextSquare4Native.declaredVarCount ∧
    TextSquare4Native.permutationTermCount = 0 := by
  decide

set_option maxRecDepth 4096 in
/-- The exporter verifies that the native compiler's actual producer outputs
are precisely the addresses in this generated range. Lean evaluates the
modeled producer scan on that range. -/
theorem native_producer_scan_exists :
    ∃ result,
      S31.Gadgets.Air.GateProducerCheck.scan
        TextSquare4Native.declaredVarCount ∅
        TextSquare4Native.declaredProducerAddresses = some result := by
  have h : (S31.Gadgets.Air.GateProducerCheck.scan
      TextSquare4Native.declaredVarCount ∅
      TextSquare4Native.declaredProducerAddresses).isSome = true := by
    decide
  cases hscan : S31.Gadgets.Air.GateProducerCheck.scan
      TextSquare4Native.declaredVarCount ∅
      TextSquare4Native.declaredProducerAddresses with
  | none => simp [hscan] at h
  | some result => exact ⟨result, rfl⟩

def declaredEvents (wire : Nat → Quad) : List Event :=
  TextSquare4Native.declaredProducerAddresses.map
    (fun address => (address, wire address))

set_option maxRecDepth 4096 in
theorem declared_events_scan_exists (wire : Nat → Quad) :
    ∃ result,
      S31.Gadgets.Air.GateProducerCheck.scan
        TextSquare4Native.declaredVarCount ∅
        ((declaredEvents wire).map Prod.fst) = some result := by
  simpa [declaredEvents, List.map_map] using native_producer_scan_exists

/-- Only addresses below 35 need unique produced values. The exported path
uses addresses 0–34, so permutation scratch producers at higher addresses may
share an address without weakening this circuit statement. -/
theorem native_public_claim_of_gate_balance_below
    (rows : List Row) (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProducedBelow (allYields rows externalYields) 35)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  let produced := allYields rows externalYields
  let wire := producedWire produced
  have hgate (gate : TextSquare4Native.Gate)
      (op : S31.Gadgets.Air.Qm31Ops.Op)
      (hbound : below35 gate)
      (h : hasGate rows gate op) :
      accepts (encode op) (wire gate.input0) (wire gate.input1)
        (wire gate.output) :=
    hasGate_on_wire_below rows externalUses externalYields
      hbalance hunique gate op hbound h
  have hpin (address : Nat) (value : Quad)
      (hbound : address < 35)
      (h : (address, value) ∈ produced) : wire address = value :=
    producedWire_eq_below produced 35 hunique address hbound value h
  rcases hpins with ⟨hzero, hinput, hb1, hb2, hb3, hunit, hinverse, houtput⟩
  rcases hpath with ⟨hcopyIn, hpackMul, hpackAdd, hfirst, hsecond,
    hpoint, hmulOut, hcopyOut⟩
  have hinput' : inputBoundary wire input :=
    ⟨hpin _ _ (by decide) hzero,
      fun i => ⟨hgate _ .add (inputCopy_below i) (hcopyIn i),
        hpin _ _ (by fin_cases i <;> decide) (hinput i)⟩⟩
  have harithmetic : arithmeticGateRows wire :=
    ⟨hpin _ _ (by decide) hb1,
      hpin _ _ (by decide) hb2,
      hpin _ _ (by decide) hb3,
      (fun i => hgate _ .mul (packMul_below i) (hpackMul i)),
      (fun i => hgate _ .add (packAdd_below i) (hpackAdd i)),
      hgate _ (s31Op true) (by unfold below35; decide) hfirst,
      hgate _ (s31Op true) (by unfold below35; decide) hsecond⟩
  have houtput' : nativeOutputRows wire claimed :=
    ⟨(fun i => ⟨hpin _ _ (by fin_cases i <;> decide) (hunit i),
        hgate _ .pointwiseMul (outputPoint_below i) (hpoint i)⟩),
      (fun i => by
        by_cases hi : i.val = 0
        · simp [hi]
        · simp only [hi, ↓reduceIte]
          have hm := hmulOut i
          simp only [hi, ↓reduceIte] at hm
          have hu := hinverse i
          simp only [hi, ↓reduceIte] at hu
          exact ⟨hpin _ _ (by fin_cases i <;> decide) hu,
            hgate _ .mul (outputInverse_below i) hm⟩),
      (fun i => ⟨hgate _ .add (outputCopy_below i) (hcopyOut i),
        hpin _ _ (by fin_cases i <;> decide) (houtput i)⟩)⟩
  exact native_public_claim_sound wire input claimed
    hinput' harithmetic houtput'

/-- The simpler full-uniqueness statement follows from the declared-address
version; it remains useful for circuits without scratch producers. -/
theorem native_public_claim_of_gate_balance
    (rows : List Row) (externalUses externalYields : List Event)
    (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hunique : uniqueProduced (allYields rows externalYields))
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input :=
  native_public_claim_of_gate_balance_below rows externalUses externalYields
    input claimed hbalance
    (uniqueProducedBelow_of_unique _ 35 hunique) hpath hpins

/-- A successful declared-producer scan suffices for this circuit path even
if scratch addresses elsewhere have repeated producers. Coverage identifies
every produced event below the declared-variable bound with a checked
declared event; multiplicity may repeat an identical event in the Gate list. -/
theorem native_public_claim_of_checked_declared
    (rows : List Row) (externalUses externalYields declared : List Event)
    (bound : Nat) (result : Finset Nat)
    (input claimed : Fin 4 → M31)
    (hbound : 35 ≤ bound)
    (hbalance : balanced rows externalUses externalYields)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan bound ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value, address < 35 →
      (address, value) ∈ allYields rows externalYields →
      (address, value) ∈ declared)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  have hlow35 := uniqueProducedBelow_of_checked_declared_prefix
    bound 35 hbound declared (allYields rows externalYields) result
    hscan hcovered
  exact native_public_claim_of_gate_balance_below rows
    externalUses externalYields input claimed hbalance hlow35 hpath hpins

/-- Instantiate the declared-address theorem with the count exported by the
production compiler, rather than a caller-supplied bound. -/
theorem native_public_claim_of_exported_bound
    (rows : List Row) (externalUses externalYields declared : List Event)
    (result : Finset Nat) (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hscan : S31.Gadgets.Air.GateProducerCheck.scan
      TextSquare4Native.declaredVarCount ∅
      (declared.map Prod.fst) = some result)
    (hcovered : ∀ address value,
      address < 35 →
      (address, value) ∈ allYields rows externalYields →
      (address, value) ∈ declared)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input :=
  native_public_claim_of_checked_declared rows
    externalUses externalYields declared
    TextSquare4Native.declaredVarCount result input claimed
    native_compiler_declared_facts.1 hbalance hscan hcovered hpath hpins

/-- The modeled scan premise is discharged by the source-exported complete
producer-address roster. The remaining coverage premise is exactly where
native trace events must be identified with this declared producer map. -/
theorem native_public_claim_of_exported_producers
    (rows : List Row) (externalUses externalYields : List Event)
    (wire : Nat → Quad) (input claimed : Fin 4 → M31)
    (hbalance : balanced rows externalUses externalYields)
    (hcovered : ∀ address value,
      address < 35 →
      (address, value) ∈ allYields rows externalYields →
      (address, value) ∈ declaredEvents wire)
    (hpath : nativePathRows rows)
    (hpins : pinnedEvents (allYields rows externalYields) input claimed) :
    claimed = TextSquare4Air.fourth input := by
  obtain ⟨result, hscan⟩ := declared_events_scan_exists wire
  exact native_public_claim_of_exported_bound rows externalUses
    externalYields (declaredEvents wire) result input claimed
    hbalance hscan hcovered hpath hpins

end S31.Functional.TextSquare4GateJoin
